[@@@ocaml.warning "+a-4-30-40-41-42"]

include Cfg_intf.S

module Location = struct
  module Stack = struct
    type t =
      | Local of
          { index : int;
            reg_class : int
          }
      | Incoming of int
      | Outgoing of int
      | Domainstate of int

    let word_size = 8

    let byte_offset_to_word_index offset =
      (* CR azewierzejew: This seems good enough but maybe we would want to
         consider unaligned offsets or 32-bit architecture. *)
      if Sys.word_size <> word_size
      then
        Cfg_regalloc_utils.fatal
          "regalloc validation only supports 64 bit architecture, got word \
           size %d"
          Sys.word_size;
      if offset mod word_size <> 0
      then
        Cfg_regalloc_utils.fatal
          "regalloc validation aligned offsets, got offset %d with remainder %d"
          offset (offset mod word_size);
      offset / word_size

    let word_index_to_byte_offset index =
      (* CR azewierzejew: This seems good enough but maybe we would want to
         consider unaligned offsets or 32-bit architecture. *)
      if Sys.word_size <> word_size
      then
        Cfg_regalloc_utils.fatal
          "regalloc validation only supports 64 bit architecture, got word \
           size %d"
          Sys.word_size;
      index * word_size

    let of_stack_loc ~reg_class loc =
      match loc with
      | Reg.Local index -> Local { index; reg_class }
      | Reg.Incoming offset -> Incoming (byte_offset_to_word_index offset)
      | Reg.Outgoing offset -> Outgoing (byte_offset_to_word_index offset)
      | Reg.Domainstate offset -> Domainstate (byte_offset_to_word_index offset)

    let to_stack_loc_lossy t =
      match t with
      | Local { index; _ } -> Reg.Local index
      | Incoming index -> Reg.Incoming (word_index_to_byte_offset index)
      | Outgoing index -> Reg.Outgoing (word_index_to_byte_offset index)
      | Domainstate index -> Reg.Domainstate (word_index_to_byte_offset index)

    let reg_class_lossy t =
      match t with
      | Local { reg_class; _ } -> reg_class
      | Incoming _ | Outgoing _ | Domainstate _ -> -1
  end

  type t =
    | Reg of int
    | Stack of Stack.t

  let of_reg reg =
    match reg.Reg.loc with
    | Reg.Unknown -> None
    | Reg.Reg idx -> Some (Reg idx)
    | Reg.Stack stack ->
      Some
        (Stack (Stack.of_stack_loc ~reg_class:(Proc.register_class reg) stack))

  let of_reg_exn reg = of_reg reg |> Option.get

  let to_loc_lossy t =
    match t with
    | Reg idx -> Reg.Reg idx
    | Stack stack -> Reg.Stack (Stack.to_stack_loc_lossy stack)

  let reg_class_lossy t =
    match t with Reg _ -> -1 | Stack stack -> Stack.reg_class_lossy stack

  let print ppf t =
    Printmach.loc ~reg_class:(reg_class_lossy t)
      ~unknown:(fun _ -> failwith "unreachable")
      ppf (to_loc_lossy t)

  let compare (t1 : t) (t2 : t) : int = compare t1 t2

  let equal (t1 : t) (t2 : t) : bool = compare t1 t2 = 0
end

module Register = struct
  type t =
    { raw_name : Reg.Raw_name.t;
      stamp : int;
      loc : Location.t option;
      typ : Cmm.machtype_component
    }

  let create reg =
    { stamp = reg.Reg.stamp;
      loc = Location.of_reg reg;
      raw_name = reg.Reg.raw_name;
      typ = reg.Reg.typ
    }

  let to_dummy_reg t =
    { Reg.dummy with
      raw_name = t.raw_name;
      typ = t.typ;
      stamp = t.stamp;
      loc =
        Option.map Location.to_loc_lossy t.loc
        |> Option.value ~default:Reg.Unknown
    }

  let print ppf t = Printmach.reg ppf (to_dummy_reg t)

  let compare (t1 : t) (t2 : t) : int =
    let stamp_cmp = Int.compare t1.stamp t2.stamp in
    let t_eq = t1 = t2 in
    assert (t_eq = (stamp_cmp = 0));
    stamp_cmp

  let equal (t1 : t) (t2 : t) : bool = compare t1 t2 = 0
end

module Instruction = struct
  type 'a t =
    { desc : 'a;
      arg : Register.t array;
      res : Register.t array
    }

  let to_prealloc (type a) ~(alloced : a instruction) (t : a t) : a instruction
      =
    { alloced with
      arg = Array.map Register.to_dummy_reg t.arg;
      res = Array.map Register.to_dummy_reg t.res
    }
end

module Description = struct
  type t =
    { instructions : (int, basic Instruction.t) Hashtbl.t;
      terminators : (int, terminator Instruction.t) Hashtbl.t
    }

  let make_instruction_helper t f instr =
    f
      (match instr.desc with Op (Spill | Reload) -> true | _ -> false)
      t.instructions instr

  let make_terminator_helper t f instr = f false t.terminators instr

  let create cfg =
    if Cfg_regalloc_utils.regalloc_debug
    then
      Cfg_with_layout.save_as_dot ~filename:"before.dot" cfg
        "before_allocation_before_validation";
    let add_instr is_reg_alloc_specific instructions instr =
      let id = instr.id in
      if is_reg_alloc_specific
      then
        Cfg_regalloc_utils.fatal
          "Instruction %d is specific to the regalloc phase while creating \
           pre-allocation description"
          id;
      if Hashtbl.find_opt instructions id |> Option.is_some
      then
        Cfg_regalloc_utils.fatal
          "Duplicate instr id %d while creating pre-allocation description" id;
      Hashtbl.add instructions id
        { Instruction.desc = instr.desc;
          arg = Array.map Register.create instr.arg;
          res = Array.map Register.create instr.res
        }
    in
    let t =
      { instructions = Hashtbl.create 0; terminators = Hashtbl.create 0 }
    in
    Cfg_with_layout.iter_instructions cfg
      ~instruction:(make_instruction_helper t add_instr)
      ~terminator:(make_terminator_helper t add_instr);
    t

  let verify_reg_array ~id ~name ~reg_arr ~loc_arr =
    if Array.length reg_arr <> Array.length loc_arr
    then
      Cfg_regalloc_utils.fatal
        "The instruction's no. %d %s count has changed. Now: %d. After: %d." id
        name (Array.length loc_arr) (Array.length reg_arr);
    Array.iter2
      (fun reg_desc loc_reg ->
        match reg_desc.Register.loc, loc_reg.Reg.loc with
        | _, Reg.Unknown ->
          Cfg_regalloc_utils.fatal
            "The instruction's no. %d %s is still unknown after allocation" id
            name
        | None, _ -> ()
        | Some (Location.Reg _), Reg.Reg _ -> ()
        | Some (Location.Stack _), Reg.Stack _ -> ()
        | Some prev_loc, new_loc ->
          Cfg_regalloc_utils.fatal
            "The instruction's no. %d %s has changed precolored location from \
             %a to %a"
            id name Location.print prev_loc
            (Printmach.loc ?wrap_out:None
               ~reg_class:(Proc.register_class loc_reg) ~unknown:(fun ppf ->
                 Format.fprintf ppf "Unknown"))
            new_loc)
      reg_arr loc_arr;
    ()

  let verify t cfg =
    let seen_ids = Hashtbl.create 0 in
    let check_instr is_regalloc_specific instructions instr =
      let id = instr.id in
      if Hashtbl.find_opt seen_ids id |> Option.is_some
      then
        Cfg_regalloc_utils.fatal
          "Duplicate instruction no. %d while checking post-allocation \
           description"
          id;
      Hashtbl.add seen_ids id ();
      match Hashtbl.find_opt instructions id, is_regalloc_specific with
      (* The instruction was present before. *)
      | Some old_instr, false ->
        if instr.desc <> old_instr.Instruction.desc
        then
          Cfg_regalloc_utils.fatal "The instruction's no. %d desc was changed"
            id;
        verify_reg_array ~id ~name:"argument" ~reg_arr:old_instr.Instruction.arg
          ~loc_arr:instr.arg;
        verify_reg_array ~id ~name:"result" ~reg_arr:old_instr.Instruction.res
          ~loc_arr:instr.res;
        ()
      (* Added spill/reload that wasn't before. *)
      | None, true -> ()
      | Some _, true ->
        Cfg_regalloc_utils.fatal
          "Register allocation changed existing instruction no. %d into a \
           register allocation specific instruction"
          id
      | None, false ->
        Cfg_regalloc_utils.fatal
          "Register allocation added non-regalloc specific instruction no. %d"
          id
    in
    Cfg_with_layout.iter_instructions cfg
      ~instruction:(make_instruction_helper t check_instr)
      ~terminator:(make_terminator_helper t check_instr);
    Hashtbl.iter
      (fun id instr ->
        let can_be_removed =
          match instr.Instruction.desc with Prologue -> true | _ -> false
        in
        if Hashtbl.find_opt seen_ids id |> Option.is_none && not can_be_removed
        then
          Cfg_regalloc_utils.fatal
            "Instruction no. %d was deleted by register allocator" id)
      t.instructions;
    Hashtbl.iter
      (fun id _ ->
        if Hashtbl.find_opt seen_ids id |> Option.is_none
        then
          Cfg_regalloc_utils.fatal
            "Terminator no. %d was deleted by register allocator" id)
      t.terminators;
    ()
end

module Equation_set : sig
  type t

  val empty : t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val union : t -> t -> t

  val remove_result :
    reg_res:Register.t array ->
    loc_res:Location.t array ->
    t ->
    (t, string) Result.t

  val verify_destroyed_locations :
    destroyed:Location.t array -> t -> (unit, string) Result.t

  val add_argument :
    reg_arg:Register.t array -> loc_arg:Location.t array -> t -> t

  val rename_loc : arg:Location.t -> res:Location.t -> t -> t

  val rename_reg : arg:Register.t -> res:Register.t -> t -> t

  val print : Format.formatter -> t -> unit
end = struct
  module Equation = struct
    type t = Register.t * Location.t

    let compare (r1, l1) (r2, l2) =
      let r_cmp = Register.compare r1 r2 in
      if r_cmp <> 0 then r_cmp else Location.compare l1 l2
  end

  include Set.Make (Equation)

  let compatibile_one ~reg ~loc t =
    for_all
      (fun (eq_reg, eq_loc) ->
        let reg_eq = Register.equal eq_reg reg in
        let loc_eq = Location.equal eq_loc loc in
        reg_eq = loc_eq)
      t

  let remove_result ~reg_res ~loc_res t =
    let compatibile =
      Array.for_all2
        (fun reg loc -> compatibile_one ~reg ~loc t)
        reg_res loc_res
    in
    if compatibile
    then (
      let t = ref t in
      Array.iter2 (fun reg loc -> t := remove (reg, loc) !t) reg_res loc_res;
      Ok !t)
    else Error "Unsatisfiable equations when removing result equations"

  let verify_destroyed_locations ~destroyed t =
    (* CR azewierzejew for azewierzejew: Add checking stack for stack_location
       other than Local. *)
    let correct =
      Array.for_all
        (fun des_loc -> for_all (fun (_stamp, loc) -> des_loc <> loc) t)
        destroyed
    in
    if correct then Ok () else Error "Destroying a live location"

  let add_argument ~reg_arg ~loc_arg t =
    let t = ref t in
    Array.iter2 (fun reg loc -> t := add (reg, loc) !t) reg_arg loc_arg;
    !t

  let rename_loc ~arg ~res t =
    map (fun (stamp, loc) -> if loc = res then stamp, arg else stamp, loc) t

  let rename_reg ~arg ~res t =
    map
      (fun (eq_reg, loc) ->
        if Register.equal eq_reg res then arg, loc else eq_reg, loc)
      t

  let print ppf t =
    let first = ref true in
    iter
      (fun (stamp, loc) ->
        if !first then first := false else Format.fprintf ppf " ";
        Format.fprintf ppf "%a=[%a]" Register.print stamp Location.print loc)
      t
end

let extract_loc_arr loc_arr =
  Array.map (fun loc_reg -> Location.of_reg_exn loc_reg) loc_arr

module type Description_value = sig
  val description : Description.t
end

module Error = struct
  type 'a t =
    { equations : Equation_set.t;
      exn_equations : Equation_set.t option;
      reg_instr : 'a Instruction.t;
      loc_instr : 'a instruction;
      message : string
    }

  module Tag = struct
    type 'a t =
      | Terminator : terminator t
      | Basic : basic t
  end

  type packed =
    | Terminator : terminator t -> packed
    | Basic : basic t -> packed

  let compare (_ : packed) (_ : packed) = 0
end

module Domain = struct
  type t =
    { equations : Equation_set.t;
      error : Error.packed option
    }

  let bot = { equations = Equation_set.empty; error = None }

  let compare t1 t2 =
    let eq_cmp = Equation_set.compare t1.equations t2.equations in
    if eq_cmp <> 0
    then eq_cmp
    else Option.compare Error.compare t1.error t2.error

  let join t_old t_suc =
    match t_old, t_suc with
    | { error = Some _; _ }, _ -> t_old
    | { equations; error = None }, { error = Some error; _ } ->
      { equations; error = Some error }
    | { equations = eq_old; error = None }, { equations = eq_suc; error = None }
      ->
      { equations = Equation_set.union eq_old eq_suc; error = None }

  let less_equal t_new t_old =
    match t_new, t_old with
    | _, { error = Some _; _ } -> true
    | { error = Some _; _ }, { error = None; _ } -> false
    | ( { error = None; equations = eq_set_new },
        { error = None; equations = eq_set_old } ) ->
      Equation_set.equal eq_set_new eq_set_old

  let to_string _ = failwith "[to_string] unimplemented"

  let to_result t =
    match t.error with Some error -> Error error | None -> Ok t.equations

  let remove_exn_bucket equations =
    let phys_reg = Proc.loc_exn_bucket in
    let reg =
      { Register.stamp = phys_reg.stamp;
        loc = Location.of_reg phys_reg;
        raw_name = phys_reg.raw_name;
        typ = phys_reg.typ
      }
    in
    Equation_set.remove_result equations ~reg_res:[| reg |]
      ~loc_res:[| Option.get reg.Register.loc |]
    |> Result.map_error (fun message ->
           Printf.sprintf "While removing exn bucket: %s" message)

  let append_equations (type a) t ~(tag : a Error.Tag.t) ~exn
      ~(reg_instr : a Instruction.t) ~(loc_instr : a instruction) ~destroyed =
    let bind f res = Result.bind res f in
    let wrap_error res =
      Result.map_error
        (fun message ->
          let err =
            { Error.message;
              equations = t.equations;
              reg_instr;
              loc_instr;
              exn_equations = Option.map (fun t -> t.equations) exn
            }
          in
          match tag with
          | Error.Tag.Terminator -> Error.Terminator err
          | Error.Tag.Basic -> Error.Basic err)
        res
    in
    let exn =
      (* If instruction can't raise [Option.is_none exn] then use empty set of
         instructions as that's the same as skipping the step. *)
      Option.value exn ~default:bot
      |> to_result
      (* Handle this here because in [exception_] we don't have enough
         information in order to give a meaningful error message. *)
      |> bind (fun exn -> remove_exn_bucket exn |> wrap_error)
    in
    let res =
      to_result t
      |> bind (fun equations ->
             Equation_set.remove_result ~reg_res:reg_instr.Instruction.res
               ~loc_res:(extract_loc_arr loc_instr.res)
               equations
             |> wrap_error)
      |> bind (fun equations ->
             exn
             |> Result.map (fun exn_equations ->
                    Equation_set.union equations exn_equations))
      |> bind (fun equations ->
             Equation_set.verify_destroyed_locations ~destroyed equations
             |> Result.map (fun () -> equations)
             |> wrap_error)
      |> Result.map (fun equations ->
             Equation_set.add_argument ~reg_arg:reg_instr.Instruction.arg
               ~loc_arg:(extract_loc_arr loc_instr.arg)
               equations)
    in
    match res with
    | Ok equations -> { equations; error = None }
    | Error error -> { equations = t.equations; error = Some error }

  let rename_location t ~loc_instr =
    match t with
    | { error = Some _; _ } -> t
    | { error = None; equations } ->
      assert (Array.length loc_instr.arg = 1);
      assert (Array.length loc_instr.res = 1);
      { equations =
          Equation_set.rename_loc
            ~arg:(Location.of_reg_exn loc_instr.arg.(0))
            ~res:(Location.of_reg_exn loc_instr.res.(0))
            equations;
        error = None
      }

  let rename_register t ~reg_instr =
    match t with
    | { error = Some _; _ } -> t
    | { error = None; equations } ->
      let open! Instruction in
      assert (Array.length reg_instr.arg = 1);
      assert (Array.length reg_instr.res = 1);
      { equations =
          Equation_set.rename_reg ~arg:reg_instr.arg.(0) ~res:reg_instr.res.(0)
            equations;
        error = None
      }
end

module Transfer (Desc_val : Description_value) = struct
  type domain = Domain.t

  let basic t ~exn instr =
    match instr.desc with
    | Op (Spill | Reload) ->
      assert (not (Cfg.can_raise_basic instr.desc));
      Domain.rename_location t ~loc_instr:instr
    | Op Move
      when Array.length instr.arg = 1
           && Array.length instr.res = 1
           && instr.arg.(0).loc = instr.res.(0).loc ->
      assert (not (Cfg.can_raise_basic instr.desc));
      let instr_before =
        Hashtbl.find Desc_val.description.instructions instr.id
      in
      Domain.rename_register t ~reg_instr:instr_before
    | _ ->
      let exn = if Cfg.can_raise_basic instr.desc then Some exn else None in
      let instr_before =
        Hashtbl.find Desc_val.description.instructions instr.id
      in
      Domain.append_equations t ~tag:Error.Tag.Basic ~exn
        ~reg_instr:instr_before ~loc_instr:instr
        ~destroyed:
          (Cfg_regalloc_utils.destroyed_at_basic instr.desc |> extract_loc_arr)

  let terminator t ~exn instr =
    let exn = if Cfg.can_raise_terminator instr.desc then Some exn else None in
    let instr_before = Hashtbl.find Desc_val.description.terminators instr.id in
    Domain.append_equations t ~tag:Terminator ~exn ~reg_instr:instr_before
      ~loc_instr:instr
      ~destroyed:
        (Cfg_regalloc_utils.destroyed_at_terminator instr.desc
        |> extract_loc_arr)

  let exception_ t = t
end

module Check_backwards (Desc_val : Description_value) =
  Cfg_dataflow.Backward (Domain) (Transfer (Desc_val))

let print_reg_as_loc ppf reg =
  Printmach.loc ~reg_class:(Proc.register_class reg)
    ~unknown:(fun ppf -> Format.fprintf ppf "<Unknown>")
    ppf reg.Reg.loc

let save_as_dot_with_equations ~desc ~res_instr ~res_block ?filename cfg msg =
  Cfg_with_layout.save_as_dot
    ~annotate_instr:
      [ (fun ppf instr ->
          let id =
            match instr with
            | `Basic instr -> instr.id
            | `Terminator instr -> instr.id
          in
          let res = Cfg_dataflow.Instr.Tbl.find res_instr id in
          (match res.Domain.error with
          | None -> ()
          | Some _ -> Format.fprintf ppf "ERROR ");
          Equation_set.print ppf res.Domain.equations;
          ());
        Cfg.print_instruction' ~print_reg:print_reg_as_loc;
        (fun ppf instr ->
          match instr with
          | `Basic instr -> (
            match Hashtbl.find_opt desc.Description.instructions instr.id with
            | Some prev_instr ->
              let instr = Instruction.to_prealloc ~alloced:instr prev_instr in
              Cfg.print_basic ppf instr
            | None -> ())
          | `Terminator ti ->
            let prev_ti = Hashtbl.find desc.Description.terminators ti.id in
            let ti = Instruction.to_prealloc ~alloced:ti prev_ti in
            Cfg.print_terminator ppf ti) ]
    ~annotate_block_end:(fun ppf block ->
      let res = Label.Tbl.find res_block block.start in
      (match res.Domain.error with
      | None -> ()
      | Some _ -> Format.fprintf ppf "ERROR ");
      Equation_set.print ppf res.Domain.equations;
      ())
    ?filename cfg msg;
  ()

let verify desc cfg =
  if Cfg_regalloc_utils.regalloc_debug
  then
    Cfg_with_layout.save_as_dot
      ~annotate_instr:[Cfg.print_instruction' ~print_reg:print_reg_as_loc]
      ~filename:"after.dot" cfg "after_allocation_before_validation";
  Description.verify desc cfg;
  let module Check_backwards = Check_backwards (struct
    let description = desc
  end) in
  let res_instr =
    Check_backwards.run (Cfg_with_layout.cfg cfg) ~init:Domain.bot
      ~map:Check_backwards.Instr ()
    |> Result.get_ok
  in
  let res_block =
    Check_backwards.run (Cfg_with_layout.cfg cfg) ~init:Domain.bot
      ~map:Check_backwards.Block ()
    |> Result.get_ok
  in
  if Cfg_regalloc_utils.regalloc_debug
  then
    save_as_dot_with_equations ~desc ~res_instr ~res_block ~filename:"annot.dot"
      cfg "after_allocation_after_validation";
  let result =
    let cfg = Cfg_with_layout.cfg cfg in
    let entry_block = Cfg.entry_label cfg |> Cfg.get_block_exn cfg in
    let entry_id =
      match entry_block.body with
      | [] -> entry_block.terminator.id
      | instr :: _ -> instr.id
    in
    Cfg_dataflow.Instr.Tbl.find res_instr entry_id
  in
  match result with
  | { error = None; _ } -> cfg
  | { error =
        Some
          (Terminator
             { equations; message; reg_instr = _; loc_instr = _; exn_equations }
          as error);
      _
    }
  | { error =
        Some
          (Basic
             { equations; message; reg_instr = _; loc_instr = _; exn_equations }
          as error);
      _
    } ->
    let id, instr =
      match error with
      | Basic { loc_instr; _ } ->
        ( loc_instr.id,
          fun ppf -> Format.fprintf ppf "%a" Cfg.print_basic loc_instr )
      | Terminator { loc_instr; _ } ->
        ( loc_instr.id,
          fun ppf -> Format.fprintf ppf "%a" Cfg.print_terminator loc_instr )
    in
    Format.printf "Check failed %d:\n%t:\nMessage: %s\n" id instr message;
    Format.printf "Equations at moment of error: [%a]\n" Equation_set.print
      equations;
    Option.iter
      (fun exn_equations ->
        Format.printf
          "Additional equations coming from the exception path: [%a]\n"
          Equation_set.print exn_equations)
      exn_equations;
    Format.printf "Dumping cfg ...\n";
    Format.print_flush ();
    let filename =
      Filename.temp_file
        (X86_proc.string_of_symbol "" (Cfg_with_layout.cfg cfg).fun_name ^ "_")
        ".dot"
    in
    let res_instr =
      Check_backwards.run (Cfg_with_layout.cfg cfg) ~init:Domain.bot
        ~map:Check_backwards.Instr ()
      |> Result.get_ok
    in
    let res_block =
      Check_backwards.run (Cfg_with_layout.cfg cfg) ~init:Domain.bot
        ~map:Check_backwards.Block ()
      |> Result.get_ok
    in
    save_as_dot_with_equations ~desc ~res_instr ~res_block ~filename cfg
      "vallidation_error";
    Format.printf "Cfg dumped into: %s\n" filename;
    Format.print_flush ();
    exit 1
