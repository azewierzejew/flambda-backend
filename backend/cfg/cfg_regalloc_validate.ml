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
    (* Check that stamps are equal iff every value in the [Register] is
       equal. *)
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
      ~is_regalloc_specific:
        (match instr.desc with Op (Spill | Reload) -> true | _ -> false)
      t.instructions instr

  let make_terminator_helper t f instr =
    f ~is_regalloc_specific:false t.terminators instr

  let add_instr ~is_regalloc_specific instructions instr =
    let id = instr.id in
    if is_regalloc_specific
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

  let create cfg =
    if Cfg_regalloc_utils.regalloc_debug
    then
      Cfg_with_layout.save_as_dot ~filename:"before.dot" cfg
        "before_allocation_before_validation";
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
        match reg_desc.Register.loc, Location.of_reg loc_reg with
        | _, None ->
          Cfg_regalloc_utils.fatal
            "The instruction's no. %d %s is still unknown after allocation" id
            name
        | None, _ -> ()
        | Some l1, Some l2 when Location.equal l1 l2 -> ()
        | Some prev_loc, Some new_loc ->
          Cfg_regalloc_utils.fatal
            "The instruction's no. %d %s has changed precolored location from \
             %a to %a"
            id name Location.print prev_loc Location.print new_loc)
      reg_arr loc_arr;
    ()

  let verify_instr ~seen_ids ~is_regalloc_specific instructions instr =
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
        Cfg_regalloc_utils.fatal "The instruction's no. %d desc was changed" id;
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
        "Register allocation added non-regalloc specific instruction no. %d" id

  let verify t cfg =
    let seen_ids =
      Hashtbl.create
        (Hashtbl.length t.instructions + Hashtbl.length t.terminators)
    in
    Cfg_with_layout.iter_instructions cfg
      ~instruction:(make_instruction_helper t (verify_instr ~seen_ids))
      ~terminator:(make_terminator_helper t (verify_instr ~seen_ids));
    Hashtbl.iter
      (fun id instr ->
        (* CR azewierzejew for azewierzejew: We would like to do an actual check
           whether [Prologue] can be removed. *)
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
      t.terminators
end

module Equation_set : sig
  type t

  val empty : t

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

  val is_empty : t -> bool

  val print : Format.formatter -> t -> unit
end = struct
  module Equation = struct
    type t = Register.t * Location.t

    let compare (r1, l1) (r2, l2) =
      let r_cmp = Register.compare r1 r2 in
      if r_cmp <> 0 then r_cmp else Location.compare l1 l2

    let print ppf (r, l) =
      Format.fprintf ppf "%a=%a" Register.print r Location.print l
  end

  include Set.Make (Equation)

  let compatibile_one ~reg ~loc t =
    let res = ref (Ok ()) in
    iter
      (fun ((eq_reg, eq_loc) as eq) ->
        let reg_eq = Register.equal eq_reg reg in
        let loc_eq = Location.equal eq_loc loc in
        if reg_eq <> loc_eq
        then (
          Format.fprintf Format.str_formatter
            "Unsatisfiable equations when removing result equations. Equation \
             %a. Result reg: %a, result location: %a"
            Equation.print eq Register.print reg Location.print loc;
          let message = Format.flush_str_formatter () in
          res := Error message))
      t;
    !res

  let remove_result ~reg_res ~loc_res t =
    let compatibile = ref (Ok ()) in
    Array.iter2
      (fun reg loc ->
        compatibile
          := Result.bind !compatibile (fun () -> compatibile_one ~reg ~loc t))
      reg_res loc_res;
    Result.bind !compatibile (fun () ->
        let t = ref t in
        Array.iter2 (fun reg loc -> t := remove (reg, loc) !t) reg_res loc_res;
        Ok !t)

  let verify_destroyed_locations ~destroyed t =
    (* CR azewierzejew for azewierzejew: Add checking stack for stack_location
       other than Local. *)
    Array.fold_left
      (fun acc des_loc ->
        Result.bind acc (fun () ->
            fold
              (fun (_stamp, loc) acc ->
                Result.bind acc (fun () ->
                    if des_loc <> loc
                    then Ok ()
                    else (
                      Format.fprintf Format.str_formatter
                        "Destroying a live location %a" Location.print des_loc;
                      let message = Format.flush_str_formatter () in
                      Error message)))
              t (Ok ())))
      (Ok ()) destroyed

  let add_argument ~reg_arg ~loc_arg t =
    let t = ref t in
    Array.iter2 (fun reg loc -> t := add (reg, loc) !t) reg_arg loc_arg;
    !t

  let rename_loc ~arg ~res t =
    map
      (fun (stamp, loc) ->
        if Location.equal loc res then stamp, arg else stamp, loc)
      t

  let rename_reg ~arg ~res t =
    map
      (fun (eq_reg, loc) ->
        if Register.equal eq_reg res then arg, loc else eq_reg, loc)
      t

  let print ppf t =
    let first = ref true in
    iter
      (fun eq ->
        if !first then first := false else Format.fprintf ppf " ";
        Format.fprintf ppf "%a" Equation.print eq)
      t
end

let extract_loc_arr loc_arr =
  Array.map (fun loc_reg -> Location.of_reg_exn loc_reg) loc_arr

module type Description_value = sig
  val description : Description.t
end

let print_reg_as_loc ppf reg =
  Printmach.loc ~reg_class:(Proc.register_class reg)
    ~unknown:(fun ppf -> Format.fprintf ppf "<Unknown>")
    ppf reg.Reg.loc

module Domain = struct
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

    let print_packed ppf (error : packed) =
      let message, equations, exn_equations, id, reg_instr, loc_instr =
        match error with
        | Basic { loc_instr; reg_instr; equations; exn_equations; message } ->
          ( message,
            equations,
            exn_equations,
            loc_instr.id,
            `Basic (Instruction.to_prealloc ~alloced:loc_instr reg_instr),
            `Basic loc_instr )
        | Terminator { loc_instr; reg_instr; equations; exn_equations; message }
          ->
          ( message,
            equations,
            exn_equations,
            loc_instr.id,
            `Terminator (Instruction.to_prealloc ~alloced:loc_instr reg_instr),
            `Terminator loc_instr )
      in
      Format.fprintf ppf "Check failed in instr %d:\n" id;
      Format.fprintf ppf "pre: %a\n" Cfg.print_instruction reg_instr;

      Format.fprintf ppf "post: %a\n"
        (Cfg.print_instruction' ~print_reg:print_reg_as_loc)
        loc_instr;
      Format.fprintf ppf "Message: %s\n" message;
      Format.fprintf ppf "Equations at moment of error: [%a]\n"
        Equation_set.print equations;
      Option.iter
        (fun exn_equations ->
          Format.fprintf ppf
            "Additional equations coming from the exception path: [%a]\n"
            Equation_set.print exn_equations)
        exn_equations;
      ()
  end

  (** This type logically works as [(Equation_set.t, Error.packed) Result.t] but
      in case there's an error we want to know the "last known equations" for a
      given instruction. Therefore [{equations; error = None}] corresponds to a
      [Ok equations] and [{equations; error = Some error}] corresponds to [Error
      error] where [equations] is biggest set of equations for a given
      instruction known before the error was found. All the values inside
      [error] correspond to values from the point of error. *)
  type t =
    { equations : Equation_set.t;
      error : Error.packed option
    }

  let bot = { equations = Equation_set.empty; error = None }

  let compare = compare

  let join t_old t_suc =
    match t_old, t_suc with
    | { error = Some _; _ }, _ ->
      (* If the last known value is an error do not update. *)
      t_old
    | { equations; error = None }, { error = Some error; _ } ->
      (* If the joined value is an error then pass through the error but keep
         the old set of equations as it's more informative. *)
      { equations; error = Some error }
    | { equations = eq_old; error = None }, { equations = eq_suc; error = None }
      ->
      (* If there are no errors combine the equation sets. *)
      { equations = Equation_set.union eq_old eq_suc; error = None }

  let less_equal t_new t_old =
    match t_new, t_old with
    | _, { error = Some _; _ } ->
      (* If the already known value is an error don't update results in order to
         terminate quickly. *)
      true
    | { error = Some _; _ }, { error = None; _ } ->
      (* If the new value is an error, always propagate. *)
      false
    | ( { error = None; equations = eq_set_new },
        { error = None; equations = eq_set_old } ) ->
      (* When there are no errors don't propagate only if the set of equations
         is exactly the same. There's no point in checking the inclusiveness of
         the sets. *)
      Equation_set.equal eq_set_new eq_set_old

  let to_string _ = failwith "[to_string] unimplemented"

  let to_result t =
    match t.error with Some error -> Error error | None -> Ok t.equations

  (** For equations coming from exceptional path remove the expected equations. *)
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
             (* First remove the result equations. *)
             Equation_set.remove_result ~reg_res:reg_instr.Instruction.res
               ~loc_res:(extract_loc_arr loc_instr.res)
               equations
             |> wrap_error)
      |> bind (fun equations ->
             (* Join the exceptional path equations. *)
             exn
             |> Result.map (fun exn_equations ->
                    Equation_set.union equations exn_equations))
      |> bind (fun equations ->
             (* Verify the destroyed registers (including the exceptional
                path). *)
             Equation_set.verify_destroyed_locations ~destroyed equations
             |> Result.map (fun () -> equations)
             |> wrap_error)
      |> Result.map (fun equations ->
             (* Add all eqations for the arguments. *)
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

  let print ppf t =
    (match t.error with None -> () | Some _ -> Format.fprintf ppf "ERROR ");
    Equation_set.print ppf t.equations;
    ()
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
      (* This corresponds to a noop move where the source and target registers
         have the same locations. *)
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
      Domain.append_equations t ~tag:Basic ~exn ~reg_instr:instr_before
        ~loc_instr:instr
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

  (* This should remove the equations for the exception value, but we do that in
     [Domain.append_equations] because there we have more information to give if
     there's an error. *)
  let exception_ t = t
end

module Check_backwards (Desc_val : Description_value) =
  Cfg_dataflow.Backward (Domain) (Transfer (Desc_val))

let save_as_dot_with_equations ~desc ~res_instr ~res_block ?filename cfg msg =
  Cfg_with_layout.save_as_dot
    ~annotate_instr:
      [ (fun ppf instr ->
          let id =
            match instr with
            | `Basic instr -> instr.id
            | `Terminator instr -> instr.id
          in
          Cfg_dataflow.Instr.Tbl.find res_instr id |> Domain.print ppf);
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
      Label.Tbl.find res_block block.start |> Domain.print ppf)
    ?filename cfg msg;
  ()

module Error = struct
  module Source = struct
    type t =
      | At_instruction of Domain.Error.packed
      | At_entrypoint of
          { message : string;
            equations : Equation_set.t;
            fun_args : Reg.t array
          }

    let print (ppf : Format.formatter) (t : t) : unit =
      match t with
      | At_instruction error -> Domain.Error.print_packed ppf error
      | At_entrypoint { message; equations; fun_args } ->
        Format.fprintf ppf "Bad eqauations at entry point, reason: %s\n" message;
        Format.fprintf ppf "Equations: %a\n" Equation_set.print equations;
        Format.fprintf ppf "Function arguments: %a\n" Printmach.regs fun_args;
        ()
  end

  type t =
    { source : Source.t;
      res_instr : Domain.t Cfg_dataflow.Instr.Tbl.t;
      res_block : Domain.t Label.Tbl.t;
      desc : Description.t;
      cfg : Cfg_with_layout.t
    }

  let print (ppf : Format.formatter) ({ source; _ } : t) : unit =
    Source.print ppf source

  let dump (ppf : Format.formatter)
      ({ source; res_instr; res_block; desc; cfg } : t) : unit =
    Source.print ppf source;
    let filename =
      Filename.temp_file
        (X86_proc.string_of_symbol "" (Cfg_with_layout.cfg cfg).fun_name ^ "_")
        ".dot"
    in
    Format.fprintf ppf "Dumping cfg into %s ...\n" filename;
    save_as_dot_with_equations ~desc ~res_instr ~res_block ~filename cfg
      "vallidation_error";
    Format.fprintf ppf "Dumped cfg into: %s\n" filename;
    ()
end

let verify_entrypoint (equations : Equation_set.t) (cfg : Cfg_with_layout.t) :
    (Cfg_with_layout.t, Error.Source.t) Result.t =
  let fun_args = (Cfg_with_layout.cfg cfg).fun_args in
  let bind f r = Result.bind r f in
  Equation_set.remove_result
    ~reg_res:(Array.map Register.create fun_args)
    ~loc_res:(extract_loc_arr fun_args) equations
  |> bind (fun equations ->
         if Equation_set.is_empty equations
         then Ok cfg
         else (
           Format.fprintf Format.str_formatter
             "Equations present at entrypoint after removing parameter \
              equations: [%a]"
             Equation_set.print equations;
           let message = Format.flush_str_formatter () in
           Error message))
  |> Result.map_error (fun message : Error.Source.t ->
         At_entrypoint { message; equations; fun_args })

let verify (desc : Description.t) (cfg : Cfg_with_layout.t) :
    (Cfg_with_layout.t, Error.t) Result.t =
  if Cfg_regalloc_utils.regalloc_debug
  then
    Cfg_with_layout.save_as_dot
      ~annotate_instr:[Cfg.print_instruction' ~print_reg:print_reg_as_loc]
      ~filename:"after.dot" cfg "after_allocation_before_validation";
  Description.verify desc cfg;
  let module Check_backwards = Check_backwards (struct
    let description = desc
  end) in
  let res_instr, res_block =
    Check_backwards.run (Cfg_with_layout.cfg cfg) ~init:Domain.bot
      ~map:Check_backwards.Both ()
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
  | { error = None; equations } ->
    verify_entrypoint equations cfg
    |> Result.map_error (fun source : Error.t ->
           { source; res_instr; res_block; desc; cfg })
  | { error = Some error; _ } ->
    Error { source = At_instruction error; res_instr; res_block; desc; cfg }

let verify_exn desc cfg =
  match verify desc cfg with
  | Ok cfg -> cfg
  | Error error ->
    Format.printf "%a%!" Error.dump error;
    exit 1
