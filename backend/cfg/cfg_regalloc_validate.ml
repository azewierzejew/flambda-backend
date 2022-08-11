[@@@ocaml.warning "+a-4-30-40-41-42"]

include Cfg_intf.S

let save_as_dot ?show_instr ?show_exn ?annotate_instr ?annotate_block
    ?annotate_block_end ?annotate_succ t filename =
  let filename = Printf.sprintf "%s.dot" filename in
  if !Cfg.verbose then Printf.printf "Writing cfg to %s\n" filename;
  let oc = open_out filename in
  Misc.try_finally
    (fun () ->
      let ppf = Format.formatter_of_out_channel oc in
      Cfg_with_layout.print_dot ?show_instr ?show_exn ?annotate_instr
        ?annotate_block ?annotate_block_end ?annotate_succ ppf t)
    ~always:(fun () -> close_out oc)
    ~exceptionally:(fun _exn -> Misc.remove_file filename)

module Description = struct
  module Instruction = struct
    type 'a t =
      { desc : 'a;
        arg : Reg.t array;
        res : Reg.t array
      }
  end

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
    save_as_dot cfg "before";
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
        { Instruction.desc = instr.desc; arg = instr.arg; res = instr.res }
    in
    let t =
      { instructions = Hashtbl.create 0; terminators = Hashtbl.create 0 }
    in
    Cfg_with_layout.iter_instructions cfg
      ~instruction:(make_instruction_helper t add_instr)
      ~terminator:(make_terminator_helper t add_instr);
    t

  let verify t cfg =
    let seen_ids = Hashtbl.create 0 in
    let check_instr is_regalloc_specific instructions instr =
      let id = instr.id in
      if Hashtbl.find_opt seen_ids id |> Option.is_some
      then
        Cfg_regalloc_utils.fatal
          "Duplicate instr id %d while checking post-allocation description" id;
      Hashtbl.add seen_ids id ();
      match Hashtbl.find_opt instructions id, is_regalloc_specific with
      (* The instruction was present before. *)
      | Some old_instr, false ->
        if instr.desc <> old_instr.Instruction.desc
        then Cfg_regalloc_utils.fatal "The instructions desc was changed %d" id;
        if Array.length instr.arg <> Array.length old_instr.Instruction.arg
        then
          Cfg_regalloc_utils.fatal
            "The instructions arg count has changed. Now: %d. After: %d." id
            (Array.length instr.arg)
            (Array.length old_instr.Instruction.arg);
        if Array.length instr.res <> Array.length old_instr.Instruction.res
        then
          Cfg_regalloc_utils.fatal
            "The instructions res count has changed. Now: %d. After: %d." id
            (Array.length instr.res)
            (Array.length old_instr.Instruction.res);
        ()
      (* Added spill/reload that wasn't before. *)
      | None, true -> ()
      | Some _, true ->
        Cfg_regalloc_utils.fatal
          "Register allocation changed existing instruction into a register \
           allocation specific instruction %d"
          id
      | None, false ->
        Cfg_regalloc_utils.fatal
          "Register allocation added non-regalloc specific instruction %d" id
    in
    Cfg_with_layout.iter_instructions cfg
      ~instruction:(make_instruction_helper t check_instr)
      ~terminator:(make_terminator_helper t check_instr);
    Hashtbl.iter
      (fun id instr ->
        let is_prologue =
          match instr.Instruction.desc with Prologue -> true | _ -> false
        in
        if Hashtbl.find_opt seen_ids id |> Option.is_none && not is_prologue
        then
          Cfg_regalloc_utils.fatal
            "Instruction %d was deleted by register allocator" id)
      t.instructions;
    Hashtbl.iter
      (fun id _ ->
        if Hashtbl.find_opt seen_ids id |> Option.is_none
        then
          Cfg_regalloc_utils.fatal
            "Terminator %d was deleted by register allocator" id)
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
    reg_res:Reg.t array -> loc_res:Reg.t array -> t -> (t, string) Result.t

  val verify_destroyed_registers :
    destroyed:Reg.t array -> t -> (unit, string) Result.t

  val add_argument : reg_arg:Reg.t array -> loc_arg:Reg.t array -> t -> t

  val rename_loc : arg:Reg.location -> res:Reg.location -> t -> t

  val rename_reg : arg:int -> res:int -> t -> t

  val print : Format.formatter -> t -> unit
end = struct
  module Equation = struct
    type t = int * Reg.location

    let compare = compare
  end

  include Set.Make (Equation)

  let compatibile_one ~reg ~loc t =
    assert (loc <> Reg.Unknown);
    for_all
      (fun (eq_stamp, eq_loc) ->
        let req_eq = eq_stamp = reg.Reg.stamp in
        let loc_eq = eq_loc = loc in
        req_eq = loc_eq)
      t

  let remove_result ~reg_res ~loc_res t =
    let compatibile =
      Array.for_all2
        (fun reg loc -> compatibile_one ~reg ~loc:loc.Reg.loc t)
        reg_res loc_res
    in
    if compatibile
    then (
      let t = ref t in
      Array.iter2
        (fun reg loc -> t := remove (reg.Reg.stamp, loc.Reg.loc) !t)
        reg_res loc_res;
      Ok !t)
    else Error "Unsatisfiable equations when removing result equations"

  let verify_destroyed_registers ~destroyed t =
    let correct =
      Array.for_all
        (fun reg -> for_all (fun (_stamp, loc) -> reg.Reg.loc <> loc) t)
        destroyed
    in
    if correct then Ok () else Error "Destroying a live register"

  let add_argument ~reg_arg ~loc_arg t =
    let t = ref t in
    Array.iter2
      (fun reg loc -> t := add (reg.Reg.stamp, loc.Reg.loc) !t)
      reg_arg loc_arg;
    !t

  let rename_loc ~arg ~res t =
    map (fun (stamp, loc) -> if loc = res then stamp, arg else stamp, loc) t

  let rename_reg ~arg ~res t =
    map (fun (stamp, loc) -> if stamp = res then arg, loc else stamp, loc) t

  let print ppf t =
    let first = ref true in
    iter
      (fun (stamp, loc) ->
        if !first then first := false else Format.fprintf ppf " ";
        Format.fprintf ppf "%d=%a" stamp
          (Printmach.loc ~unknown:(fun ppf -> Format.fprintf ppf "UK"))
          loc)
      t
end

module type Description_value = sig
  val description : Description.t
end

module Error = struct
  type 'a t =
    { equations : Equation_set.t;
      exn_equations : Equation_set.t option;
      reg_instr : 'a Description.Instruction.t;
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
    let reg = Proc.loc_exn_bucket in
    Equation_set.remove_result equations ~reg_res:[| reg |] ~loc_res:[| reg |]
    |> Result.map_error (fun message ->
           Printf.sprintf "While removing exn bucket: %s" message)

  let append_equations (type a) t ~(tag : a Error.Tag.t) ~exn
      ~(reg_instr : a Description.Instruction.t) ~(loc_instr : a instruction)
      ~destroyed =
    if loc_instr.id = 19
    then (
      Format.printf "Beg TEST 19\n";
      Format.printf "eq: %a\n" Equation_set.print t.equations;
      Format.printf "er: ";
      (match t.error with
      | None -> Format.printf "No error"
      | Some _ -> Format.printf "ERROR");
      Format.printf "\n";
      Format.printf "End TEST 19\n\n");
    let bind f res = Result.bind res f in
    let wrap_error res =
      Result.map_error
        (fun message ->
          Format.printf "Wrapping error\n";
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
      Option.value exn ~default:bot
      |> to_result
      (* Handle this here because in [exception_] we don't have enough info. *)
      |> bind (fun exn -> remove_exn_bucket exn |> wrap_error)
    in
    let res =
      to_result t
      |> bind (fun equations ->
             Equation_set.remove_result
               ~reg_res:reg_instr.Description.Instruction.res
               ~loc_res:loc_instr.res equations
             |> wrap_error)
      |> bind (fun equations ->
             exn
             |> Result.map (fun exn_equations ->
                    Equation_set.union equations exn_equations))
      |> bind (fun equations ->
             Equation_set.verify_destroyed_registers ~destroyed equations
             |> Result.map (fun () -> equations)
             |> wrap_error)
      |> Result.map (fun equations ->
             Equation_set.add_argument
               ~reg_arg:reg_instr.Description.Instruction.arg
               ~loc_arg:loc_instr.arg equations)
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
          Equation_set.rename_loc ~arg:loc_instr.arg.(0).loc
            ~res:loc_instr.res.(0).loc equations;
        error = None
      }

  let rename_register t ~reg_instr =
    match t with
    | { error = Some _; _ } -> t
    | { error = None; equations } ->
      let open! Description.Instruction in
      assert (Array.length reg_instr.arg = 1);
      assert (Array.length reg_instr.res = 1);
      { equations =
          Equation_set.rename_reg ~arg:reg_instr.arg.(0).stamp
            ~res:reg_instr.res.(0).stamp equations;
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
        ~destroyed:(Cfg_regalloc_utils.destroyed_at_basic instr.desc)

  let terminator t ~exn instr =
    let exn = if Cfg.can_raise_terminator instr.desc then Some exn else None in
    let instr_before = Hashtbl.find Desc_val.description.terminators instr.id in
    Domain.append_equations t ~tag:Terminator ~exn ~reg_instr:instr_before
      ~loc_instr:instr
      ~destroyed:(Cfg_regalloc_utils.destroyed_at_terminator instr.desc)

  let exception_ t = t
end

module Check_backwards (Desc_val : Description_value) =
  Cfg_dataflow.Backward (Domain) (Transfer (Desc_val))

let verify desc cfg =
  save_as_dot cfg "after";
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
  save_as_dot
    ~annotate_instr:(fun id ->
      let res = Cfg_dataflow.Instr.Tbl.find res_instr id in
      (match res.Domain.error with
      | None -> ()
      | Some _ -> Format.fprintf Format.str_formatter "ERROR ");
      Equation_set.print Format.str_formatter res.Domain.equations;
      Format.flush_str_formatter ())
    ~annotate_block_end:(fun block ->
      let res = Label.Tbl.find res_block block.start in
      (match res.Domain.error with
      | None -> ()
      | Some _ -> Format.fprintf Format.str_formatter "ERROR ");
      Equation_set.print Format.str_formatter res.Domain.equations;
      Format.flush_str_formatter ())
    cfg "annot";
  Format.print_flush ();
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
  (match result with
  | { error = None; _ } -> Printf.printf "Check SUCCESS\n"
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
    let id, desc =
      match error with
      | Basic { loc_instr; _ } ->
        ( loc_instr.id,
          fun ppf -> Format.fprintf ppf "%a" Cfg.print_basic loc_instr )
      | Terminator { loc_instr; _ } ->
        ( loc_instr.id,
          fun ppf -> Format.fprintf ppf "%a" Cfg.print_terminator loc_instr )
    in

    Format.printf "Check failed %d: %t: %s\n" id desc message;
    Format.printf "Equations at moment of error: [%a]\n" Equation_set.print
      equations;
    Option.iter
      (fun exn_equations ->
        Format.printf
          "Additional equations coming from the exception path: [%a]\n"
          Equation_set.print exn_equations)
      exn_equations;
    Format.print_flush ());
  cfg
