(** This module implement validator for register allocation. The algorithm is
    based on a paper by Silvain Rideau and Xavier Leroy titles "Validating
    Register Allocation and Spilling" which can be found here

    [1] https://xavierleroy.org/publi/validation-regalloc.pdf

    The solution is substantially adapted to the different representation of CFG
    that is used in this compiler. Most of the differences actually simpilify
    the computation e.g. the arguments for a function call are specified as
    preassigned registers and we don't have to reconstruct the argument
    locations from the function type. *)

[@@@ocaml.warning "+a-4-30-40-41-42"]

include Cfg_intf.S

module Location : sig
  type t

  val of_reg : Reg.t -> t option

  val of_reg_exn : Reg.t -> t

  val to_loc_lossy : t -> Reg.location

  val print : Format.formatter -> t -> unit

  val compare : t -> t -> int

  val equal : t -> t -> bool
end = struct
  module Stack = struct
    type t =
      | Local of
          { index : int;
            reg_class : int
          }
      | Incoming of { index : int }
      | Outgoing of { index : int }
      | Domainstate of { index : int }

    let word_size = 8

    let byte_bits = 8

    let check_word_size () =
      (* CR azewierzejew: This seems good enough but maybe we would want to
         consider unaligned offsets or 32-bit architecture. *)
      if Sys.word_size <> word_size * byte_bits
      then
        Cfg_regalloc_utils.fatal
          "regalloc validation only supports 64 bit architecture, got word \
           size %d"
          Sys.word_size

    let byte_offset_to_word_index offset =
      check_word_size ();
      if offset mod word_size <> 0
      then
        Cfg_regalloc_utils.fatal
          "regalloc validation expects aligned offsets, got offset %d with \
           remainder %d"
          offset (offset mod word_size);
      offset / word_size

    let word_index_to_byte_offset index =
      check_word_size ();
      index * word_size

    let of_stack_loc ~reg_class loc =
      match loc with
      | Reg.Local index -> Local { index; reg_class }
      | Reg.Incoming offset ->
        Incoming { index = byte_offset_to_word_index offset }
      | Reg.Outgoing offset ->
        Outgoing { index = byte_offset_to_word_index offset }
      | Reg.Domainstate offset ->
        Domainstate { index = byte_offset_to_word_index offset }

    let to_stack_loc_lossy t =
      match t with
      | Local { index; _ } -> Reg.Local index
      | Incoming { index } -> Reg.Incoming (word_index_to_byte_offset index)
      | Outgoing { index } -> Reg.Outgoing (word_index_to_byte_offset index)
      | Domainstate { index } ->
        Reg.Domainstate (word_index_to_byte_offset index)

    let unknown_reg_class = -1

    let reg_class_lossy t =
      match t with
      | Local { reg_class; _ } -> reg_class
      | Incoming _ | Outgoing _ | Domainstate _ -> unknown_reg_class
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
      ~unknown:(fun _ -> assert false)
      ppf (to_loc_lossy t)

  let compare (t1 : t) (t2 : t) : int =
    (* CR-someday azewierzejew: Implement proper comparison. *)
    Stdlib.compare t1 t2

  let equal (t1 : t) (t2 : t) : bool = compare t1 t2 = 0
end

module Reg_id : sig
  type t =
    | Preassigned of { location : Location.t }
    | Named of { stamp : int }

  val compare : t -> t -> int

  val of_reg : Reg.t -> t

  val to_loc_lossy : t -> Reg.location

  val print :
    typ:Cmm.machtype_component ->
    raw_name:Reg.Raw_name.t ->
    spill:bool ->
    Format.formatter ->
    t ->
    unit
end = struct
  type t =
    | Preassigned of { location : Location.t }
    | Named of { stamp : int }

  let of_reg (reg : Reg.t) =
    let loc = Location.of_reg reg in
    if Option.is_some loc <> Reg.is_preassigned reg
    then
      Cfg_regalloc_utils.fatal
        "Mismatch between register having location (%b) and register being a \
         preassigned register (%b)"
        (Option.is_some loc) (Reg.is_preassigned reg);
    match loc with
    | Some location -> Preassigned { location }
    | None -> Named { stamp = reg.stamp }

  let to_loc_lossy t =
    match t with
    | Preassigned { location } -> Location.to_loc_lossy location
    | Named _ -> Reg.Unknown

  let compare (t1 : t) (t2 : t) =
    (* CR-someday azewierzejew: Implement proper comparison. *)
    Stdlib.compare t1 t2

  let print ~typ ~raw_name ~spill ppf t =
    match t with
    | Preassigned { location } ->
      Format.fprintf ppf "R[%a]" Location.print location
    | Named { stamp } ->
      Format.fprintf ppf "%a" Printmach.reg
        { Reg.dummy with raw_name; stamp; typ; spill }
end

module Register : sig
  module For_print : sig
    type t
  end

  type t =
    { reg_id : Reg_id.t;
      for_print : For_print.t
    }

  val create : Reg.t -> t

  val to_dummy_reg : t -> Reg.t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val print : Format.formatter -> t -> unit
end = struct
  module For_print = struct
    type t =
      { raw_name : Reg.Raw_name.t;
        stamp : int;
        typ : Cmm.machtype_component;
        spill : bool
      }
  end

  type t =
    { reg_id : Reg_id.t;
      for_print : For_print.t
    }

  let create (reg : Reg.t) : t =
    { reg_id = Reg_id.of_reg reg;
      for_print =
        { raw_name = reg.raw_name;
          stamp = reg.stamp;
          typ = reg.typ;
          spill = reg.spill
        }
    }

  let to_dummy_reg (t : t) : Reg.t =
    { Reg.dummy with
      raw_name = t.for_print.raw_name;
      typ = t.for_print.typ;
      stamp = t.for_print.stamp;
      loc = Reg_id.to_loc_lossy t.reg_id
    }

  let print (ppf : Format.formatter) (t : t) : unit =
    Reg_id.print ~typ:t.for_print.typ ~raw_name:t.for_print.raw_name
      ~spill:t.for_print.spill ppf t.reg_id

  let compare (t1 : t) (t2 : t) : int = Reg_id.compare t1.reg_id t2.reg_id

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

module Description : sig
  (** This snapshots the [desc], [arg] and [res] of all instructions in the CFG.
      This snapshots layout of the basic blocks implicitly by comparing [desc]
      of the terminators. This doesn't have information of where the basic
      instructions were located in the graph.

      With this the (register_before, location_after) pairs for results and
      arguments can be reconstructed while only having the CFG after the
      transformation.

      Such a things doesn't exist in the paper [1] but that's because there they
      have both CFG before and after transformation. Because the CFG here is
      mutable we only see the state after. This description allows us to
      reconstruct needed part's of the state before on the fly. *)
  type t

  (** Will never raise for instructions from the verified CFG that aren't
      regalloc specific (examples of regalloc specific instructions are [Spill]
      and [Reload]). *)
  val find_basic : t -> basic instruction -> basic Instruction.t

  (** Will never raise for a terminator from the verified CFG. *)
  val find_terminator : t -> terminator instruction -> terminator Instruction.t

  val create : Cfg_with_layout.t -> t

  val verify : t -> Cfg_with_layout.t -> unit
end = struct
  type t =
    { instructions : (int, basic Instruction.t) Hashtbl.t;
      terminators : (int, terminator Instruction.t) Hashtbl.t
    }

  let find_basic t instr = Hashtbl.find t.instructions instr.id

  let find_terminator t instr = Hashtbl.find t.terminators instr.id

  let make_instruction_helper t f instr =
    f
      ~is_regalloc_specific:
        (match instr.desc with Op (Spill | Reload) -> true | _ -> false)
      t.instructions instr

  let make_terminator_helper t f instr =
    f ~is_regalloc_specific:false t.terminators instr

  let add_instr ~seen_ids ~is_regalloc_specific instructions instr =
    let id = instr.id in
    if Hashtbl.mem seen_ids id
    then
      Cfg_regalloc_utils.fatal
        "Duplicate instruction no. %d while creating pre-allocation description"
        id;
    Hashtbl.add seen_ids id ();
    if is_regalloc_specific
    then
      Cfg_regalloc_utils.fatal
        "Instruction no. %d is specific to the regalloc phase while creating \
         pre-allocation description"
        id;
    Hashtbl.add instructions id
      { Instruction.desc = instr.desc;
        arg = Array.map Register.create instr.arg;
        res = Array.map Register.create instr.res
      }

  let create cfg =
    Cfg_regalloc_utils.precondition cfg;
    if Cfg_regalloc_utils.validator_debug
    then
      (* CR-someday: We don't save the file with [fun_name] in the filename
         because there is an appended stamp that is fragile and is annoying when
         testing. Currently it's not a problem because we abort the build
         whenever register allocation fails but if there was a fallback mode
         then the interesting files would be instantly overwritten. *)
      Cfg_with_layout.save_as_dot ~filename:"before.dot" cfg
        "before_allocation_before_validation";
    let basic_count, terminator_count =
      Cfg_with_layout.fold_instructions cfg
        ~instruction:(fun (basic_count, terminator_count) _ ->
          basic_count + 1, terminator_count)
        ~terminator:(fun (basic_count, terminator_count) _ ->
          basic_count, terminator_count + 1)
        ~init:(0, 0)
    in
    let seen_ids = Hashtbl.create (basic_count + terminator_count) in
    let t =
      { instructions = Hashtbl.create basic_count;
        terminators = Hashtbl.create terminator_count
      }
    in
    Cfg_with_layout.iter_instructions cfg
      ~instruction:(make_instruction_helper t (add_instr ~seen_ids))
      ~terminator:(make_terminator_helper t (add_instr ~seen_ids));
    t

  let verify_reg_array ~id ~name ~reg_arr ~loc_arr =
    if Array.length reg_arr <> Array.length loc_arr
    then
      Cfg_regalloc_utils.fatal
        "The instruction's no. %d %s count has changed. Before: %d. Now: %d." id
        name (Array.length reg_arr) (Array.length loc_arr);
    Array.iter2
      (fun (reg_desc : Register.t) loc_reg ->
        match reg_desc.reg_id, Location.of_reg loc_reg with
        | _, None ->
          Cfg_regalloc_utils.fatal
            "The instruction's no. %d %s is still unknown after allocation" id
            name
        | Named { stamp = _ }, _ -> ()
        | Preassigned { location = l1 }, Some l2 when Location.equal l1 l2 -> ()
        | Preassigned { location = prev_loc }, Some new_loc ->
          Cfg_regalloc_utils.fatal
            "The instruction's no. %d %s has changed preassigned register's \
             location from %a to %a"
            id name Location.print prev_loc Location.print new_loc)
      reg_arr loc_arr;
    ()

  let verify_instr ~seen_ids ~is_regalloc_specific instructions instr =
    let id = instr.id in
    if Hashtbl.mem seen_ids id
    then
      Cfg_regalloc_utils.fatal
        "Duplicate instruction no. %d while checking post-allocation \
         description"
        id;
    Hashtbl.add seen_ids id ();
    match Hashtbl.find_opt instructions id, is_regalloc_specific with
    (* The instruction was present before. *)
    | Some old_instr, false ->
      (* CR-someday azewierzejew: Avoid using polymrphic compare. That is tricky
         because here we can compare both [basic] and [terminator]. *)
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
    Cfg_regalloc_utils.postcondition cfg;
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
        if (not (Hashtbl.mem seen_ids id)) && not can_be_removed
        then
          Cfg_regalloc_utils.fatal
            "Instruction no. %d was deleted by register allocator" id)
      t.instructions;
    Hashtbl.iter
      (fun id _ ->
        if not (Hashtbl.mem seen_ids id)
        then
          Cfg_regalloc_utils.fatal
            "Terminator no. %d was deleted by register allocator" id)
      t.terminators
end

module Equation_set : sig
  (** This corresponds to the set of equations defined in section 3.2 of in the
      paper [1]. The definition is simplified substantially because here none of
      the locations (e.g. registers or stack) are allowed to overlap. *)
  type t

  val empty : t

  val union : t -> t -> t

  val subset : t -> t -> bool

  (** This corresponds to case (10) in Fig. 1 of the paper [1]. *)
  val rename_loc : arg:Location.t -> res:Location.t -> t -> t

  (** This corresponds to case (3) in Fig. 1 of the paper [1]. *)
  val rename_reg : arg:Register.t -> res:Register.t -> t -> t

  (** Calling [remove_result], [verify_destoyed_locations] and [add_argument] in
      this order corresponds to case (7) in Fig. 1 of the paper [1]. This
      implementation is also generalized for all cases not handled by
      [rename_loc] or [rename_reg]. *)
  val remove_result :
    reg_res:Register.t array ->
    loc_res:Location.t array ->
    t ->
    (t, string) Result.t

  val verify_destroyed_locations :
    destroyed:Location.t array -> t -> (t, string) Result.t

  val add_argument :
    reg_arg:Register.t array -> loc_arg:Location.t array -> t -> t

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

  exception Verification_failed of string

  include Set.Make (Equation)

  let array_fold2 f acc arr1 arr2 =
    let acc = ref acc in
    Array.iter2 (fun v1 v2 -> acc := f !acc v1 v2) arr1 arr2;
    !acc

  let compatible_one ~reg ~loc t =
    iter
      (fun ((eq_reg, eq_loc) as eq) ->
        (* This check corresponds to simplified check that "(x, l) is compatible
           with E" from chapter 3.2 section "Unsatisfiability and Overlap" from
           the paper [1], where "x" is [reg] and "l" is [loc]. Because we don't
           consider overlap at all, the condition simplifies to [(x' = x && l' =
           l) || (x' <> x && l' <> l)]. *)
        let reg_eq = Register.equal eq_reg reg in
        let loc_eq = Location.equal eq_loc loc in
        if not (Bool.equal reg_eq loc_eq)
        then (
          Format.fprintf Format.str_formatter
            "Unsatisfiable equations when removing result equations.\n\
             Existing equation has to agree one 0 or 2 sides (cannot on \
             exactly 1) with the removed equation.\n\
             Existing equation %a.\n\
             Removed equation: %a." Equation.print eq Equation.print (reg, loc);
          let message = Format.flush_str_formatter () in
          raise (Verification_failed message)))
      t

  let remove_result ~reg_res ~loc_res t =
    try
      Array.iter2 (fun reg loc -> compatible_one ~reg ~loc t) reg_res loc_res;
      let t =
        array_fold2 (fun t reg loc -> remove (reg, loc) t) t reg_res loc_res
      in
      Ok t
    with Verification_failed message -> Error message

  let verify_destroyed_locations ~destroyed t =
    (* CR azewierzejew for azewierzejew: Add checking stack for stack_location
       other than Local. *)
    try
      Array.iter
        (fun destroyed_loc ->
          iter
            (fun (live_reg, live_loc) ->
              if destroyed_loc = live_loc
              then (
                Format.fprintf Format.str_formatter
                  "Destroying a location %a in which a live register %a is \
                   stored"
                  Location.print live_loc Register.print live_reg;
                let message = Format.flush_str_formatter () in
                raise (Verification_failed message)))
            t)
        destroyed;
      Ok t
    with Verification_failed message -> Error message

  let add_argument ~reg_arg ~loc_arg t =
    array_fold2 (fun t reg loc -> add (reg, loc) t) t reg_arg loc_arg

  let rename_loc ~arg ~res t =
    map
      (fun ((stamp, loc) as eq) ->
        if Location.equal loc res then stamp, arg else eq)
      t

  let rename_reg ~arg ~res t =
    map
      (fun ((eq_reg, loc) as eq) ->
        if Register.equal eq_reg res then arg, loc else eq)
      t

  let print ppf t =
    let first = ref true in
    iter
      (fun eq ->
        if !first then first := false else Format.fprintf ppf " ";
        Format.fprintf ppf "%a" Equation.print eq)
      t
end

let extract_loc_arr loc_arr = Array.map Location.of_reg_exn loc_arr

module type Description_value = sig
  val description : Description.t
end

let print_reg_as_loc ppf reg =
  Printmach.loc ~reg_class:(Proc.register_class reg)
    ~unknown:(fun ppf -> Format.fprintf ppf "<Unknown>")
    ppf reg.Reg.loc

module Domain : sig
  (** This type corresponds to the domain of the dataflow from the paper [1]. It
      is represented as [(Ok equations)] corresponing to the set of equations
      from the paper [1] or [(Error error)] which corresponds to the "top" from
      the paper [1]. For the purposes of dataflow all [(Error error)] values are
      equal even though the carried error can be different. That is because we
      want to get an error information but if there are multiple errors we do
      not care which one we see. *)
  include Cfg_dataflow.Backward_domain

  module Error : sig
    type t

    module Tag : sig
      type 'a t =
        | Terminator : terminator t
        | Basic : basic t
    end

    val print : Format.formatter -> t -> unit
  end

  (** This corresponds to case (10) in Fig. 1 of the paper [1]. *)
  val rename_location : t -> loc_instr:_ instruction -> t

  (** This corresponds to case (3) in Fig. 1 of the paper [1]. *)
  val rename_register : t -> reg_instr:_ Instruction.t -> t

  (** This corresponds to case (7) in Fig. 1 of the paper [1] generalized for
      all other cases not handled by [rename_location] or [rename_register]. We
      have an additional parameter which is the equations for the exceptional
      path successor which is not present in the paper [1] because exceptions
      are not considered there. *)
  val append_equations :
    t ->
    tag:'a Error.Tag.t ->
    exn:t option ->
    reg_instr:'a Instruction.t ->
    loc_instr:'a instruction ->
    destroyed:Location.t array ->
    t

  val print : Format.formatter -> t -> unit

  (** Convert the domain value to its representation. *)
  val to_result : t -> (Equation_set.t, Error.t) Result.t
end = struct
  module Error = struct
    type 'a unpacked =
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

    type t =
      | Terminator : terminator unpacked -> t
      | Basic : basic unpacked -> t

    let print ppf (error : t) =
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
      Format.fprintf ppf "CFG REGALLOC Check failed in instr %d:\n" id;
      Format.fprintf ppf "Instruction's description before allocation: %a\n"
        Cfg.print_instruction reg_instr;
      Format.fprintf ppf "Instruction's description after allocation: %a\n"
        (Cfg.print_instruction' ~print_reg:print_reg_as_loc)
        loc_instr;
      Format.fprintf ppf "Message: %s\n" message;
      Format.fprintf ppf "Live equations for the normal successor: [%a]\n"
        Equation_set.print equations;
      Option.iter
        (fun exn_equations ->
          Format.fprintf ppf
            "Live equations for the exceptional successor: [%a]\n"
            Equation_set.print exn_equations)
        exn_equations;
      ()
  end

  (** This type logically works as [(Equation_set.t, Error.t) Result.t] but in
      case there's an error we want to know the "last known equations" for a
      given instruction. Therefore [{equations; error = None}] corresponds to a
      [Ok equations] and [{equations; error = Some error}] corresponds to [Error
      error] where [equations] is biggest set of equations for a given
      instruction known before the error was found. All the values inside
      [error] correspond to values from the point of error. *)
  type t =
    { equations : Equation_set.t;
      error : Error.t option
    }

  let bot = { equations = Equation_set.empty; error = None }

  let compare (t1 : t) (t2 : t) =
    (* CR-someday azewierzejew: Implement proper comparison. *)
    Stdlib.compare t1 t2

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

  let less_equal t1 t2 =
    match t1, t2 with
    | _, { error = Some _; _ } ->
      (* Error is the greatest element in the order so it's larger or equal to
         every other element. *)
      true
    | { error = Some _; _ }, { error = None; _ } ->
      (* Error is strictly greater than every non-error element so false.*)
      false
    | ( { error = None; equations = eq_set1 },
        { error = None; equations = eq_set2 } ) ->
      (* If neither of the value is an error then compare the equation sets. *)
      Equation_set.subset eq_set1 eq_set2

  let to_string _ = failwith "[to_string] unimplemented"

  let to_result t =
    match t.error with Some error -> Error error | None -> Ok t.equations

  (** For equations coming from exceptional path remove the expected equations. *)
  let remove_exn_bucket equations =
    let phys_reg = Proc.loc_exn_bucket in
    let reg = Register.create phys_reg in
    let loc =
      match reg.reg_id with
      | Preassigned { location } -> location
      | Named _ -> assert false
    in
    Equation_set.remove_result equations ~reg_res:[| reg |] ~loc_res:[| loc |]
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
      exn
      |> Option.map (fun exn ->
             (* Handle the exceptional path specific conversions here because in
                [exception_] we don't have enough information in order to give a
                meaningful error message. *)
             to_result exn
             (* Remove the equality for [exn_bucket] if it exists. *)
             |> bind (fun exn -> remove_exn_bucket exn |> wrap_error)
             |> bind (fun equations ->
                    (* Verify the destroyed registers for exceptional path
                       only. *)
                    equations
                    |> Equation_set.verify_destroyed_locations
                         ~destroyed:(extract_loc_arr Proc.destroyed_at_raise)
                    |> Result.map_error (fun message ->
                           Printf.sprintf
                             "While verifying locations destroyed at raise: %s"
                             message)
                    |> wrap_error))
      (* If instruction can't raise [Option.is_none exn] then use empty set of
         equations as that's the same as skipping the step. *)
      |> Option.value ~default:(to_result bot)
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

  let rename_register t ~(reg_instr : _ Instruction.t) =
    match t with
    | { error = Some _; _ } -> t
    | { error = None; equations } ->
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

  let[@inline] transfer_generic (type a) (tag : a Domain.Error.Tag.t)
      ~(find_description : Description.t -> a instruction -> a Instruction.t)
      ~(can_raise : a -> bool) ~(destroyed_at : a -> Reg.t array) :
      domain -> exn:domain -> a instruction -> domain =
   fun t ~exn instr ->
    let exn = if can_raise instr.desc then Some exn else None in
    let instr_before = find_description Desc_val.description instr in
    Domain.append_equations t ~tag ~exn ~reg_instr:instr_before ~loc_instr:instr
      ~destroyed:(destroyed_at instr.desc |> extract_loc_arr)

  let basic t ~exn instr =
    match instr.desc with
    | Op (Spill | Reload) ->
      assert (not (Cfg.can_raise_basic instr.desc));
      Domain.rename_location t ~loc_instr:instr
    | Op Move
      when Array.length instr.arg = 1
           && Array.length instr.res = 1
           && Reg.same_loc instr.arg.(0) instr.res.(0) ->
      (* This corresponds to a noop move where the source and target registers
         have the same locations. *)
      assert (not (Cfg.can_raise_basic instr.desc));
      let instr_before = Description.find_basic Desc_val.description instr in
      Domain.rename_register t ~reg_instr:instr_before
    | _ ->
      transfer_generic Domain.Error.Tag.Basic
        ~find_description:Description.find_basic ~can_raise:Cfg.can_raise_basic
        ~destroyed_at:Cfg_regalloc_utils.destroyed_at_basic t ~exn instr

  let terminator t ~exn instr =
    (* CR-soon azewierzejew: This is kind of fragile for [Tailcall (Self _)]
       because that instruction doesn't strictly adhere to generic semantics. *)
    transfer_generic Domain.Error.Tag.Terminator
      ~find_description:Description.find_terminator
      ~can_raise:Cfg.can_raise_terminator
      ~destroyed_at:Cfg_regalloc_utils.destroyed_at_terminator t ~exn instr

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
            match Description.find_basic desc instr with
            | prev_instr ->
              let instr = Instruction.to_prealloc ~alloced:instr prev_instr in
              Cfg.print_basic ppf instr
            | exception Not_found -> ())
          | `Terminator ti ->
            let prev_ti = Description.find_terminator desc ti in
            let ti = Instruction.to_prealloc ~alloced:ti prev_ti in
            Cfg.print_terminator ppf ti) ]
    ~annotate_block_end:(fun ppf block ->
      Label.Tbl.find res_block block.start |> Domain.print ppf)
    ?filename cfg msg;
  ()

module Error = struct
  module Source = struct
    type t =
      | At_instruction of Domain.Error.t
      | At_entrypoint of
          { message : string;
            equations : Equation_set.t;
            fun_args : Reg.t array
          }

    let print (ppf : Format.formatter) (t : t) : unit =
      match t with
      | At_instruction error -> Domain.Error.print ppf error
      | At_entrypoint { message; equations; fun_args } ->
        Format.fprintf ppf "Bad equations at entry point, reason: %s\n" message;
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
      "validation_error";
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
         (* This check is stronger than the one in the paper [1]. That because C
            allows to start with uninitialized variables as it's explained in
            chapter 3.2 and of section "Dataflow Analysis and Its Uses". Such a
            thing is not allowed in OCaml. Therefore after removing all
            equations for arguments the should be no additional equations
            left. *)
         if Equation_set.is_empty equations
         then Ok cfg
         else (
           Format.fprintf Format.str_formatter
             "Some equations still present at entrypoint after removing \
              parameter equations: [%a]"
             Equation_set.print equations;
           let message = Format.flush_str_formatter () in
           Error message))
  |> Result.map_error (fun message : Error.Source.t ->
         At_entrypoint { message; equations; fun_args })

let test (desc : Description.t) (cfg : Cfg_with_layout.t) :
    (Cfg_with_layout.t, Error.t) Result.t =
  if Cfg_regalloc_utils.validator_debug
  then
    (* CR-someday: We don't save the file with [fun_name] in the filename
       because there is an appended stamp that is fragile and is annoying when
       testing. Currently it's not a problem because we abort the build whenever
       register allocation fails but if there was a fallback mode then the
       interesting files would be instantly overwritten. *)
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
  if Cfg_regalloc_utils.validator_debug
  then
    (* CR-someday: We don't save the file with [fun_name] in the filename
       because there is an appended stamp that is fragile and is annoying when
       testing. Currently it's not a problem because we abort the build whenever
       register allocation fails but if there was a fallback mode then the
       interesting files would be instantly overwritten. *)
    save_as_dot_with_equations ~desc ~res_instr ~res_block ~filename:"annot.dot"
      cfg "after_allocation_after_validation";
  let result =
    let cfg = Cfg_with_layout.cfg cfg in
    let entry_block = Cfg.entry_label cfg |> Cfg.get_block_exn cfg in
    let entry_id = Cfg_regalloc_utils.first_instruction_id entry_block in
    Cfg_dataflow.Instr.Tbl.find res_instr entry_id
  in
  match Domain.to_result result with
  | Ok equations ->
    verify_entrypoint equations cfg
    |> Result.map_error (fun source : Error.t ->
           { source; res_instr; res_block; desc; cfg })
  | Error error ->
    Error { source = At_instruction error; res_instr; res_block; desc; cfg }

let run desc cfg =
  match test desc cfg with
  | Ok cfg -> cfg
  | Error error -> Cfg_regalloc_utils.fatal "%a%!" Error.dump error
