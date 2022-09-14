[@@@ocaml.warning "+a-4-30-40-41-42"]

type domain =
  { before : Reg.Set.t;
    across : Reg.Set.t
  }

module Domain : Cfg_dataflow.Domain_S with type t = domain = struct
  type t = domain =
    { before : Reg.Set.t;
      across : Reg.Set.t
    }

  let bot = { before = Reg.Set.empty; across = Reg.Set.empty }

  let join { before = left_before; across = _ }
      { before = right_before; across = _ } =
    { before = Reg.Set.union left_before right_before; across = Reg.Set.empty }

  let less_equal { before = left_before; across = _ }
      { before = right_before; across = _ } =
    Reg.Set.subset left_before right_before

  let with_formatter ~f x =
    let buff = Buffer.create 64 in
    let fmt = Format.formatter_of_buffer buff in
    f fmt x;
    Format.pp_print_flush fmt ();
    Buffer.contents buff
end

type error = |

module Transfer :
  Cfg_dataflow.Backward_transfer
    with type domain = domain
     and type error = error = struct
  type nonrec domain = domain =
    { before : Reg.Set.t;
      across : Reg.Set.t
    }

  type nonrec error = error

  let basic :
      domain ->
      exn:domain ->
      Cfg.basic Cfg.instruction ->
      (domain, error) result =
   fun { before; across = _ } ~exn instr ->
    Result.ok
    @@
    match instr.desc with
    | Op _ | Call _ ->
      if Cfg.is_pure_basic instr.desc
         && Reg.disjoint_set_array before instr.res
         && (not (Proc.regs_are_volatile instr.arg))
         && not (Proc.regs_are_volatile instr.res)
      then { before; across = before }
      else
        let across = Reg.diff_set_array before instr.res in
        let across =
          if Cfg.can_raise_basic instr.desc && instr.stack_offset > 0
          then Reg.Set.union across exn.before
          else across
        in
        let before = Reg.add_set_array across instr.arg in
        { before; across }
    | Reloadretaddr ->
      { before = Reg.diff_set_array before Proc.destroyed_at_reloadretaddr;
        across = Reg.Set.empty
      }
    | Pushtrap _ -> { before; across = before }
    | Poptrap -> { before; across = before }
    | Prologue -> { before; across = before }

  let terminator :
      domain ->
      exn:domain ->
      Cfg.terminator Cfg.instruction ->
      (domain, error) result =
   fun { before; across = _ } ~exn instr ->
    Result.ok
    @@
    match instr.desc with
    | Never -> assert false
    | Always _ ->
      { before = Reg.add_set_array before instr.arg; across = before }
    | Parity_test _ ->
      { before = Reg.add_set_array before instr.arg; across = before }
    | Truth_test _ ->
      { before = Reg.add_set_array before instr.arg; across = before }
    | Float_test _ ->
      { before = Reg.add_set_array before instr.arg; across = before }
    | Int_test _ ->
      { before = Reg.add_set_array before instr.arg; across = before }
    | Switch _ ->
      { before = Reg.add_set_array before instr.arg; across = before }
    | Return -> { before = Reg.set_of_array instr.arg; across = Reg.Set.empty }
    | Tailcall (Self _) ->
      { before = Reg.set_of_array instr.arg; across = Reg.Set.empty }
    | Raise _ ->
      { before = Reg.add_set_array exn.before instr.arg; across = exn.before }
    | Tailcall (Func _) ->
      { before = Reg.set_of_array instr.arg; across = Reg.Set.empty }
    | Call_no_return _ ->
      { before = Reg.add_set_array exn.before instr.arg; across = exn.before }

  let exception_ : domain -> (domain, error) result =
   fun { before; across = _ } ->
    Result.ok
    @@ { before = Reg.Set.remove Proc.loc_exn_bucket before;
         across = Reg.Set.empty
       }
end

module Liveness = Cfg_dataflow.Backward (Domain) (Transfer)
