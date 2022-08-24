[@@@ocaml.warning "+a-4-30-40-41-42"]

type domain =
  { before : Reg.Set.t;
    across : Reg.Set.t
  }

module Domain : Cfg_dataflow.Backward_domain with type t = domain = struct
  type t = domain =
    { before : Reg.Set.t;
      across : Reg.Set.t
    }

  let bot = { before = Reg.Set.empty; across = Reg.Set.empty }

  let compare { before = left_before; across = _ }
      { before = right_before; across = _ } =
    Reg.Set.compare left_before right_before

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

  let to_string { before = regset; across = _ } =
    regset |> Reg.Set.elements
    |> ListLabels.map ~f:(with_formatter ~f:Printmach.reg)
    |> StringLabels.concat ~sep:", "
end

module Transfer : Cfg_dataflow.Backward_transfer with type domain = domain =
struct
  type nonrec domain = domain =
    { before : Reg.Set.t;
      across : Reg.Set.t
    }

  let instruction { before; across = _ } ~can_raise ~exn
      (instr : _ Cfg.instruction) =
    let across = Reg.diff_set_array before instr.res in
    let across =
      if can_raise then Reg.Set.union across exn.before else across
    in
    let before = Reg.add_set_array across instr.arg in
    { before; across }

  let basic : domain -> exn:domain -> Cfg.basic Cfg.instruction -> domain =
   fun domain ~exn instr ->
    instruction ~can_raise:(Cfg.can_raise_basic instr.desc) ~exn domain instr

  let terminator :
      domain -> exn:domain -> Cfg.terminator Cfg.instruction -> domain =
   fun domain ~exn instr ->
    instruction
      ~can_raise:(Cfg.can_raise_terminator instr.desc)
      ~exn domain instr

  let exception_ : domain -> domain =
   fun { before; across = _ } ->
    { before = Reg.Set.remove Proc.loc_exn_bucket before;
      across = Reg.Set.empty
    }
end

module Liveness = Cfg_dataflow.Backward (Domain) (Transfer)
