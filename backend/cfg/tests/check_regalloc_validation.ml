open Cfg_intf.S

module Res = struct
  type t =
    | Exception_before of exn
    | Exception_after of exn
    | Ok
    | Validation_changed_cfg of
        { before : Cfg_with_layout.t;
          after : Cfg_with_layout.t
        }
    | Error of Cfg_regalloc_validate.Error.t

  let print (ppf : Format.formatter) (t : t) : unit =
    match t with
    | Exception_before exn ->
      Format.fprintf ppf "Exception when creating description: %s"
        (Printexc.to_string exn)
    | Exception_after exn ->
      Format.fprintf ppf "Exception while checking description: %s"
        (Printexc.to_string exn)
    | Ok -> Format.fprintf ppf "Validation passed"
    | Validation_changed_cfg _ -> Format.fprintf ppf "Validation changed cfg"
    | Error error ->
      Format.fprintf ppf "Validation failed: %a"
        Cfg_regalloc_validate.Error.print error
end

module Instruction = struct
  type 'a t =
    { desc : 'a;
      arg : Reg.t array;
      res : Reg.t array;
      id : int
    }

  let make ({ desc; arg; res; id } : 'a t) : 'a instruction =
    { desc;
      arg;
      res;
      id;
      dbg = [];
      fdo = None;
      irc_work_list = Unknown_list;
      live = Reg.Set.empty;
      stack_offset = 0
    }
end

module Basic = struct
  type t = basic Instruction.t

  let make (t : t) : basic instruction = Instruction.make t
end

module Terminator = struct
  type t = terminator Instruction.t

  let make (t : t) : terminator instruction = Instruction.make t
end

module Block = struct
  type t =
    { start : Label.t;
      body : Basic.t list;
      terminator : Terminator.t;
      exn : Label.t option
    }

  let make ({ start; body; terminator; exn } : t) : Cfg.basic_block =
    let body = List.map Basic.make body in
    let terminator = Terminator.make terminator in
    let can_raise =
      List.exists
        (fun (i : basic instruction) -> Cfg.can_raise_basic i.desc)
        body
      || Cfg.can_raise_terminator terminator.desc
    in
    { start;
      body;
      terminator;
      predecessors = Label.Set.empty;
      stack_offset = 0;
      exn;
      can_raise;
      is_trap_handler = false;
      dead = false
    }
end

module Cfg_desc = struct
  type t =
    { fun_args : Reg.t array;
      blocks : Block.t list;
      fun_contains_calls : bool
    }

  let make ({ fun_args; blocks; fun_contains_calls } : t) : Cfg_with_layout.t =
    let cfg =
      Cfg.create ~fun_name:"foo" ~fun_args ~fun_dbg:[] ~fun_fast:false
        ~fun_contains_calls
        ~fun_num_stack_slots:(Array.make Proc.num_register_classes 0)
    in
    List.iter
      (fun (block : Block.t) ->
        Label.Tbl.add cfg.blocks block.start (Block.make block))
      blocks;
    Cfg_with_layout.create ~layout:[] ~preserve_orig_labels:true
      ~new_labels:Label.Set.empty cfg
end

let entry_label =
  Cfg_desc.make { fun_args = [||]; blocks = []; fun_contains_calls = false }
  |> Cfg_with_layout.cfg |> Cfg.entry_label

let () =
  let made_cfg =
    ({ fun_args = [||];
       blocks =
         [ { start = entry_label;
             body = [];
             exn = None;
             terminator =
               { id = 1;
                 desc = Return;
                 arg = [| Proc.phys_reg 0 |];
                 res = [||]
               }
           } ];
       fun_contains_calls = false
     }
      : Cfg_desc.t)
    |> Cfg_desc.make
  in
  let cfg =
    Cfg.create ~fun_name:"foo"
      ~fun_args:[| Proc.phys_reg 0 |]
      ~fun_dbg:[] ~fun_fast:false ~fun_contains_calls:false
      ~fun_num_stack_slots:(Array.make Proc.num_register_classes 0)
  in
  Label.Tbl.add cfg.Cfg.blocks (Cfg.entry_label cfg)
    { start = Cfg.entry_label cfg;
      body = [];
      exn = None;
      can_raise = false;
      is_trap_handler = false;
      predecessors = Label.Set.empty;
      stack_offset = 0;
      dead = false;
      terminator =
        { desc = Return;
          arg = [| Proc.phys_reg 0 |];
          res = [||];
          dbg = [];
          fdo = None;
          stack_offset = 0;
          id = 1;
          live = Reg.Set.empty;
          irc_work_list = Unknown_list
        }
    };
  let cfg =
    cfg
    |> Cfg_with_layout.create ~layout:[] ~preserve_orig_labels:true
         ~new_labels:Label.Set.empty
  in
  assert (made_cfg = cfg);
  ()

let check before after expected =
  let res : Res.t =
    try
      let desc = Cfg_regalloc_validate.Description.create before in
      try
        match Cfg_regalloc_validate.verify desc after with
        | Ok cfg ->
          if cfg = after
          then Ok
          else Validation_changed_cfg { before = after; after = cfg }
        | Error error -> Error error
      with exn -> Exception_after exn
    with exn -> Exception_before exn
  in
  if res = expected
  then Printf.printf "Test successful\n%!"
  else (
    Format.printf "Test failed\n";
    Format.printf "Expected: %a\n" Res.print expected;
    Format.printf "Got: %a\n" Res.print res;
    Format.print_flush ();
    exit 1)

let () =
  let cfg =
    ({ fun_args = [||];
       blocks =
         [ { start = entry_label;
             body = [];
             exn = None;
             terminator =
               { id = 1;
                 desc = Return;
                 arg = [| Proc.phys_reg 0 |];
                 res = [||]
               }
           } ];
       fun_contains_calls = false
     }
      : Cfg_desc.t)
    |> Cfg_desc.make
  in
  check cfg cfg Ok;
  ()
