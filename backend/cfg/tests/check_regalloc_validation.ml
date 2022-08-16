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
  check cfg cfg Ok;
  ()
