open Cfg_intf.S

module Instruction = struct
  type 'a t =
    { mutable desc : 'a;
      mutable arg : Reg.t array;
      mutable res : Reg.t array;
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
      mutable body : Basic.t list;
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
    ({ fun_args = [| Proc.phys_reg 0 |];
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

exception Break_test

let check before after ~exp_std ~exp_err =
  let with_wrap_ppf ppf f =
    Format.pp_print_flush ppf ();
    let buf = Buffer.create 0 in
    let ppf_buf = Format.formatter_of_buffer buf in
    let old_out_func = Format.pp_get_formatter_out_functions ppf () in
    Format.pp_set_formatter_out_functions ppf
      (Format.pp_get_formatter_out_functions ppf_buf ());
    let res = f () in
    Format.pp_print_flush ppf ();
    Format.pp_set_formatter_out_functions ppf old_out_func;
    res, buf |> Buffer.to_bytes |> Bytes.to_string |> String.trim
  in
  let ((), err_out), std_out =
    with_wrap_ppf Format.std_formatter (fun () ->
        with_wrap_ppf Format.err_formatter (fun () ->
            try
              let desc =
                try Cfg_regalloc_validate.Description.create before
                with Misc.Fatal_error ->
                  Format.printf
                    "fatal exception raised when creating description";
                  raise Break_test
              in
              let res =
                try Cfg_regalloc_validate.verify desc after
                with Misc.Fatal_error ->
                  Format.printf
                    "fatal exception raised when validating description";
                  raise Break_test
              in
              match res with
              | Ok cfg ->
                if cfg = after
                then ()
                else Format.printf "Validation changed cfg"
              | Error error ->
                Format.printf "Validation failed: %a"
                  Cfg_regalloc_validate.Error.print error
            with Break_test -> ()))
  in
  if exp_std = std_out && exp_err = err_out
  then Format.printf "Test successful\n%!"
  else
    let print_as_text msg text =
      Format.printf "@?@[<h 2>%s:" msg;
      if String.length text > 0 then Format.force_newline ();
      Format.pp_print_text Format.std_formatter text;
      Format.printf "@]\n";
      ()
    in
    Format.printf "Test failed\n";
    print_as_text "Expected std" exp_std;
    print_as_text "Got std" std_out;
    print_as_text "Expected err" exp_err;
    print_as_text "Got err" err_out;
    Format.printf "Std as string literal:\n%S\n" std_out;
    Format.printf "Err as string literal:\n%S\n" err_out;
    Format.print_flush ();
    exit 1

let ( .&() ) (cfg : Cfg_desc.t) (label : Label.t) : Block.t =
  List.find (fun (block : Block.t) -> block.start = label) cfg.blocks

let ( .!() ) (block : Block.t) (index : int) : Basic.t =
  List.nth block.body index

let () =
  let cfg =
    ({ fun_args = [| Proc.phys_reg 0 |];
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
  check cfg cfg ~exp_std:"" ~exp_err:""

let () =
  let cfg =
    ({ fun_args = [||];
       blocks =
         [ { start = entry_label;
             body = [{ id = 1; desc = Prologue; arg = [||]; res = [||] }];
             exn = None;
             terminator =
               { id = 1; desc = Return; arg = [| Reg.create Int |]; res = [||] }
           } ];
       fun_contains_calls = false
     }
      : Cfg_desc.t)
    |> Cfg_desc.make
  in
  check cfg cfg ~exp_std:"fatal exception raised when creating description"
    ~exp_err:
      ">> Fatal error: Duplicate instruction no. 1 while creating \
       pre-allocation description"

let () =
  let cfg =
    ({ fun_args = [||];
       blocks =
         [ { start = entry_label;
             body = [{ id = 1; desc = Op Spill; arg = [||]; res = [||] }];
             exn = None;
             terminator =
               { id = 2; desc = Return; arg = [| Reg.create Int |]; res = [||] }
           } ];
       fun_contains_calls = false
     }
      : Cfg_desc.t)
    |> Cfg_desc.make
  in
  check cfg cfg ~exp_std:"fatal exception raised when creating description"
    ~exp_err:
      ">> Fatal error: Instruction no. 1 is specific to the regalloc phase \
       while creating pre-allocation description"

let () =
  let cfg =
    ({ fun_args = [||];
       blocks =
         [ { start = entry_label;
             body = [{ id = 1; desc = Op Reload; arg = [||]; res = [||] }];
             exn = None;
             terminator =
               { id = 2; desc = Return; arg = [| Reg.create Int |]; res = [||] }
           } ];
       fun_contains_calls = false
     }
      : Cfg_desc.t)
    |> Cfg_desc.make
  in
  check cfg cfg ~exp_std:"fatal exception raised when creating description"
    ~exp_err:
      ">> Fatal error: Instruction no. 1 is specific to the regalloc phase \
       while creating pre-allocation description"

let call_label = entry_label + 1

let return_label = entry_label + 2

let base_templ =
  let make_id =
    let last_id = ref 2 in
    fun () ->
      last_id := !last_id + 1;
      !last_id
  in
  let res_regs = Proc.loc_results [| Int |] in
  ({ fun_args = [||];
     blocks =
       [ { start = entry_label;
           body = [{ id = make_id (); desc = Prologue; arg = [||]; res = [||] }];
           exn = None;
           terminator =
             { id = make_id ();
               desc = Always call_label;
               arg = [||];
               res = [||]
             }
         };
         { start = call_label;
           body =
             [ { id = make_id ();
                 desc = Call (F Indirect);
                 arg = [||];
                 res = [||]
               } ];
           exn = None;
           terminator =
             { id = make_id ();
               desc = Always return_label;
               arg = [||];
               res = [||]
             }
         };
         { start = return_label;
           body = [];
           exn = None;
           terminator =
             { id = make_id (); desc = Return; arg = res_regs; res = [||] }
         } ];
     fun_contains_calls = true
   }
    : Cfg_desc.t)

let () =
  let templ =
    ({ fun_args = [||];
       blocks =
         [ { start = entry_label;
             body =
               [{ id = 1; desc = Call (F Indirect); arg = [||]; res = [||] }];
             exn = None;
             terminator =
               { id = 2; desc = Return; arg = [| Reg.create Int |]; res = [||] }
           } ];
       fun_contains_calls = true
     }
      : Cfg_desc.t)
  in
  let cfg1 = Cfg_desc.make templ in
  templ.&(entry_label).!(0).arg <- [| Reg.create Int |];
  let cfg2 = Cfg_desc.make templ in
  check cfg1 cfg2 ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: The instruction's no. 1 argument count has changed. \
       Now: 1. After: 0."

let () =
  let cfg =
    ({ fun_args = [||];
       blocks =
         [ { start = entry_label;
             body = [];
             exn = None;
             terminator =
               { id = 1; desc = Return; arg = [| Reg.create Int |]; res = [||] }
           } ];
       fun_contains_calls = false
     }
      : Cfg_desc.t)
    |> Cfg_desc.make
  in
  check cfg cfg ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: The instruction's no. 1 argument is still unknown after \
       allocation"
