open Cfg_intf.S

module Instruction = struct
  type 'a t =
    { mutable desc : 'a;
      mutable arg : Reg.t array;
      mutable res : Reg.t array;
      mutable id : int
    }

  let make ~remove_locs ({ desc; arg; res; id } : 'a t) : 'a instruction =
    let map_regs arr =
      Array.map
        (fun (r : Reg.t) ->
          { r with
            loc =
              (if remove_locs && not (Reg.is_phys r) then Unknown else r.loc)
          })
        arr
    in
    { desc;
      arg = map_regs arg;
      res = map_regs res;
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

  let make ~remove_locs (t : t) : basic instruction =
    Instruction.make ~remove_locs t
end

module Terminator = struct
  type t = terminator Instruction.t

  let make ~remove_locs (t : t) : terminator instruction =
    Instruction.make ~remove_locs t
end

module Block = struct
  type t =
    { start : Label.t;
      mutable body : Basic.t list;
      terminator : Terminator.t;
      exn : Label.t option
    }

  let make ~remove_regalloc ~remove_locs ({ start; body; terminator; exn } : t)
      : Cfg.basic_block =
    let body =
      List.map (Basic.make ~remove_locs) body
      |> List.filter (function
           | { desc = Op (Spill | Reload); _ } -> not remove_regalloc
           | _ -> true)
    in
    let terminator = Terminator.make ~remove_locs terminator in
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

  let make ~remove_regalloc ~remove_locs
      ({ fun_args; blocks; fun_contains_calls } : t) : Cfg_with_layout.t =
    let cfg =
      Cfg.create ~fun_name:"foo" ~fun_args ~fun_dbg:[] ~fun_fast:false
        ~fun_contains_calls
        ~fun_num_stack_slots:(Array.make Proc.num_register_classes 0)
    in
    List.iter
      (fun (block : Block.t) ->
        Label.Tbl.add cfg.blocks block.start
          (Block.make ~remove_regalloc ~remove_locs block))
      blocks;
    Label.Tbl.iter
      (fun _ (block : Cfg.basic_block) ->
        Cfg.successor_labels ~normal:true ~exn:false block
        |> Label.Set.iter (fun suc ->
               let suc = Label.Tbl.find cfg.blocks suc in
               suc.predecessors <- Label.Set.add block.start suc.predecessors);
        Cfg.successor_labels ~normal:false ~exn:true block
        |> Label.Set.iter (fun suc ->
               let suc = Label.Tbl.find cfg.blocks suc in
               suc.predecessors <- Label.Set.add block.start suc.predecessors;
               suc.is_trap_handler <- true))
      cfg.blocks;
    let cfg_layout =
      Cfg_with_layout.create ~layout:[] ~preserve_orig_labels:true
        ~new_labels:Label.Set.empty cfg
    in
    (if not remove_locs
    then
      (* If we leave in the locations we want to have the actual stack slot
         count. *)
      let update_stack_slots i =
        let update_slot (r : Reg.t) =
          match r.loc, Proc.register_class r with
          | Stack (Local idx), reg_class ->
            cfg.fun_num_stack_slots.(reg_class)
              <- max cfg.fun_num_stack_slots.(reg_class) (idx + 1)
          | _ -> ()
        in
        Array.iter update_slot i.arg;
        Array.iter update_slot i.res
      in
      Cfg_with_layout.iter_instructions ~instruction:update_stack_slots
        ~terminator:update_stack_slots cfg_layout);
    cfg_layout

  let make_pre t = make ~remove_regalloc:true ~remove_locs:true t

  let make_post t = make ~remove_regalloc:false ~remove_locs:false t
end

let entry_label =
  Cfg_desc.make_post
    { fun_args = [||]; blocks = []; fun_contains_calls = false }
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
    |> Cfg_desc.make_post
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

let move_param_label = entry_label + 1

let call_label = entry_label + 2

let move_tmp_res_label = entry_label + 3

let add_label = entry_label + 4

let return_label = entry_label + 5

let new_label i = entry_label + 6 + i

let int = Array.init 8 (fun _ -> Reg.create Int)

let val_ = Array.init 8 (fun _ -> Reg.create Val)

let addr = Array.init 8 (fun _ -> Reg.create Addr)

let float = Array.init 8 (fun _ -> Reg.create Float)

let base_templ () : Cfg_desc.t * (unit -> int) =
  let make_id =
    let last_id = ref 2 in
    fun () ->
      last_id := !last_id + 1;
      !last_id
  in
  let make_locs regs f =
    let locs = f (Array.map (fun (r : Reg.t) -> r.typ) regs) in

    let regs =
      Array.map2
        (fun (reg : Reg.t) (loc : Reg.t) -> { reg with loc = loc.loc })
        regs locs
    in
    regs, locs
  in
  (* This is one possible representation of code:

     [fun f x y a -> let y = f x y a in let x = x + y in x] *)
  let int_arg1 = int.(0) in
  let int_arg2 = int.(1) in
  let stack_loc = Reg.at_location int_arg1.typ (Stack (Local 0)) in
  let args, arg_locs =
    make_locs [| val_.(0); int_arg1; int_arg2; float.(0) |] Proc.loc_parameters
  in
  let int_arg1 = args.(1) in
  let int_arg2 = args.(2) in
  let tmp_results, tmp_result_locs = make_locs [| int.(2) |] Proc.loc_results in
  let results, result_locs = make_locs [| int.(3) |] Proc.loc_results in
  let make_moves src dst =
    Array.map2
      (fun src dst : Basic.t ->
        { id = make_id (); desc = Op Move; arg = [| src |]; res = [| dst |] })
      src dst
    |> Array.to_list
  in
  ( { fun_args = arg_locs;
      blocks =
        [ { start = entry_label;
            body = [{ id = make_id (); desc = Prologue; arg = [||]; res = [||] }];
            exn = None;
            terminator =
              { id = make_id ();
                desc = Always move_param_label;
                arg = [||];
                res = [||]
              }
          };
          { start = move_param_label;
            body =
              make_moves arg_locs args
              @ [ { Instruction.id = make_id ();
                    desc = Op Spill;
                    arg = [| int_arg1 |];
                    res = [| stack_loc |]
                  } ]
              @ make_moves args arg_locs;
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
                  arg = arg_locs;
                  res = tmp_result_locs
                } ];
            exn = None;
            terminator =
              { id = make_id ();
                desc = Always move_tmp_res_label;
                arg = [||];
                res = [||]
              }
          };
          { start = move_tmp_res_label;
            body =
              make_moves tmp_result_locs tmp_results
              @ make_moves tmp_results [| int_arg2 |]
              @ [ { Instruction.id = make_id ();
                    desc = Op Reload;
                    arg = [| stack_loc |];
                    res = [| int_arg1 |]
                  } ];
            exn = None;
            terminator =
              { id = make_id ();
                desc = Always add_label;
                arg = [||];
                res = [||]
              }
          };
          { start = move_tmp_res_label;
            body =
              make_moves tmp_result_locs tmp_results
              @ make_moves tmp_results [| int_arg2 |]
              @ [ { Instruction.id = make_id ();
                    desc = Op Reload;
                    arg = [| stack_loc |];
                    res = [| int_arg1 |]
                  } ];
            exn = None;
            terminator =
              { id = make_id ();
                desc = Always add_label;
                arg = [||];
                res = [||]
              }
          };
          { start = add_label;
            body =
              [ { Instruction.id = make_id ();
                  desc = Op (Intop Mach.Iadd);
                  arg = [| int_arg1; int_arg2 |];
                  res = [| int_arg1 |]
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
            body =
              make_moves [| int_arg1 |] results
              @ make_moves results result_locs
              @ [ { id = make_id ();
                    desc = Reloadretaddr;
                    arg = [||];
                    res = [||]
                  } ];
            exn = None;
            terminator =
              { id = make_id (); desc = Return; arg = result_locs; res = [||] }
          } ];
      fun_contains_calls = true
    },
    make_id )

let check name f ~exp_std ~exp_err =
  let before, after = f () in
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
  then Format.printf "%s: OK\n%!" name
  else
    let print_as_text msg text =
      Format.printf "@?@[<h 2>%s:" msg;
      if String.length text > 0 then Format.force_newline ();
      Format.pp_print_text Format.std_formatter text;
      Format.printf "@]\n";
      ()
    in
    Format.printf "%s: FAILED\n" name;
    print_as_text "Expected std" exp_std;
    print_as_text "Got std" std_out;
    print_as_text "Expected err" exp_err;
    print_as_text "Got err" err_out;
    Format.printf "Std as string literal:\n%S\n" std_out;
    Format.printf "Err as string literal:\n%S\n" err_out;
    Format.print_flush ();
    Cfg_with_layout.save_as_dot ~filename:"/tmp/before.dot" before
      "test-cfg-before";
    Cfg_with_layout.save_as_dot ~filename:"/tmp/after.dot" after
      "test-cfg-after";
    Format.printf "The failing cfgs were put in /tmp/[before|after].dot\n";
    Format.print_flush ();
    exit 1

let ( .&() ) (cfg : Cfg_desc.t) (label : Label.t) : Block.t =
  List.find (fun (block : Block.t) -> block.start = label) cfg.blocks

let ( .!() ) (block : Block.t) (index : int) : Basic.t =
  List.nth block.body index

(* let () = check "IRC works on base templ" (fun templ _ -> let cfg =
   Cfg_desc.make templ in cfg, Cfg_irc.run cfg) ~exp_std:"" ~exp_err:"" *)

let () =
  check "Duplicate instruction found when creating description"
    (fun () ->
      let templ, _ = base_templ () in
      let block = templ.&(add_label) in
      (* Duplicate the instruction. *)
      block.body <- List.hd block.body :: block.body;
      let cfg = Cfg_desc.make_pre templ in
      cfg, cfg)
    ~exp_std:"fatal exception raised when creating description"
    ~exp_err:
      ">> Fatal error: Duplicate instruction no. 8 while creating \
       pre-allocation description"

let () =
  check "Duplicate terminator found when creating description"
    (fun () ->
      let templ, _ = base_templ () in
      (* Change id of one terminator to the id of the other one. *)
      templ.&(add_label).terminator.id <- templ.&(call_label).terminator.id;
      let cfg = Cfg_desc.make_pre templ in
      cfg, cfg)
    ~exp_std:"fatal exception raised when creating description"
    ~exp_err:
      ">> Fatal error: Duplicate instruction no. 17 while creating \
       pre-allocation description"

let () =
  check "Regalloc specific instructions are checked when creating description"
    (fun () ->
      let templ, make_id = base_templ () in
      let cfg = Cfg_desc.make ~remove_regalloc:false ~remove_locs:true templ in
      cfg, cfg)
    ~exp_std:"fatal exception raised when creating description"
    ~exp_err:">> Fatal error: instruction 24 is a spill"

let () =
  check "Instruction argument count"
    (fun () ->
      let templ, make_id = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      templ.&(call_label).!(0).arg <- Array.sub templ.&(call_label).!(0).arg 0 1;
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: The instruction's no. 18 argument count has changed. \
       Before: 4. Now: 1."

let () =
  check "Instruction result count"
    (fun () ->
      let templ, make_id = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      templ.&(call_label).!(0).res <- [||];
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: The instruction's no. 18 result count has changed. \
       Before: 1. Now: 0."

let () =
  check "Terminator arugment count"
    (fun () ->
      let templ, make_id = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      templ.&(return_label).terminator.arg <- [||];
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: The instruction's no. 3 argument count has changed. \
       Before: 1. Now: 0."

let () =
  check "Location can't be unknown after allocation"
    (fun () ->
      let templ, make_id = base_templ () in
      let cfg = Cfg_desc.make_pre templ in
      cfg, cfg)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: instruction 25 has a register with an unknown location"

let () =
  check "Precoloring can't change"
    (fun () ->
      let templ, make_id = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      templ.&(move_param_label).!(7).res <- templ.&(move_param_label).!(6).res;
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: The instruction's no. 22 result has changed precolored \
       location from %rdi to %rbx"

let () =
  check "Duplicate instruction found when validating description"
    (fun () ->
      let templ, _ = base_templ () in
      (* The spill has the same id as reload instruction. *)
      templ.&(move_param_label).!(4).id <- templ.&(move_tmp_res_label).!(2).id;
      let cfg1 = Cfg_desc.make_pre templ in
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: Duplicate instruction no. 14 while checking \
       post-allocation description"

let () =
  check "Regalloc changed existing instruction into regalloc instruction"
    (fun () ->
      let templ, _ = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      templ.&(move_param_label).!(3).desc <- Op Spill;
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: Register allocation changed existing instruction no. 28 \
       into a register allocation specific instruction"

let () =
  check "Regalloc added non-regalloc specific instr"
    (fun () ->
      let templ, make_id = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      let block = templ.&(add_label) in
      let r = (List.hd block.body).res in
      block.body
        <- { desc = Op Move; id = make_id (); arg = r; res = r } :: block.body;
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: Register allocation added non-regalloc specific \
       instruction no. 31"

let () =
  check "Regalloc added a terminator and a block"
    (fun () ->
      let templ, make_id = base_templ () in
      (* The spill has the same id as another instruction. *)
      let cfg1 = Cfg_desc.make_pre templ in
      let templ =
        { templ with
          blocks =
            { start = new_label 1;
              exn = None;
              body = [];
              terminator =
                { desc = Always return_label;
                  res = [||];
                  arg = [||];
                  id = make_id ()
                }
            }
            :: templ.blocks
        }
      in
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: Register allocation added non-regalloc specific \
       instruction no. 31"

let () =
  check "Regalloc changed instruction desc"
    (fun () ->
      let templ, _ = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      templ.&(add_label).!(0).desc <- Op (Intop Isub);
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:">> Fatal error: The instruction's no. 8 desc was changed"

let () =
  check "Regalloc changed terminator desc"
    (fun () ->
      let templ, _ = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      templ.&(return_label).terminator.desc <- Raise Raise_regular;
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:">> Fatal error: The instruction's no. 3 desc was changed"

let () =
  check "Deleted instruction"
    (fun () ->
      let templ, _ = base_templ () in
      let cfg1 = Cfg_desc.make_pre templ in
      templ.&(add_label).body <- List.tl templ.&(add_label).body;
      let cfg2 = Cfg_desc.make_post templ in
      cfg1, cfg2)
    ~exp_std:"fatal exception raised when validating description"
    ~exp_err:
      ">> Fatal error: Instruction no. 8 was deleted by register allocator"
