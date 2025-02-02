(* TEST

include dynlink
libraries = ""
files = "sheep.mli sheep.ml pig.mli"
set plugin1 = "${test_source_directory}/plugin1"
set plugin2 = "${test_source_directory}/plugin2"
set plugin2_build = "${test_build_directory}/plugin2"
set plugin2b = "${test_source_directory}/plugin2b"
set plugin2c = "${test_source_directory}/plugin2c"
set plugin3 = "${test_source_directory}/plugin3"
set plugin4 = "${test_source_directory}/plugin4"
set plugin5 = "${test_source_directory}/plugin5"
set plugin6 = "${test_source_directory}/plugin6"

* shared-libraries
** setup-ocamlc.byte-build-env
*** ocamlc.byte
module = "sheep.mli"
**** ocamlc.byte
module = "sheep.ml"
***** ocamlc.byte
module = "pig.mli"
****** ocamlc.byte
module = "test.ml"
*** script
script = "mkdir plugin1 plugin2 plugin2b plugin2c plugin3 plugin4 plugin5 plugin6"
**** script
script = "cp ${plugin1}/sheep.mli ${plugin1}/sheep.ml plugin1"
**** script
script = "cp ${plugin2}/cow.mli ${plugin2}/cow.ml plugin2"
**** script
script = "cp ${plugin2b}/cow.mli ${plugin2b}/cow.ml plugin2b"
**** script
script = "cp ${plugin2c}/cow.mli ${plugin2c}/cow.ml plugin2c"
**** script
script = "cp ${plugin3}/pig.mli ${plugin3}/pig.ml plugin3"
**** script
script = "cp ${plugin4}/chicken.mli ${plugin4}/chicken.ml plugin4"
**** script
script = "cp ${plugin5}/chicken.mli ${plugin5}/chicken.ml plugin5"
**** script
script = "cp ${plugin6}/pheasant.mli ${plugin6}/pheasant.ml ${plugin6}/partridge.mli ${plugin6}/partridge.ml plugin6"
***** ocamlc.byte
module = "plugin1/sheep.mli"
***** ocamlc.byte
flags = "-I plugin1"
module = "plugin1/sheep.ml"
***** ocamlc.byte
module = "plugin2/cow.mli"
***** ocamlc.byte
flags = "-I plugin2"
module = "plugin2/cow.ml"
***** ocamlc.byte
module = "plugin2b/cow.mli"
***** ocamlc.byte
flags = "-I plugin2b"
module = "plugin2b/cow.ml"
***** ocamlc.byte
module = "plugin2c/cow.mli"
***** ocamlc.byte
flags = "-I plugin2c"
module = "plugin2c/cow.ml"
***** ocamlc.byte
module = "plugin3/pig.mli"
***** ocamlc.byte
flags = "-I plugin3"
module = "plugin3/pig.ml"
***** ocamlc.byte
module = "plugin4/chicken.mli"
***** ocamlc.byte
flags = "-I plugin4"
module = "plugin4/chicken.ml"
***** ocamlc.byte
module = "plugin5/chicken.mli"
***** ocamlc.byte
flags = "-I plugin5"
module = "plugin5/chicken.ml"
***** ocamlc.byte
module = "plugin6/pheasant.mli"
***** ocamlc.byte
flags = "-I plugin6"
module = "plugin6/pheasant.ml"
***** ocamlc.byte
module = "plugin6/partridge.mli"
***** ocamlc.byte
flags = "-I plugin6"
module = "plugin6/partridge.ml"
***** ocamlc.byte
program = "${test_build_directory}/test.byte"
libraries = "dynlink"
all_modules = "sheep.cmo test.cmo"
****** script
script = "cp ${plugin2_build}/cow.cmo ${plugin2_build}/cow_copy.cmo"
******* run

** native-dynlink
*** setup-ocamlopt.byte-build-env
**** ocamlopt.byte
module = "sheep.mli"
***** ocamlopt.byte
module = "sheep.ml"
****** ocamlopt.byte
module = "pig.mli"
******* ocamlopt.byte
module = "test.ml"
**** script
script = "mkdir plugin1 plugin2 plugin2b plugin2c plugin3 plugin4 plugin5 plugin6"
***** script
script = "cp ${plugin1}/sheep.mli ${plugin1}/sheep.ml plugin1"
***** script
script = "cp ${plugin2}/cow.mli ${plugin2}/cow.ml plugin2"
***** script
script = "cp ${plugin2b}/cow.mli ${plugin2b}/cow.ml plugin2b"
***** script
script = "cp ${plugin2c}/cow.mli ${plugin2c}/cow.ml plugin2c"
***** script
script = "cp ${plugin3}/pig.mli ${plugin3}/pig.ml plugin3"
***** script
script = "cp ${plugin4}/chicken.mli ${plugin4}/chicken.ml plugin4"
***** script
script = "cp ${plugin5}/chicken.mli ${plugin5}/chicken.ml plugin5"
***** script
script = "cp ${plugin6}/pheasant.mli ${plugin6}/pheasant.ml ${plugin6}/partridge.mli ${plugin6}/partridge.ml plugin6"
****** ocamlopt.byte
module = "plugin1/sheep.mli"
****** ocamlopt.byte
program = "plugin1/sheep.cmxs"
flags = "-I plugin1 -shared"
all_modules = "plugin1/sheep.ml"
****** ocamlopt.byte
module = "plugin2/cow.mli"
****** ocamlopt.byte
program = "plugin2/cow.cmxs"
flags = "-I plugin2 -shared"
all_modules = "plugin2/cow.ml"
****** ocamlopt.byte
module = "plugin2b/cow.mli"
****** ocamlopt.byte
program = "plugin2b/cow.cmxs"
flags = "-I plugin2b -shared"
all_modules = "plugin2b/cow.ml"
****** ocamlopt.byte
module = "plugin2c/cow.mli"
****** ocamlopt.byte
program = "plugin2c/cow.cmxs"
flags = "-I plugin2c -shared"
all_modules = "plugin2c/cow.ml"
****** ocamlopt.byte
module = "plugin3/pig.mli"
****** ocamlopt.byte
program = "plugin3/pig.cmxs"
flags = "-I plugin3 -shared"
all_modules = "plugin3/pig.ml"
****** ocamlopt.byte
module = "plugin4/chicken.mli"
****** ocamlopt.byte
program = "plugin4/chicken.cmxs"
flags = "-I plugin4 -shared"
all_modules = "plugin4/chicken.ml"
****** ocamlopt.byte
module = "plugin5/chicken.mli"
****** ocamlopt.byte
program = "plugin5/chicken.cmxs"
flags = "-I plugin5 -shared"
all_modules = "plugin5/chicken.ml"
****** ocamlopt.byte
module = "plugin6/pheasant.mli"
****** ocamlopt.byte
program = "plugin6/pheasant.cmxs"
flags = "-I plugin6 -shared"
all_modules = "plugin6/pheasant.ml"
****** ocamlopt.byte
module = "plugin6/partridge.mli"
****** ocamlopt.byte
program = "plugin6/partridge.cmxs"
flags = "-I plugin6 -shared"
all_modules = "plugin6/partridge.ml"
****** ocamlopt.byte
program = "${test_build_directory}/test.exe"
libraries = "dynlink"
all_modules = "sheep.cmx test.cmx"
******* script
script = "cp ${plugin2_build}/cow.cmxs ${plugin2_build}/cow_copy.cmxs"
******** run
*)

let () = Sheep.baa Sheep.s (* Use Sheep module *)
let _ = fun (x : Pig.t) -> x (* Reference Pig module *)

(* Test that a privately loaded module cannot have the same name as a
   module in the program. *)
let test_sheep () =
  match
    if Dynlink.is_native then
      Dynlink.loadfile_private "plugin1/sheep.cmxs"
    else
      Dynlink.loadfile_private "plugin1/sheep.cmo"
  with
  | () -> assert false
  | exception Dynlink.Error (
      Dynlink.Module_already_loaded "Sheep") -> ()

(* Test repeated loading of a privately-loaded module from the same .cmxs
   file.  This is forbidden in native code. *)
let test_cow_repeated () =
  if Dynlink.is_native then begin
    let load () = Dynlink.loadfile_private "plugin2/cow.cmxs" in
    begin try load () with _ -> assert false end;
    match load () with
    | () -> assert false
    | exception Dynlink.Error (
        Dynlink.Library_file_already_loaded_privately _) -> ()
  end

(* Test repeated loading of the same privately-loaded module from two
   different .cmo / .cmxs files.  This is similar to the previous case, but is
   ok, because we're not trying to load the same .cmxs file twice. *)
let test_cow_repeated_different_cmxs () =
  try
    (* Note that [Cow] is already loaded from the previous test. *)
    if Dynlink.is_native then
      Dynlink.loadfile_private "plugin2/cow_copy.cmxs"
    else
      Dynlink.loadfile_private "plugin2/cow_copy.cmo"
  with _ -> assert false

(* Test that a privately loaded module can have the same name as a
   previous privately loaded module, in the case where the interfaces are
   the same, but the implementations differ. *)
let test_cow_same_name_same_mli () =
  if Dynlink.is_native then
    Dynlink.loadfile_private "plugin2b/cow.cmxs"
  else
    Dynlink.loadfile_private "plugin2b/cow.cmo"

(* Test that a privately loaded module can have the same name as a
   previous privately loaded module, in the case where neither the interfaces
   nor the implementations are the same. *)
let test_cow_same_name_different_mli () =
  if Dynlink.is_native then
    Dynlink.loadfile_private "plugin2c/cow.cmxs"
  else
    Dynlink.loadfile_private "plugin2c/cow.cmo"

(* Test that a privately loaded module cannot have the same name as an
   interface depended on by modules the program. *)
let test_pig () =
  match
    if Dynlink.is_native then
      Dynlink.loadfile_private "plugin3/pig.cmxs"
    else
      Dynlink.loadfile_private "plugin3/pig.cmo"
  with
  | () -> assert false
  | exception Dynlink.Error (
      Dynlink.Private_library_cannot_implement_interface "Pig") -> ()

(* Test that a privately loaded module can recursively load a module of
   the same name. *)
let test_chicken () =
  if Dynlink.is_native then
    Dynlink.loadfile_private "plugin4/chicken.cmxs"
  else
    Dynlink.loadfile_private "plugin4/chicken.cmo"

(* Test that a public load of a module M inside a privately-loaded module,
   followed by a public load of M, causes an error. *)
let test_pheasant () =
  begin
    if Dynlink.is_native then
      Dynlink.loadfile_private "plugin6/pheasant.cmxs"
    else
      Dynlink.loadfile_private "plugin6/pheasant.cmo"
  end;
  match
    if Dynlink.is_native then
      Dynlink.loadfile "plugin6/partridge.cmxs"
    else
      Dynlink.loadfile "plugin6/partridge.cmo"
  with
  | () -> assert false
  | exception Dynlink.Error (
      Dynlink.Module_already_loaded "Partridge") -> ()

let () =
  test_sheep ();
  test_cow_repeated ();
  test_cow_repeated_different_cmxs ();
  test_cow_same_name_same_mli ();
  test_cow_same_name_different_mli ();
  test_pig ();
  test_chicken ();
  test_pheasant ()
