Require Import Extractions lang syntax Integers.

Definition rotate10 : prog.
  refine (VDecl Input "w" (Int.repr 12) _).
  refine (VDecl Local "r" (Int.repr 4) _).
  refine (VDecl Output "b" (Int.repr 0) _).
  refine (PSeq (SAssign Blocking "b" (r_rotate (evar "w") (evar "r"))) _).
  apply PDone.
  Defined.
                     
Definition rotate_print_tb :=
  pretty_print_tb "rotate" rotate10.

Extract Constant main => "Prelude.putStrLn rotate_print_tb".

(* run the program 'sha.hs' and pipe to a file to get verilog *)
Extraction "rotate.hs" rotate_print_tb main.
