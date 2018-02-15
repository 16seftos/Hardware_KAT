Require Import Extractions.
Require Import syntax lang Integers.
Open Scope hdl_type_scope.
Open Scope hdl_exp_scope.
Open Scope hdl_stmt_scope.

Definition m : interp_ty (tarr 16<<<tvec32>>>).
  refine (arr_init _ _).
  apply (Int.repr 0).
  intros.
  inversion H.
  apply (Int.repr (Z_of_nat' n)).
  apply (Int.repr (Z_of_nat' n)).
  Defined.

Definition loop : prog.
  (* refine (@ADecl Output 64 TVec32 "w" _ ). *)
  refine (@ADecl Input 16 TVec32 "m" _).
  refine (Output vec "x" ::== Int.repr 0;;; _).
  refine (iter 0 16 (fun i => _ )).
  refine (SAssign Blocking "x" _ ).
  refine ((EBinop OAdd (EVar "x") _)).
  refine (EDeref _ _).
  exact i.
  apply ("m").
Defined.

Definition loop_print_tb : verilog :=
  pretty_print_tb_results "looper" "380" loop.
(* Definition loop_print : verilog :=  *)
(*   pretty_print "looper" loop. *)

Extract Constant main => "Prelude.putStrLn loop_print_tb".

Extraction "looper.hs" loop_print_tb main.
