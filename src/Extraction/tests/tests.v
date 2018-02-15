Require Import Extractions.
Require Import syntax lang Integers.
Open Scope hdl_type_scope.
Open Scope hdl_exp_scope.
Open Scope hdl_stmt_scope.

Definition shiftsAndBitStuff : prog :=
  Local vec "h0" ::== Int.repr 100;;;
        Input vec "sdf" ::== Int.zero;;;
        Output vec "s" ::== Int.zero;;;
        "h0" <= (EVar "h0") rightshift (EVal (Int.repr 3));;;
       "s" <= (EVar "h0") rightrotate (EVal (Int.repr 3));;;
       "s" <= (EVar "h0") and (EVar "s");;;
       "s" <= (EVar "h0") xor (EVar "s");;;
       "s" <= (EVar "h0") plus (EVar "s");;;
       "s" <= not (EVar "s");;;
       "s" ::= not (EVal Int.zero);;;
        done.

Definition print_shifts : verilog :=
  pretty_print_tb_results "shiftsAndBitStuff" "Some shifts" shiftsAndBitStuff.
(* Definition loop_print : verilog :=  *)
(*   pretty_print "looper" loop. *)

Extract Constant main => "Prelude.putStrLn print_shifts".

Extraction "shifts.hs" print_shifts main.


Program Definition array : prog :=
  Input arr "w" <<<(tarr 64 <<<tvec32>>>), 64>>>;;;
  Output arr "m" <<<(tarr 64 <<<tvec32>>>), 64>>>;;;
  iter 0 64 (fun i => "m"@'i <- "w"[[i]]);;;
  done.                                             
Next Obligation.    
apply 64.
Defined.
Next Obligation.
  unfold array_obligation_1.
  destruct (Fin.to_nat i).
  auto.
Defined.
Definition print_array : verilog :=
  pretty_print_tb "array" array.

Extract Constant main => "Prelude.putStrLn print_array".

Extraction "array.hs" print_array main.

