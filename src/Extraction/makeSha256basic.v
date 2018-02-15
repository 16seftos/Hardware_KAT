Require Import Extractions sha256.
(* print the sha256 basic program *)
Definition sha256_print_tb :=
  pretty_print_tb "sha256" sha256.

Extract Constant main => "Prelude.putStrLn sha256_print_tb".

(* run the program 'sha256.hs' and pipe to a file to get verilog *)
Extraction "sha256.hs" sha256_print_tb main.
