Require Import Extractions sha256.
(* print the sha256 program *)
Definition sha256_print_tb32 :=
  pretty_print_tb "sha256_mult32" sha256_mult32.

Definition sha256_print_tb24 :=
  pretty_print_tb "sha256_mult24" sha256_mult24.

Extract Constant main => "Prelude.putStrLn sha256_print_tb32".

(* run the program 'sha256.hs' and pipe to a file to get verilog *)
Extraction "sha256_32.hs" sha256_print_tb32 main.

Extract Constant main => "Prelude.putStrLn sha256_print_tb24".

Extraction "sha256_24.hs" sha256_print_tb24 main.
