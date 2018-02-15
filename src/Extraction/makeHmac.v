Require Import Extractions hmac.
Definition hmac_print :=
  pretty_print_tb "hmac" hmac.
Extract Constant main => "Prelude.putStrLn hmac_print".
Extraction "hmac.hs" hmac_print main.
