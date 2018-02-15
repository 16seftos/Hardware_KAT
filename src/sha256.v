Set Implicit Arguments.
Unset Strict Implicit.

Require Import List. Import ListNotations.
Require Import ZArith.
Require Import Extractions.
Require Import Integers.
Require Import String.
Require Import lang syntax.

Definition h0' := Int.repr 1779033703.
Definition h1' := Int.repr 3144134277.
Definition h2' := Int.repr 1013904242.
Definition h3' := Int.repr 2773480762.
Definition h4' := Int.repr 1359893119.
Definition h5' := Int.repr 2600822924.
Definition h6' := Int.repr 528734635.
Definition h7' := Int.repr 1541459225.

Definition k (n:nat) : bvec32 :=
  match n with
  | 0 => Int.repr 1116352408
  | 1 => Int.repr 1899447441
  | 2 => Int.repr 3049323471
  | 3 => Int.repr 3921009573
  | 4 => Int.repr 961987163
  | 5 => Int.repr 1508970993
  | 6 => Int.repr 2453635748
  | 7 => Int.repr 2870763221
  | 8 => Int.repr 3624381080
  | 9 => Int.repr 310598401
  | 10 => Int.repr 607225278
  | 11 => Int.repr 1426881987
  | 12 => Int.repr 1925078388
  | 13 => Int.repr 2162078206
  | 14 => Int.repr 2614888103
  | 15 => Int.repr 3248222580
  | 16 => Int.repr 3835390401
  | 17 => Int.repr 4022224774
  | 18 => Int.repr 264347078
  | 19 => Int.repr 604807628
  | 20 => Int.repr 770255983
  | 21 => Int.repr 1249150122
  | 22 => Int.repr 1555081692
  | 23 => Int.repr 1996064986
  | 24 => Int.repr 2554220882
  | 25 => Int.repr 2821834349
  | 26 => Int.repr 2952996808
  | 27 => Int.repr 3210313671
  | 28 => Int.repr 3336571891
  | 29 => Int.repr 3584528711
  | 30 => Int.repr 113926993
  | 31 => Int.repr 338241895
  | 32 => Int.repr 666307205
  | 33 => Int.repr 773529912
  | 34 => Int.repr 1294757372
  | 35 => Int.repr 1396182291
  | 36 => Int.repr 1695183700
  | 37 => Int.repr 1986661051
  | 38 => Int.repr 2177026350
  | 39 => Int.repr 2456956037
  | 40 => Int.repr 2730485921
  | 41 => Int.repr 2820302411
  | 42 => Int.repr 3259730800
  | 43 => Int.repr 3345764771
  | 44 => Int.repr 3516065817
  | 45 => Int.repr 3600352804
  | 46 => Int.repr 4094571909
  | 47 => Int.repr 275423344
  | 48 => Int.repr 430227734
  | 49 => Int.repr 506948616
  | 50 => Int.repr 659060556
  | 51 => Int.repr 883997877
  | 52 => Int.repr 958139571
  | 53 => Int.repr 1322822218
  | 54 => Int.repr 1537002063
  | 55 => Int.repr 1747873779
  | 56 => Int.repr 1955562222
  | 57 => Int.repr 2024104815
  | 58 => Int.repr 2227730452
  | 59 => Int.repr 2361852424
  | 60 => Int.repr 2428436474
  | 61 => Int.repr 2756734187
  | 62 => Int.repr 3204031479
  | 63 => Int.repr 3329325298
  | _ => Int.zero (*Shouldn't happen*)
  end.

Open Scope hdl_type_scope.
Open Scope hdl_exp_scope.
Open Scope hdl_stmt_scope.
Open Scope string_scope.

Lemma LessThanB: forall x y j : nat,
  (x < y -> x-j < y).
Proof. 
  intros; induction j; omega.
Qed.

Ltac LessBSolve i l :=
  unfold nat_of_fin;
  destruct (Fin.to_nat i); simpl;
  clear - l;
  apply LessThanB; apply l.

(* Calculate the number of zeroes needed for padding *)
Definition calc_zeroes
  (size : nat)
  : nat :=
  512 - Nat.modulo (size + 65) 512.

(* Calculate the number of chunks the message needs to be broken into *)
(* Will be useful if I implement "preprocessing on the fly" *)
Definition calc_chunks
  (size : nat)
  : nat :=
  (size + 64 + 512) / 512. (* Remember, division rounds down *)

Ltac solve_obligations :=
  match goal with
  | |- context[proj1_sig (Fin.to_nat ?i) < ?n] =>
    destruct (Fin.to_nat i); simpl; omega; auto
  | |- context[?i - _ < _] =>
    unfold nat_of_fin; simpl; apply LessThanB; solve_obligations
  | |- context[?i < _] => omega
  end; auto.                                            
Hint Extern 3 =>
 solve_obligations
: core.

Program Definition core
        (* inputs *)
        (n : nat)
        (w : id (tarr 64<<<tvec32>>>))
        (m : id (tarr n<<<tvec32>>>)) (* Originally, n = 16 *)
        (h0 h1 h2 h3 h4 h5 h6 h7 : id (tvec32))
        (* local variables *)
        (s0 s1 : id (tvec32))
        (s1 ch temp1 s0 maj temp2 : id (tvec32))
        (a b c d e f g h : id (tvec32))
        (* outputs *)
        (hash : id (tarr 8<<<tvec32>>>))  
  : prog :=

(* Initialize the values of h0 to h7 *)
h0 <= val h0';;;
h1 <= val h1';;;
h2 <= val h2';;;
h3 <= val h3';;;
h4 <= val h4';;;
h5 <= val h5';;;
h6 <= val h6';;;
h7 <= val h7';;;

(* Begin chunk loop *)
iter 0 (calc_chunks (n*32)) (fun j : iN (calc_chunks (n*32)) =>
                               
(* Copy chunk into first 16 words of w. *)
   iter 0 16 (fun i =>
     (match ((16*j+i) <? n) as H_eq with
      | true => w@'i <- m[[''(16*j+i)]]
      | false =>
        (match ((16*j+i) =? n) with
        | true => w@'i <- (EVal (Int.repr 1)) rightrotate (val 1%Z)
        | false => w@'i <- EVal Int.zero
         end)
      end))
    (* if((16*j+i) <? n) then w@'i <- m[[''(16*j+i)]] *)
    (* else (if((16*j+i) =? n) then w@'i <- (EVal (Int.repr 1)) rightrotate (val 1%Z) *)
    (* else w@'i <- EVal Int.zero)) *);;
                               
(* Make the preprocessed message end in n*32 *)
  iter 15 16 (fun i =>
    if(j+1 =? (calc_chunks (n*32))) then w@'i <- EVal (Int.repr (Z_of_nat (n*32)))
    else w@'i <- w[[i]]);;

(* Extend the first 16 words into the remaining 48 words w[16..63] of the message schedule array:
   for i from 16 to 63
     s0 := (w[i-15] rightrotate 7) xor (w[i-15] rightrotate 18) xor (w[i-15] rightshift 3)
     s1 := (w[i-2] rightrotate 17) xor (w[i-2] rightrotate 19) xor (w[i-2] rightshift 10)
     w[i] := w[i-16] + s0 + w[i-7] + s1 *)
  iter 16 64 (fun i : iN 64 =>
    "s0" <= (w[[''(i-15)]] rightrotate (val 7%Z)) xor (w[[''(i-15)]] rightrotate (val 18%Z)) xor
            (w[[''(i-15)]] rightshift (val 3%Z));;
    "s1" <= (w[[''(i-2)]] rightrotate (val 17%Z)) xor (w[[''(i-2)]] rightrotate (val 19%Z)) xor
            (w[[''(i-2)]] rightshift (val 10%Z));;
    w@i <- w[[''(i-16)]] plus (evar "s0") plus w[[''(i-7)]] plus (evar "s1")
  );;

(* Initialize working variables to current hash value:
    a := h0
    b := h1
    c := h2
    d := h3
    e := h4
    f := h5
    g := h6
    h := h7 *)
  a <= evar h0;;
  b <= evar h1;;
  c <= evar h2;;
  d <= evar h3;;
  e <= evar h4;;
  f <= evar h5;;
  g <= evar h6;;
  h <= evar h7;;

(* Compression function main loop:
    for i from 0 to 63
        s1 := (e rightrotate 6) xor (e rightrotate 11) xor (e rightrotate 25)
        ch := (e and f) xor ((not e) and g)
        temp1 := h + s1 + ch + k[i] + w[i]
        s0 := (a rightrotate 2) xor (a rightrotate 13) xor (a rightrotate 22)
        maj := (a and b) xor (a and c) xor (b and c)
        temp2 := s0 + maj
 
        h := g
        g := f
        f := e
        e := d + temp1
        d := c
        c := b
        b := a
        a := temp1 + temp2 *)
  iter 0 64 (fun i : iN 64 =>
    s1 <= (evar e rightrotate (val 6%Z)) xor (evar e rightrotate (val 11%Z)) xor
          (evar e rightrotate (val 25%Z));;
    ch <= (evar "e" and evar "f") xor (not (evar "e") and evar "g");;
    temp1 <= evar "h" plus evar "s1" plus evar "ch" plus val (k i) plus w[[i]];;
    s0 <= (evar "a" rightrotate (val 2%Z)) xor (evar "a" rightrotate (val 13%Z)) xor
          (evar "a" rightrotate (val 22%Z));;
    maj <= (evar "a" and evar "b") xor (evar "a" and evar "c") xor
           (evar "b" and evar "c");;
    temp2 <= (evar "s0") plus evar "maj";;

    h <= evar g;;
    g <= evar f;;
    f <= evar e;;
    e <= evar d plus evar temp1;;
    d <= evar c;;
    c <= evar b;;
    b <= evar a;;
    a <= evar temp1 plus evar temp2
  );;

(* Add the compressed chunk to the current hash value:
    h0 := h0 + a
    h1 := h1 + b
    h2 := h2 + c
    h3 := h3 + d
    h4 := h4 + e
    h5 := h5 + f
    h6 := h6 + g
    h7 := h7 + h *)
  h0 <= evar h0 plus evar a;;
  h1 <= evar h1 plus evar b;;                       
  h2 <= evar h2 plus evar c;;
  h3 <= evar h3 plus evar d;;                       
  h4 <= evar h4 plus evar e;;
  h5 <= evar h5 plus evar f;;                      
  h6 <= evar h6 plus evar g;;
  h7 <= evar h7 plus evar h

(* End chunk loop *)
);;;

(* Produce the final hash value (big-endian): *)
  hash@''0 <- evar h0;;; 
  hash@''1 <- evar h1;;;             
  hash@''2 <- evar h2;;; 
  hash@''3 <- evar h3;;;             
  hash@''4 <- evar h4;;; 
  hash@''5 <- evar h5;;;             
  hash@''6 <- evar h6;;; 
  hash@''7 <- evar h7;;;             
  done.
Next Obligation.
 rewrite <- Nat.ltb_lt.
 auto.
Defined.

Definition mm (n : nat) : id (tarr n<<<tvec32>>>).
  apply "mm".
Defined.

Program Definition sha256'
  (* inputs *)
  (w : id (tarr 64<<<tvec32>>>))
  (m : id (tarr 16<<<tvec32>>>))
  (* outputs *)
  (hash : id (tarr 8 <<<tvec32>>>))
  : prog := 

  (* Notation "i 'arr' x <<< t , N >>>" := (@ADecl i N t x) (at level 79). *)
  Local arr "ww" <<<(tarr 64<<<tvec32>>>), 64 >>>;;;
  Local arr "mm" <<<(tarr 16<<<tvec32>>>), 16 >>>;;;                       iter 0 64 (fun i =>
               "ww"@'i <- w[[i]]);;;
                                              
  iter 0 16 (fun i =>
               "mm"@'i <- m[[i]]);;;

  Local vec "h0" ::== Int.zero;;;
  Local vec "h1" ::== Int.zero;;;
  Local vec "h2" ::== Int.zero;;;      
  Local vec "h3" ::== Int.zero;;;      
  Local vec "h4" ::== Int.zero;;;
  Local vec "h5" ::== Int.zero;;;
  Local vec "h6" ::== Int.zero;;;      
  Local vec "h7" ::== Int.zero;;;      

  Local vec "s0" ::== Int.zero;;;
  Local vec "s1" ::== Int.zero;;;

  Local vec "s1" ::== Int.zero;;;
  Local vec "ch" ::== Int.zero;;;
  Local vec "temp1" ::== Int.zero;;;
  Local vec "s0" ::== Int.zero;;;
  Local vec "maj" ::== Int.zero;;;
  Local vec "temp2" ::== Int.zero;;;

  Local vec "a" ::== Int.zero;;;
  Local vec "b" ::== Int.zero;;;
  Local vec "c" ::== Int.zero;;;      
  Local vec "d" ::== Int.zero;;;      
  Local vec "e" ::== Int.zero;;;
  Local vec "f" ::== Int.zero;;;
  Local vec "g" ::== Int.zero;;;      
  Local vec "h" ::== Int.zero;;;      

  (core
    (* 16 is implicit *) "ww" (mm 16)
    "h0" "h1" "h2" "h3" "h4" "h5" "h6" "h7"
    "s0" "s1" "s1" "ch" "temp1" "s0" "maj" "temp2"
    "a" "b" "c" "d" "e" "f" "g" "h"
    hash).  
Next Obligation.
apply 64.
Defined.
Next Obligation.
unfold sha256'_obligation_1.
destruct (Fin.to_nat i).
auto.
Defined.
Next Obligation.
apply 16.
Defined.
Next Obligation.
unfold sha256'_obligation_1.
destruct (Fin.to_nat i).
auto.
Defined.

Definition sha256 : prog.
  refine (@ADecl Input 64 TVec32 "w" _).
  refine (@ADecl Input 16 TVec32 "m" _).
  refine (@ADecl Output 8 TVec32 "hash" _).
  refine (sha256' "w" "m" "hash").
Defined.

Definition x := Eval hnf in sha256.


Program Definition sha256_mult
  (* inputs *)
  (n : nat) (* Either 32 or 24 in hmac *)
  (w : id (tarr 64<<<tvec32>>>))
  (m : id (tarr n<<<tvec32>>>))
  (* outputs *)
  (hash : id (tarr 8 <<<tvec32>>>))
  : prog := 


  Local arr "ww" <<<(tarr 64<<<tvec32>>>), 64 >>>;;;
  iter 0 64 (fun i => _);;;
  Local arr ("mm" ++ (show (nat_to_prelInt n))) <<<(tarr n<<<tvec32>>>), n >>>;;;                     

  iter 0 n (fun i => _ );;;



  Local vec "h0" ::== Int.zero;;;
  Local vec "h1" ::== Int.zero;;;
  Local vec "h2" ::== Int.zero;;;      
  Local vec "h3" ::== Int.zero;;;      
  Local vec "h4" ::== Int.zero;;;
  Local vec "h5" ::== Int.zero;;;
  Local vec "h6" ::== Int.zero;;;      
  Local vec "h7" ::== Int.zero;;;      

  Local vec "s0" ::== Int.zero;;;
  Local vec "s1" ::== Int.zero;;;

  Local vec "s1" ::== Int.zero;;;
  Local vec "ch" ::== Int.zero;;;
  Local vec "temp1" ::== Int.zero;;;
  Local vec "s0" ::== Int.zero;;;
  Local vec "maj" ::== Int.zero;;;
  Local vec "temp2" ::== Int.zero;;;

  Local vec "a" ::== Int.zero;;;
  Local vec "b" ::== Int.zero;;;
  Local vec "c" ::== Int.zero;;;      
  Local vec "d" ::== Int.zero;;;      
  Local vec "e" ::== Int.zero;;;
  Local vec "f" ::== Int.zero;;;
  Local vec "g" ::== Int.zero;;;      
  Local vec "h" ::== Int.zero;;;      

  @core n
    "ww" ("mm" ++ (show (nat_to_prelInt n)))
    "h0" "h1" "h2" "h3" "h4" "h5" "h6" "h7"
    "s0" "s1" "s1" "ch" "temp1" "s0" "maj" "temp2"
    "a" "b" "c" "d" "e" "f" "g" "h"
    hash.  
Next Obligation.
 refine  ("ww"@'i <- w[[i]]). 
 destruct (Fin.to_nat i). 
 simpl.
 exact l.
Defined.
Next Obligation.
refine (("mm" ++ (show (nat_to_prelInt n)))@'i <- m[[i]]).
 destruct (Fin.to_nat i). 
 simpl.
 exact l.
Defined.


Definition sha256_mult32 : prog.
  refine (@ADecl Input 64 TVec32 "w" _).
  refine (@ADecl Input 32 TVec32 "m" _).
  refine (@ADecl Output 8 TVec32 "hash" _).
  refine (sha256_mult "w" "m" "hash").
  apply 32.
Defined.

Definition sha256_mult24 : prog.
  refine (@ADecl Input 64 TVec32 "w" _).
  refine (@ADecl Input 24 TVec32 "m" _).
  refine (@ADecl Output 8 TVec32 "hash" _).
  refine (sha256_mult "w" "m" "hash").
  apply 24.
Defined.

