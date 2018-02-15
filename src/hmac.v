(* hmac.v *)

Set Implicit Arguments.
Unset Strict Implicit.
(*
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra. Import zmodp.
*)
Require Import List. Import ListNotations.
Require Import ZArith.

Require Import Integers.

Require Import sha256.

Require Import lang syntax.

Open Scope hdl_type_scope.
Open Scope hdl_exp_scope.
Open Scope hdl_stmt_scope.
Open Scope string_scope.

Program Definition h_core 
    (* inputs *)
    (key : id (tarr 16<<<tvec32>>>))
    (msg : id (tarr 16 <<<tvec32>>>))
    (* local variables *)
    (w : id (tarr 64 <<<tvec32>>>))
    (ikp okp : id (tarr 16<<<tvec32>>>))
    (fstin : id (tarr 32<<<tvec32>>>))
    (sndin : id (tarr 24<<<tvec32>>>))
    (fstot sndot : id (tarr 8<<<tvec32>>>))
    (* output *)
    (hout : id (tarr 8 <<<tvec32>>>))
  : prog :=

(* ikp and okp *)
iter 0 16 (fun i => ikp@'i <-
 (key[[i]] xor (val 909522486%Z)));;;

iter 0 16 (fun j => okp@'j <-
 (key[[j]] xor (val 1549556828%Z)));;;

(* Set up the first hash's input *)
iter 0 16 (fun i => fstin@'i <- ikp[[i]]);;;
iter 16 32 (fun j => fstin@'j <- msg[[''(j-16)]]);;;

(* Run the hash function *)
@sha256_mult 32 w fstin fstot;;;

(* Set up the second hash's input *)
iter 0 16 (fun i => sndin@'i <- okp[[i]]);;;
iter 16 24 (fun j => sndin@'j <- fstot[[''(j-16)]]);;;

(* Run the hash function once again *)
@sha256_mult 24 w sndin sndot;;;

(* And finally... *)
iter 0 8 (fun i => hout@'i <- sndot[[i]]);;;
done.

Lemma LessThanX: forall x y j : nat,
  (x - j > 0) -> (x < y+j -> x-j < y).
Proof.
  intros; induction j.
  - omega.
  - assert(x < S (y + j)). omega.
    assert(x < y + j \/ x = y + j). omega.
    destruct H2.
    + apply IHj in H2; omega.
    + assert (x - j = y). omega. rewrite <- H3. omega.
Qed.

Ltac LessXSolve i l :=
  unfold nat_of_fin; destruct (Fin.to_nat i); simpl; omega.

Next Obligation. LessXSolve j l. Qed.
Next Obligation. LessXSolve j l. Qed.


    (* (key : id (tarr 16<<<tvec32>>>)) *)
    (* (msg : id (tarr 16 <<<tvec32>>>)) *)
    (* (* local variables *) *)
    (* (w : id (tarr 64 <<<tvec32>>>)) *)
    (* (ikp okp : id (tarr 16<<<tvec32>>>)) *)
    (* (fstin : id (tarr 32<<<tvec32>>>)) *)
    (* (sndin : id (tarr 24<<<tvec32>>>)) *)
    (* (fstot sndot : id (tarr 8<<<tvec32>>>)) *)
    (* (* output *) *)
    (* (hout : id (tarr 8 <<<tvec32>>>)) *)

Definition hmac'
(* inputs *)
(key : id (tarr 16 <<<tvec32>>>))
(msg : id (tarr 16 <<<tvec32>>>))
(* output *)
(hout : id (tarr 8 <<<tvec32>>>))
  : prog :=
  Local arr "w" <<<(tarr 64 <<<tvec32>>>), 64>>>;;;
  Local arr "ikp" <<<(tarr 16 <<<tvec32>>>), 16>>>;;;                      Local arr "okp" <<<(tarr 16 <<<tvec32>>>), 16>>>;;;
  Local arr "fstot" <<<(tarr 8 <<<tvec32>>>), 8>>>;;;
  Local arr "sndot" <<<(tarr 8 <<<tvec32>>>), 8>>>;;;
  Local arr "fstin" <<<(tarr 32 <<<tvec32>>>), 32>>>;;;
  Local arr "sndin" <<<(tarr 24 <<<tvec32>>>), 24>>>;;;
  h_core
    key msg
    "w" "ikp" "okp" "fstin" "sndin" "fstot"   "sndot"
    hout.

(* Definition x := Eval hnf in hmac'. *)
Definition hmac : prog :=
  Input arr "key" <<<(tarr 16 <<<tvec32>>>), 16>>>;;;
  Input arr "msg" <<<(tarr 16 <<<tvec32>>>), 16>>>;;;
  Output arr "hout" <<<(tarr 8 <<<tvec32>>>), 8>>>;;;
  (hmac' "key" "msg" "hout");;;
 done.


(* Definition hmac : prog. *)
(*   refine (@ADecl Input 16 TVec32 "key" _). *)
(*   refine (@ADecl Input 16 TVec32 "msg" _). *)
(*   refine (@ADecl Output 8 TVec32 "hout" _). *)
(*   refine (hmac' "key" "msg" "hout"). *)
(* Defined. *)
