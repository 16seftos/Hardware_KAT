(* H. Wiley Hill III | 23 March 2017 *)

Require Import Arith.

Definition id := nat.

Inductive bvalue : Type :=
  | btrue : bvalue
  | bfalse : bvalue.          

Inductive tm : Type :=
  | tval : bvalue -> tm
  | tneg : tm -> tm           
  | tif : tm -> tm -> tm -> tm.

(* Point 4.2 in the paper: Event expressions *)

(* T ::= v (change of value)
       | posedge V (positive edge)
       | negedge V (negative edge)
       | T1 or ... or Tn (compound sensitivity list) *)

Inductive ee : Type :=
  | tvalue : id -> ee (* change of value *)
  | tposedge : id -> ee (* positive edge *)
  | tnegedge : id -> ee (* negative edge *)
  | tor : ee -> ee -> ee. (* compound sensitivity list *)

(* Point 4.3 in the paper: Statements *)

(* S ::== V1, ..., Vn := E1, ..., En (assignment)
        | S1; ...; Sn (sequencing block)
        | if E then S1 (conditional without else)
        | if E then S1 else S2 (conditional with else)
        | at T S (event control) *)

Inductive st : Type :=
  | stass : id -> tm -> st (* assignment - use seq. block for more *)
  | stseq : st -> st -> st (* sequencing block *)
  | stskip : st (* do nothing *)
  | stcond : tm -> st -> st -> st (* conditional with else *)
  | stev : ee -> st. (* event control *)

Definition env := id -> bvalue.

Definition upd (rho : env) (x : id) (v : bvalue) : env :=
  fun y => if eq_nat_dec x y then v else rho y.

Inductive guarded : st -> ee -> Prop :=
| guarded_stev :
    forall e,
      guarded (stev e) e
| guarded_stseq :
    forall e s1 s2,
      guarded s1 e ->
      guarded (stseq s1 s2) e.

Fixpoint unguard (s : st) :=
  match s with
  | stev ee => stskip
  | stseq s1 s2 => stseq (unguard s1) s2
  | _ => s
  end.

Lemma nguarded_unguard e s : ~guarded (unguard s) e.
Proof.
  induction s; try inversion 1; subst.
  apply IHs1; auto.
Qed.  

Fixpoint eval (rho : env) (t : tm) : bvalue :=
match t with
| tval b => b
| tneg t' =>
  match (eval rho t') with
  | btrue => bfalse
  | bfalse => btrue
  end
| tif t1 t2 t3 =>
  if (eval rho t1) then (eval rho t2) else (eval rho t3)
end.

Theorem eval_example1 : forall rho : env,
  eval rho (tval btrue) = btrue.
Proof. simpl. reflexivity. Qed.

Theorem eval_example2 : forall rho : env,
  eval rho (tif (tneg (tval bfalse)) (tval bfalse) (tval btrue)) = bfalse.
Proof. simpl. reflexivity. Qed.

Fixpoint interp (rho : env) (s : st) : env * st :=
  match s with
  | stass x t => (upd rho x (eval rho t), stskip)
  | stseq s1 s2 =>
    match interp rho s1 with
    | (rho', stskip) => interp rho' s2
    | (rho', s1') => (rho', stseq s1' s2)
    end
  | stskip => (rho, stskip)
  | stcond t s1 s2 =>
    match eval rho t with
    | btrue => interp rho s1
    | bfalse => interp rho s2
    end
  | stev e => (rho, s)
  end.

Lemma interp_guarded rho s rho' s' :
  interp rho s = (rho', s') ->
  s'=stskip \/ exists e, guarded s' e.
Proof.
  intros. generalize dependent rho.
  generalize dependent rho'.
  generalize dependent s'.
  induction s; intros; simpl in H.
  - left. inversion H. reflexivity.
  - case_eq (interp rho s1); intros rho'' st H2.
    rewrite H2 in H.
    destruct (IHs1 _ _ _ H2) as [H1|H1].
    { subst st.
      destruct (IHs2 _ _ _ H).
      { subst s'. left; auto. }
      destruct H0 as [e H0].
      right; exists e; auto. }
    destruct H1 as [e H1].
    inversion H1; subst.
    { inversion H; subst.
      clear H.
      right; exists e.
      constructor; auto. }
    inversion H1; subst.
    inversion H; subst.
    right; exists e.
    constructor.
    constructor; auto.
  - inversion H. left. reflexivity.
  - case_eq (eval rho t).
    + intros. rewrite H0 in H.
      eapply IHs1. apply H.
    + intros. rewrite H0 in H.
      eapply IHs2. apply H.
  - right. exists e. inversion H. constructor.
Qed.
