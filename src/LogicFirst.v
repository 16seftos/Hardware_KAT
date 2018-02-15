Require Import Equivalence.
Require Import Quote.
Require Import Bool.

Inductive formula : Set :=
| Atomic : index -> formula
| Truth : formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula
| Not : formula -> formula.

(* Definition imp (P1 P2 : Prop) := P1 -> P2. *)
(* Infix "->" := imp (no associativity, at level 95). *)
Set Implicit Arguments.
Definition asgn := varmap Prop.
Definition imp (P1 P2 : Prop) := P1 -> P2.

Infix "===>" := imp (no associativity, at level 95).

Fixpoint formulaDenote (atomics : asgn) (f : formula) : Prop :=
match f with
| Atomic v => varmap_find False v atomics
| Truth => True
| Falsehood => False
| And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
| Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
| Imp f1 f2 => formulaDenote atomics f1 ===> formulaDenote atomics f2
| Not f1 => ~ formulaDenote atomics f1
end.

Fixpoint solver (atomics : asgn) (f : formula) : bool :=
  match f with
  | Atomic index => false
  | Truth => true
  | Falsehood => false
  | And f1 f2 => andb (solver atomics f1) (solver atomics f2)
  | Or f1 f2 => orb (solver atomics f1) (solver atomics f2)
  | Imp f1 f2 => if solver atomics f1 then solver atomics f2 else true
  | Not f1 => negb (solver atomics f1)
  end.

Require Import Setoid.

Lemma solver_sound atomics f : solver atomics f = true -> formulaDenote atomics f.
Proof.
  induction f; simpl; auto; try inversion 1.
  { rewrite andb_true_iff in H; destruct H as [Hx Hy].
    split; [apply IHf1; auto|apply IHf2; auto]. }
Admitted.

Ltac solver_tac :=
  quote formulaDenote;
  apply solver_sound;
  reflexivity.

Lemma xx : True ===> True /\ True.
Proof. solver_tac. Qed.

Lemma yy : True /\ False ===> False.
Proof. solver_tac. Qed.

Lemma zz : True /\ (True /\ (False \/ False)) ===> False.
Proof. solver_tac. Qed.

Lemma ww (P : Prop) : P /\ True.
Proof.
  quote formulaDenote.






