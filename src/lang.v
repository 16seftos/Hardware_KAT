Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith ZArith.
Require Import Vector. 
Require Import String.
Require Import JMeq.

Require Import Integers.

(* semantics definitions *)
Definition bit := bool.
Definition bvec64 := Int64.int.
Definition bvec64_nil : bvec64 := Int64.zero.

Definition iN (N : nat) := Fin.t N.

Definition arr (N:nat) T := Vector.t T N.
Definition arr_upd N T (a:arr N T) (i:iN N) (v:T) : arr N T :=
  Vector.replace a i v.

Program Fixpoint vector_keymap
         A B n (v : Vector.t A n)
         (f : Fin.t n -> A -> B)
  : Vector.t B n
  := match v with
     | Vector.nil => (@Vector.nil B)
     | Vector.cons a n' v' =>
       Vector.cons
         _ (f (@Fin.of_nat_lt (n-1) n _) a) n'
         (vector_keymap v' (fun i => f (@Fin.of_nat_lt (proj1_sig (Fin.to_nat i)) n _)))
     end.
Next Obligation.
  induction n';
    omega.
Defined.
Next Obligation.
  clear -i.
  induction i; simpl; try omega.
  destruct (Fin.to_nat i); simpl in *; omega.
Defined.

Definition arr_init (N : nat) T (t0 : T) (f : iN N -> T) : arr N T :=
  vector_keymap (Vector.const t0 N) (fun ix _ => f ix).

(* syntax *)
Inductive ty : Type :=
  | TVec64 : ty
  | TArr : nat -> ty -> ty.

Ltac solve_ty_dec :=
  repeat
    (match goal with
     | |- context[not (?X)] => 
       let x := fresh "x" in intros x
     | [ H : (?T /\ ?T1) |- _ ] => destruct H
     | [ H : ~ (?T /\ ?T1) |- _ ] => destruct H
     | [ H : ?P |- _] => 
       match type of P with
         Prop =>
         repeat
           (match goal with
            | H : ?T |- False =>
              solve [ subst; inversion H]
            end)
       end
     end); auto.

Program Fixpoint ty_dec (t1 t2 : ty) : {t1=t2} + {t1<>t2} :=
  match t1, t2 with
  | TVec64, TVec64 => left eq_refl
  | TArr n1 t1', TArr n2 t2' =>
    match eq_nat_dec n1 n2 with
    | left pf =>
      match ty_dec t1' t2' with
      | left pf' => left _
      | right pf' => right _
      end
    | right pf => right _
    end
  | _, _ => right _
  end.
Next Obligation.
  solve_ty_dec.
  destruct t1; destruct t2; solve_ty_dec.
  exfalso.
  eapply H; eauto.
Defined.
Next Obligation.
  split; intros;
  solve_ty_dec.
Defined.
Next Obligation.
  split; intros;
  solve_ty_dec.
Defined.

Fixpoint interp_ty (t : ty) : Type :=
  match t with
  | TVec64 => bvec64
  | TArr N t2 => arr N (interp_ty t2)
  end.

Program Definition cast_interp_ty (t1 t2 : ty) (pf : t1=t2)
  : interp_ty t1 -> interp_ty t2 :=
  fun v =>
    match pf as p in eq _ _ return interp_ty t2 with
    | eq_refl => v
    end.

Definition id (t : ty) := string.

Inductive binop : Type :=
    OAnd (* and *)| OXor (* xor *) | OAdd (* 64-bit unsigned add *)
    | OShr (* shift right *) | OShru (* unsigned shift right *)
    | OShl (* shift left *)
    | OOr
    | OSub
    | OEq
    (*| OIfOr (* or used in IF statements *)*)
    .

Inductive exp : ty -> Type :=
  | EVal : bvec64 -> exp TVec64
  | EVar : forall t, id t -> exp t
  | EDeref : forall N t (i : iN N), id (TArr N t) -> exp t
  | EBinop : binop -> exp TVec64 -> exp TVec64 -> exp TVec64
  | ENot : exp TVec64 -> exp TVec64.

Inductive assign_kind : Type := Blocking | Nonblocking.

Inductive stmt : Type :=
  | SAssign : forall (k:assign_kind) (x:id TVec64) (e:exp TVec64), stmt
  | SUpdate : forall (k:assign_kind) N (x:id (TArr N TVec64)) (i:iN N) (e:exp TVec64), stmt
  | SSeq : stmt -> stmt -> stmt
  | SITE : exp TVec64 -> stmt -> stmt -> stmt
  | SIter : forall (lo hi:nat) (f:iN hi -> stmt), stmt
  | SSkip : stmt.

Definition r_rotate (x : exp TVec64)
           (i : exp TVec64) : exp TVec64 :=
  EBinop OOr (EBinop OShr x i) (EBinop OShl x 
           (EBinop OSub (EVal (Int64.repr 64)) i)).

Inductive var_kind : Type := Local | Input | Output.

Inductive prog : Type :=
  | VDecl : var_kind -> id TVec64 -> bvec64 -> prog -> prog
  | ADecl : var_kind -> forall N t, id (TArr N t) -> prog -> prog
  | PStmt : stmt -> prog
  | PSeq : prog -> prog -> prog
  | PDone : prog.

Definition binop_interp (op : binop) (v1 v2 : bvec64) : bvec64 :=
  match op with
  | OAnd => Int64.and v1 v2
  | OSub => Int64.sub v1 v2
  | OXor => Int64.xor v1 v2
  | OAdd => Int64.add v1 v2
  | OShr => Int64.shr v1 v2
  | OShru => Int64.shru v1 v2
  | OShl => Int64.shl v1 v2
  | OOr =>  Int64.or v1 v2
  | OEq => v1 (*BOGUS*)
  (*| OIfOr => v1 (*BOGUS*)*)
  end.

Section state.
  Definition state := forall t, id t -> interp_ty t.

  Definition upd t (x : id t) (v : interp_ty t) (s : state)
    : state :=
    fun t2 (y : id t2) =>
      match ty_dec t t2 as t' in sumbool _ _ with
      | left pf => 
        match string_dec x y with
        | left pf' => cast_interp_ty pf v
        | right pf' => s t2 y
        end
      | right _ => s t2 y
      end.
End state.
  
Section exp_interp.
  Variable s : forall t, id t -> interp_ty t.
  
 Fixpoint exp_interp (e : exp TVec64) : interp_ty TVec64 := 
    match e as e' in exp t return interp_ty t with 
    | EVal v => v
    | EVar _ x => s x
    | EDeref _ _ i x => Vector.nth (s x) i
    | EBinop op e1 e2 =>
      let v1 := exp_interp e1 in
      let v2 := exp_interp e2 in
      binop_interp op v1 v2
    | ENot e' =>
      Int64.not (exp_interp e')
    end.
     
End exp_interp.

Definition enum_iN (N : nat) : list (iN N) :=
  Vector.to_list (vector_keymap (Vector.const O N) (fun ix _ => ix)).

Definition itern lo hi T (f : iN hi -> T -> T) (t : T) : T :=
  List.fold_right
    f t
    (List.filter (fun i => let n := proj1_sig (Fin.to_nat i) in
                           (lo <=? n))  (enum_iN hi)).

Fixpoint stmt_interp (s : state) (c : stmt) (cont : state -> state) : state :=
  match c with
  | SAssign k x e => 
    let v := exp_interp s e in
    cont (upd x v s)
  | SUpdate k t x i e =>
    let v := exp_interp s e in
    cont (upd x (arr_upd (s _ x) i v) s)
  | SSeq c1 c2 =>
    stmt_interp s c1 (fun s' => stmt_interp s' c2 cont)
  | SITE e c1 c2 =>
    let v := exp_interp s e in
    if Int64.eq v Int64.zero then stmt_interp s c2 cont
    else stmt_interp s c1 cont
  | SIter lo hi f =>
    cont (itern lo (fun i s => stmt_interp s (f i) (fun s' => s')) s)
  | SSkip => cont s
  end.

Program Fixpoint prog_interp (s : state) (p : prog) : state :=
  match p with
  | VDecl vk x v p' =>
    prog_interp (upd x v s) p'
  | ADecl vk N t x p' =>
    prog_interp s p'
  | PStmt c => stmt_interp s c (fun s => s)
  | PSeq p1 p2 =>
    prog_interp (prog_interp s p1) p2
  | PDone => s
  end.
