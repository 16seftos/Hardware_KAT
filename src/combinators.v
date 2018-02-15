Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith ZArith.
Require Import Vector. 
Require Import String.
Require Import JMeq.

Require Import Integers.

Require Import lang.

Inductive pred : Type := 
| BPred : binop -> pred -> pred -> pred
| BZero : pred
| BNeg : pred -> pred
| BField : bvec32 -> pred.

Inductive pol : Type :=
| PTest : pred -> pol
| PUpd : (id TVec32 -> exp TVec32) -> pol 
| PChoice : pol -> pol -> pol
| PConcat : pol -> pol -> pol.

Fixpoint compile_pred (x : id TVec32) (p : pred) : exp TVec32 :=
  match p with
  | BPred op pl pr => EBinop op (compile_pred x pl) (compile_pred x pr)
  | BZero => EVal (Int.repr 0)
  | BNeg p' => ENot (compile_pred x p')
  | BField i => EVal i (*FIXME: EBinop OSub x (EVal i) = 0*)
  end.

Section M.
  Variable state : Type.

  Definition M (A : Type) := state -> (state * A).

  Definition ret (A : Type) (a : A) : M A := fun s => (s, a).

  Definition bind (A B : Type) (m : M A) (f : A -> M B) : M B :=
    fun s =>
      match m s with
      | (s', a) => f a s'
      end.
End M.

Definition new_buf : M nat string :=
  fun n => (S n, append "_x" (String (Ascii.ascii_of_nat n) "")).

Fixpoint compile_pol (i o : id TVec32) (p : pol) : M nat stmt :=
  match p with
  | PTest test =>
    let e_test := compile_pred i test
    in ret (SAssign Nonblocking o (EBinop OAnd (EVar i) e_test))

  | PUpd f => ret (SAssign Nonblocking o (f i))

  | PChoice p1 p2 =>
    bind new_buf (fun o_new1 =>
    bind new_buf (fun o_new2 =>                     
    bind (compile_pol i o_new1 p1) (fun s1 =>
    bind (compile_pol i o_new2 p2) (fun s2 => 
    ret (SSeq s1 
        (SSeq s2
        (SAssign Nonblocking o (EBinop OOr (EVar o_new1) (EVar o_new2)))))))))

  | PConcat p1 p2 =>
    bind new_buf (fun m_new =>
    bind (compile_pol i m_new p1) (fun s1 =>
    bind (compile_pol m_new o p2) (fun s2 => 
    ret (SSeq s1 s2))))
  end.

Section test.
  Variables i o : id TVec32.

  Definition zero_or_notzero : pol :=
    PChoice (PTest BZero) (PTest (BNeg BZero)).

  Eval compute in compile_pol i o zero_or_notzero O.
End test.  