Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith ZArith.
Require Import Vector. 
Require Import String.
Require Import JMeq.
Require Import List. Import ListNotations.

Require Import Integers.

Require Import lang.

Inductive fld : Type := OpCode | EffAddr.

Definition offset (f : fld) : int :=
  match f with
  | OpCode => Int.repr 26
  | EffAddr => Int.repr 0 (*BOGUS*)
  end.

Definition size (f : fld) : int :=
  match f with
  | OpCode => Int.repr 6
  | EffAddr => Int.repr 26 (*BOGUS*)
  end.

Inductive pred : Type := 
| BPred : binop -> pred -> pred -> pred
| BZero : pred
| BNeg : pred -> pred
| BField : fld -> bvec32 -> pred.

Inductive pol : Type :=
| PTest : pred -> pol
| PUpd : (id TVec32 -> exp TVec32) -> pol 
| PChoice : pol -> pol -> pol
| PConcat : pol -> pol -> pol.

(* Compile Predicates *)
(*Define neg1 := EVal (Int.Repr 4294967295).*)

Fixpoint compile_pred (x : id TVec32) (p : pred) : exp TVec32 :=
  match p with
  | BPred op pl pr => EBinop op (compile_pred x pl) (compile_pred x pr)
  | BZero => EVal (Int.repr 0)
  | BNeg p' => ENot (compile_pred x p')
  (*BField OpCode Int.Repr 2*)
  | BField f i => (*FIXME: don't ignore offsets*) (* Almost completely fixed, probably *)
     EBinop OAnd (EBinop OShru (EVar x) (EVal (offset f)))   (EBinop OShru (EVal (Int.repr 4294967295)) (EVal (size f)))
  end.

(* Monad *)
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

(* Variables using decimal integers *)
Inductive digit : Type :=
  Zero | One | Two | Three | Four | Five | Six | Seven | Eight | Nine.

Definition digit2string (d : digit) : string :=
  match d with
  | Zero => "0"
  | One => "1"
  | Two => "2"
  | Three => "3"
  | Four => "4"
  | Five => "5"
  | Six => "6"
  | Seven => "7"
  | Eight => "8"
  | Nine => "9"
  end.

Definition decimal := list digit.

Fixpoint decimal2string (d : decimal) : string :=
  match d with
  | nil => ""
  | x :: d' => append (digit2string x) (decimal2string d')
  end.

Fixpoint nat2decimal_aux (fuel n : nat) (acc : decimal) : decimal :=
  match fuel with
  | O => Zero :: acc
  | S fuel' => 
      match n with
      | 0 => Zero :: acc
      | 1 => One :: acc
      | 2 => Two :: acc
      | 3 => Three :: acc
      | 4 => Four :: acc
      | 5 => Five :: acc
      | 6 => Six :: acc
      | 7 => Seven :: acc
      | 8 => Eight :: acc
      | 9 => Nine :: acc
      | _ =>
        let d := Nat.div n 10 in
        let r := Nat.modulo n 10 in
        nat2decimal_aux fuel' d (nat2decimal_aux fuel' r acc)
      end
  end.
 
 Definition nat2decimal (n : nat) : decimal :=
   nat2decimal_aux n n nil.
 
 Definition nat2string (n : nat) : string := decimal2string (nat2decimal n).
 
 Definition new_buf : M nat string :=
   fun n => (S n, append "internal" (nat2string n)).

(* Compile Policies *)
Fixpoint compile_pol (i o : id TVec32) (p : pol) (monad : M nat) : M nat stmt :=
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
    bind new_buf (fun m_new_buf =>
    bind (compile_pol i m_new_buf p1) (fun s1 =>
    bind (compile_pol m_new_buf o p2) (fun s2 => 
    ret (SSeq s1 s2))))
  end.

Section test.
  Variables i o : id TVec32.

  Definition zero_or_notzero : pol :=
    PChoice (PTest BZero) (PTest (BNeg BZero)).

  Eval compute in compile_pol i o zero_or_notzero O.

  Definition j := Int.repr 2.
  Definition op_j := BField OpCode j.

  Definition sec_addr := BField EffAddr (Int.repr 0). (*FIXME*)
  
  (*PTest BField OpCode Int.repr2*)
  Definition sec_jmp : pol :=
    PChoice
      (PConcat (PTest op_j) (PTest (BNeg sec_addr)))
      (PTest (BNeg op_j)).

  Definition compile (p : pol) : prog :=
    let (_,s) := compile_pol i o p O
    in VDecl Input i (Int.repr 0)
      (VDecl Output o (Int.repr 0)
      (PStmt s)).              

  Require Import syntax.

  Local Open Scope hdl_stmt_scope.
  Local Open Scope hdl_exp_scope.
  
  Eval vm_compute in compile sec_jmp.
End test.

Require Import Extractions.

(* print the program *)

Definition i : id TVec32 := "i".
Definition o : id TVec32 := "o".

Definition sec_jmp_compiled : prog := compile i o sec_jmp.

Definition pretty_print_sec_jmp :=
  pretty_print_tb "secjmp" sec_jmp_compiled.

Eval vm_compute in pretty_print_sec_jmp.

Extract Constant main => "Prelude.putStrLn pretty_print_sec_jmp".

(* run the program 'secjmp.hs' and pipe to a file to get verilog *)
Extraction "secjmp.hs" pretty_print_sec_jmp.
