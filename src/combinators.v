Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith ZArith.
Require Import Vector. 
Require Import String.
Require Import JMeq.
Require Import List. Import ListNotations.

Require Import Integers.

Require Import lang.

Inductive fld : Type := OpCode | JField | EffAddr | EffTag.

Definition offset (f : fld) : int :=
  match f with
  | OpCode  => Int.repr 26
  | JField  => Int.repr  0 (* Jump field offset, of instr *)
  | EffAddr => Int.repr  0 (* Technically EXE output, of res *)
  | EffTag  => Int.repr 22 (* Tag is top 8 bits *)
  end.

Definition size (f : fld) : int :=
  match f with
  | OpCode  => Int.repr  6
  | JField  => Int.repr 26 (* Jump field size, of instr *)
  | EffAddr => Int.repr 32 (* Exe output, of res *)
  | EffTag  => Int.repr  87 (* Tag is top 8 bits *)
  end.

Inductive pred : Type := 
| BPred : binop -> pred -> pred -> pred
| BZero : pred
| BNeg : pred -> pred
| BField : fld -> bvec32 -> pred.

Inductive pol : Type :=
| PTest : pred -> pol -> pol
| PUpd : (id TVec32 -> exp TVec32) -> pol 
| PChoice : pol -> pol -> pol
| PConcat : pol -> pol -> pol
| PSkip : pol
| PId : pol.

(* Compile Predicates *)
Fixpoint compile_pred (x : id TVec32) (p : pred) : exp TVec32 :=
  match p with
  | BPred op pl pr => EBinop op (compile_pred x pl) (compile_pred x pr)
  | BZero => EVal (Int.repr 0)
  | BNeg p' => ENot (compile_pred x p')
  | BField f i => (*FIXME: don't ignore offsets*) (* Almost completely fixed, probably *)
    let field_val :=
        EBinop
          OAnd
          (EBinop OShru (EVar x) (EVal (offset f)))
          (EBinop OShru (EVal (Int.repr 4294967295))
                  (EVal (Int.sub (Int.repr 32) (size f))))
    in ENot (EBinop OXor field_val (EVal i)) (*FIXME: this computation should return all 0s or all 1s*)
  end.

(* Monad *)
Section M.
  Variable state : Type.

  Definition M (A : Type) := state -> state * A.

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

 Definition state := (nat * list string)%type.
 
 Definition new_buf : M state string :=
   fun p =>
     match p with
     | (n, l) =>
       let new_buf := append "internal" (nat2string n) in 
       ((S n, new_buf::l), new_buf)
     end.       
 
 (* Compile Policies *)
 Fixpoint compile_pol (i o : id TVec32) (p : pol) : M state stmt :=
  match p with
  | PTest test p_cont =>
    let e_test := compile_pred i test
    in bind (compile_pol i o p_cont) (fun s_cont =>
       ret (SITE e_test s_cont SSkip))

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

  | PSkip => ret SSkip

  | PId => ret (SAssign Nonblocking o (EVar i))
  end.

 Fixpoint compile_bufs (bufs : list string) (p : prog) : prog :=
   match bufs with
   | nil => p
   | x::bufs' => VDecl Local x (Int.repr 0) (compile_bufs bufs' p)
   end.
 
Section compile.
  Variables i o : id TVec32.
  
  Definition compile (p : pol) : prog :=
    let (state, s) := compile_pol i o p (O, nil) in 
    let output_p := VDecl Input i (Int.repr 0) (VDecl Output o (Int.repr 0) (PStmt s))
    in match state with
       | (_, bufs) => compile_bufs bufs output_p
       end.
End compile.

Section opcodes.
  Definition j := Int.repr 2.
  Definition op_j := BField OpCode j.
End opcodes.

Section test.
  Variables i o : id TVec32.

  Definition sec_addr := BField JField (Int.repr 0). (*FIXME*)
  
  Definition sec_jmp : pol :=
    PChoice
      (PTest op_j (PTest (BNeg sec_addr) PId))
      (PTest (BNeg op_j) PId).

  Require Import syntax.

  Local Open Scope hdl_stmt_scope.
  Local Open Scope hdl_exp_scope.
  
  Eval vm_compute in compile i o sec_jmp.
End test.

Section SFI.
  Variables ri ro : id TVec32.

  (* Lets say that a secure addr. has a tag 0xA2...... *)
  (* Need to mask tag, see above *)

  Definition secure_mem_address := BField EffTag (Int.repr 162). (*FIXME*)
  
  (*This test acts on results so pretend it's in the result slice*)
  Definition sec_field_iso : pol :=
      (PTest (secure_mem_address) PId).

  Require Import syntax.

  Local Open Scope hdl_stmt_scope.
  Local Open Scope hdl_exp_scope.
  
  Eval vm_compute in compile ri ro sec_field_iso.
End SFI.

Require Import Extractions.

(* print the program *)

Definition i : id TVec32 := "i".
Definition o : id TVec32 := "o".
Definition ri : id TVec32 := "ri".
Definition ro : id TVec32 := "ro".

Definition sec_jmp_compiled : prog := compile i o sec_jmp.
Definition SFI_compiled : prog := compile ri ro sec_field_iso.

Definition pretty_print_sec_jmp :=
  pretty_print_tb "secjmp" sec_jmp_compiled.
Definition pretty_print_SFI :=
  pretty_print_tb "SFI" SFI_compiled.

Eval vm_compute in pretty_print_sec_jmp.
Eval vm_compute in pretty_print_SFI.

(* Not sure how this works. *)
Extract Constant main => "Prelude.putStrLn pretty_print_sec_jmp".
Extract Constant main => "Prelude.putStrLn pretty_print_p2".

(* run the program 'secjmp.hs' and pipe to a file to get verilog *)
Extraction "secjmp.hs" pretty_print_sec_jmp.
Extraction "SFI.hs" pretty_print_SFI.


