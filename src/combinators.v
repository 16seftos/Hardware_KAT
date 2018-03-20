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

Definition offset (f : fld) : Int64.int :=
  match f with
  | OpCode  => Int64.repr 26
  | JField  => Int64.repr  0 (* Jump field offset, of instr *)
  | EffAddr => Int64.repr  0 (* Technically EXE output, of res *)
  | EffTag  => Int64.repr 56 (* Tag is top 8 bits *)  (* Assume it's the top 8bits of the top word *)
  end.

Definition size (f : fld) : Int64.int :=
  match f with
  | OpCode  => Int64.repr  6
  | JField  => Int64.repr 26 (* Jump field size, of instr *)
  | EffAddr => Int64.repr 32 (* Exe output, of res *)
  | EffTag  => Int64.repr  8 (* Tag is top 8 bits *)
  end.

Inductive pred : Type := 
| BPred : binop -> pred -> pred -> pred
| BZero : pred
| BNeg : pred -> pred
| BField : fld -> bvec64 -> pred
(*| BIfOr : pred -> pred -> pred*). (* Combines 2 predicates *)

Inductive pol : Type :=
| PTest : pred -> pol -> pol
| PUpd : (id TVec64 -> exp TVec64) -> pol 
| PChoice : pol -> pol -> pol
| PConcat : pol -> pol -> pol
| PSkip : pol
| PId : pol.

(* Compile Predicates *)
Fixpoint compile_pred (x : id TVec64) (p : pred) : exp TVec64 :=
  match p with
  | BPred op pl pr => EBinop op (compile_pred x pl) (compile_pred x pr)
  | BZero => EVal (Int64.repr 0)
  | BNeg p' => ENot (compile_pred x p')
  | BField f i => 
    let field_val :=
        EBinop
          OAnd
          (EBinop OShru (EVar x) (EVal (offset f)))
          (EBinop OShru (EVal (Int64.repr 18446744073709551615))
                  (EVal (Int64.sub (Int64.repr 64) (size f))))
    in (EBinop OEq field_val (EVal i)) 
  (*| BIfOr pd1 pd2 => EBinop OIfOr pd1 pd2*) (* The OR of two predicates, | will not work in IF statements (probably?) *)
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
 Fixpoint compile_pol (i o : id TVec64) (p : pol) : M state stmt :=
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
        (SAssign Nonblocking o
          (EBinop OOr (EVar o_new1) (EVar o_new2)))))))))

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
   | x::bufs' => VDecl Local x (Int64.repr 0) (compile_bufs bufs' p)
   end.
 
Section compile.
  Variables i o : id TVec64.
  
  Definition compile (p : pol) : prog :=
    let (state, s) := compile_pol i o p (O, nil) in 
    let output_p := VDecl Input i (Int64.repr 0) (VDecl Output o (Int64.repr 0) (PStmt s))
    in match state with
       | (_, bufs) => compile_bufs bufs output_p
       end.
End compile.

Section opcodes.
  Definition j := Int64.repr 2.
  Definition op_j := BField OpCode j.
  (* Store-type instruction are: *)
  (*  *)
  Definition instr_SB := Int64.repr 40.
  Definition instr_SC := Int64.repr 56.
  Definition instr_SCD:= Int64.repr 60.
  Definition instr_SD := Int64.repr 63.
  Definition instr_SDL:= Int64.repr 44.
  Definition instr_SDR:= Int64.repr 45.
  Definition instr_SH := Int64.repr 41.
  Definition instr_SW := Int64.repr 43.
  Definition instr_SWL:= Int64.repr 42.
  Definition instr_SWR:= Int64.repr 46.
  (*Definition op_store := BIfOr (
    BIfOr ( BIfOr ( BIfOr (BField OpCode instr_SB )
                          (BField OpCode instr_SC ) )
                  ( BIfOr (BField OpCode instr_SCD)
                          (BField OpCode instr_SD ) ) )
          ( BIfOr ( BIfOr (BField OpCode instr_SDL)
                          (BField OpCode instr_SDR) )
                  ( BIfOr (BField OpCode instr_SH )
                          (BField OpCode instr_SW ) ) )
                               )(
    BIfOr                 (BField OpCode instr_SWL)
                          (BField OpCode instr_SWR) ).*)
  Definition op_storew := BField OpCode instr_SW.
End opcodes.

Section sec_jmp.
  Variables i o : id TVec64.

  Definition sec_addr := BField JField (Int64.repr 0). (*FIXME*)
  
  Definition sec_jmp : pol :=
    PChoice
      (PTest op_j (PTest (BNeg sec_addr) PId))
      (PTest (BNeg op_j) PId).

  Require Import syntax.

  Local Open Scope hdl_stmt_scope.
  Local Open Scope hdl_exp_scope.
  
  Eval vm_compute in compile i o sec_jmp.
End sec_jmp.

(* FIXME *)
Section SFI.
  Variables ri ro : id TVec64.
  (* ri must be able to include effaddr and the original instruction *)
  

  (* Lets say that a secure addr. has a tag 0xA2...... *)
  (* Need to mask tag, see above *)

  Definition secure_mem_address := BField EffTag (Int64.repr 162). (*FIXME*)
  (* Make sure it tests that it's a load or store type instruction, defined above *)
  (* If the process0or has a memory access wire that would make things easier, but I don't think so *)
  (* Just test all feasable isntructions of thost types?  mips instr? *)

  (* Check st. instruction *)
  (* op_store *)

  (* Force address into range 162 *)
  (* Definition force_range_ef_adr : (id TVec64 -> exp TVec64) :=
    EBinop OOr (EBinop OAnd (EVar ri)
                            (EBinop OShl (EVal (Int64.repr 67108864)) (EVal (Int64.repr 32)) ) ) 
               (EBinop OShl (EVal (Int64.repr 162))
                            (EVal (Int64.repr 56)) ). *)

  (*This test acts on results so pretend it's in the result slice*)
  Definition sec_field_iso : pol :=
   (*PConcat( *)
            PTest op_storew PId (*)
           (
            PUpd ro (force_range_ef_adr)
           )*).

  Require Import syntax.

  Local Open Scope hdl_stmt_scope.
  Local Open Scope hdl_exp_scope.
  
  Eval vm_compute in compile ri ro sec_field_iso.
End SFI.

(* FIXME *)
Section Taint.
  Variables i o : id TVec64.

  (* policy that tracks taint *)
  Definition taint_tracker : pol :=
    (*PTest (BNeg BZero) PId.*)
    (* or *)
    PId.

  Require Import syntax.
  Local Open Scope hdl_stmt_scope.
  Local Open Scope hdl_exp_scope.
  Eval vm_compute in compile i o taint_tracker.
End Taint.

Require Import Extractions.

(* print the program *)

Definition i : id TVec64 := "i".
Definition o : id TVec64 := "o".
Definition ri : id TVec64 := "ri".
Definition ro : id TVec64 := "ro".

Definition sec_jmp_compiled : prog := compile  i  o       sec_jmp.
Definition SFI_compiled     : prog := compile ri ro sec_field_iso.
Definition taint_compiled   : prog := compile  i  o taint_tracker.

Definition pretty_print_sec_jmp :=
  pretty_print_tb "secjmp" sec_jmp_compiled.
Definition pretty_print_SFI :=
  pretty_print_tb "SFI" SFI_compiled.
Definition pretty_print_taint :=
  pretty_print_tb "taint" taint_compiled.

Eval vm_compute in pretty_print_sec_jmp.
Eval vm_compute in pretty_print_SFI.
Eval vm_compute in pretty_print_taint.

(* Not sure how this works. *)
Extract Constant main => "Prelude.putStrLn pretty_print_sec_jmp".
Extract Constant main => "Prelude.putStrLn pretty_print_SFI".
Extract Constant main => "Prelude.putStrLn pretty_print_taint".

(* run the program 'secjmp.hs' and pipe to a file to get verilog *)
Extraction "secjmp.hs" pretty_print_sec_jmp.
Extraction "SFI.hs" pretty_print_SFI.
Extraction "taint.hs" pretty_print_taint.


