Require Import ZArith Integers String.
Require Import FMapWeakList.
Require Import lang syntax.
Set Implicit Arguments.
Require Import List.
Import ListNotations.
Require Import Coq.extraction.ExtrHaskellString.
Open Scope string_scope.
(* Will generate haskell with a main that outputs verilog *)
(* Currently need to make sure that inputs are not used in the 
   left hand side of an assignment statement. *)
(* Not matching on assign_kind until it's made clear how it works
   inside an always block *)
   
Module stringdec <: DecidableType.DecidableType.
  Definition t := string.
  Definition eq : t -> t-> Prop := Logic.eq.
  Lemma eq_refl : forall x : t, eq x x.
  Proof. reflexivity. Qed.
  Lemma  eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. apply CRelationClasses.eq_Symmetric. Qed.
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. apply CRelationClasses.eq_Transitive. Qed.
  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. apply string_dec. Qed.
End stringdec.

(* Maintain a map of id to the id's var_kind and type *)
Module state_map := FMapWeakList.Make stringdec.
Definition state := state_map.t (var_kind*ty).
Definition verilog := string.

Definition newline : string := String (Ascii.Ascii false true false true false false false false) EmptyString.

(* Some axioms to turn numbers into strings 
   should probably eventually do it in coq *)
(* Haskells Int *)
Axiom prelInt : Type.
Axiom Z_to_prelInt : Z -> prelInt.
Axiom int_of_ps : positive -> prelInt.
Axiom show : prelInt -> string.
Axiom nat_to_prelInt : nat -> prelInt.
Axiom IO : Type.
Axiom main : IO.

Definition Z_to_string (z : Z) : string :=
  match z with
  | Zneg p => (show (Z_to_prelInt z))
  | _ => (show (Z_to_prelInt z))
  end.

Definition verilog_of_binop (b : binop) : verilog :=
  match b with
  | OAnd => "&"
  | OSub => "-"
  | OXor => "^"
  | OAdd => "+"
  | OShr => ">>>"
  | OShru => ">>"
  | OShl => "<<<"
  | OOr => "|"
  | OEq => "=="
end.

Fixpoint verilog_of_exp (ty_exp : ty) (e : exp ty_exp) (st : state):
  (verilog * state) :=
  match e with
  | EVal bv => (Z_to_string (Int64.intval bv), st)
  | EVar t id1 => (id1, st)
  | EDeref N t N_iN idtarr =>
    let verilog1 := idtarr ++ "[" ++ (show (nat_to_prelInt N_iN))
                           ++ "] " in 
    (verilog1, st)
  | EBinop b exp1 exp2 =>
    let (verilog1, st1) := (verilog_of_exp exp1 st) in
    let (verilog2, st2) := (verilog_of_exp exp2 st1) in 
       ("(" ++ (verilog1)
            ++ " " ++ (verilog_of_binop b) ++ " " 
            ++ (verilog2) ++ ")", st2)
  | ENot (ENot exp1) => verilog_of_exp exp1 st         
  | ENot exp1 => let (verilog1, st') := verilog_of_exp exp1 st in 
                 ("~" ++ verilog1, st')
  end.

Definition enum_iN (lo N : nat) : list (iN N) :=
  List.filter
    (fun i => negb ((proj1_sig (Fin.to_nat i)) <? lo))
    (Vector.to_list (vector_keymap (Vector.const O N) (fun ix _ => ix))).

Program Fixpoint verilog_of_stmt (s : stmt) (st : state)
  : (verilog *state) :=
  match s with
  | SAssign a_kind id1 exp1 =>
    let (verilog1, st1) := (verilog_of_exp exp1 st) in
    (" " ++ id1 ++ " = " ++ (verilog1) ++ ";" ++ newline, st1)
  | SUpdate kind N id1 inN exp1 =>
    let (verilog1, st1) := (verilog_of_exp exp1 st) in
    (" " ++ id1++"["++(show (nat_to_prelInt inN)) ++ "]"++" = "++
         (verilog1) ++ ";" ++ newline, st1)
  | SSeq s1 s2 => 
    let (verilog1, st1) := (verilog_of_stmt s1 st) in
    let (verilog2, st2) := (verilog_of_stmt s2 st1) in 
    (verilog1 ++ verilog2 ++ newline, st2)
  | SITE e c1 c2 =>
    let (ve, st0) := verilog_of_exp e st in
    let (vc1, st1) := verilog_of_stmt c1 st0 in
    let (vc2, st2) := verilog_of_stmt c2 st1 in
    ("if (" ++ ve ++ ")" ++ newline ++
            "begin" ++ newline ++ vc1 ++ "end" ++ newline ++
            "else begin" ++ newline ++ vc2 ++ "end" ++ newline,
     st2)
  | SIter lo hi f => 
    List.fold_right
      (fun elt (acc : (verilog*state)) =>
         let (v_acc, st_acc) := acc in 
         let (verilog1, st') := (verilog_of_stmt (f elt) st_acc) in
         (v_acc ++ verilog1, st')) 
      ("", st) (enum_iN lo hi) 
  | SSkip => ("", st)
  end.

Program Fixpoint verilog_of_prog (p : prog) (st : state)
  : (verilog*state) :=
  match p with
  | VDecl kind id1 bv p' =>
    let (verilog1, st') := (verilog_of_prog p' st) in
    (match kind with
    | Input => (verilog1, state_map.add id1 (kind,TVec64) st')
    | _ => 
      let decl := " " ++ id1 ++ " = " ++
      (show (Z_to_prelInt (Int64.intval bv))) ++ ";" ++ newline in
      (decl ++ verilog1, state_map.add id1 (kind,TVec64) st')
    end)
  | ADecl kind N t id1 p' =>
    let (verilog1, st') := (verilog_of_prog p' st) in
    (verilog1, state_map.add id1 (kind, TArr N t) st')
  | PStmt stmt1 => verilog_of_stmt stmt1 st
  | PSeq p1 p2 => 
    let (verilog1, st1) := verilog_of_prog p1 st in 
    let (verilog2, st2) := verilog_of_prog p2 st1 in
    (verilog1 ++ verilog2, st2)
  | PDone => ("",st)
  end.

Definition verilog_of_kind (x : var_kind) : verilog :=
  match x with
  | Local => " "
  | Input => "input"
  | Output => "output"
  end.

(* This might need to be looked at to get the correct verilog datatypes*)
Definition verilog_of_ty (x : (string*ty)) : verilog :=
  match x with
  | (s,TVec64) => "[63:0] " ++ s 
  | (s,TArr N t) => "[" ++ show (nat_to_prelInt (N - 1)) ++":" ++ "0" ++ "] [63:0] " ++ s
  end.

Definition foldI (st : state) : list string :=
  state_map.fold
    (fun key (elt : (var_kind*ty)) acc =>
       let (kind,ty1) := elt in
       match kind with
       | Local => acc 
       | _ =>
         if string_dec key "" then acc else key :: acc
    end) st [].

Definition verilog_of_args' (xs : list string)
  : string :=
  match xs with
  | [] => ""
  | [x] => x 
  | x :: xs' =>
    List.fold_left
      (fun acc elt =>
         if string_dec elt "" then acc else
         acc ++ ", " ++ elt) xs'
      x
  end.


(* Gets a list of id's id1,id2,...,idn *)
Definition verilog_of_args (st : state) : verilog :=
  verilog_of_args' (foldI st).

(* Defines var_kind and datatype for each id used in the program *)
(* input id1;
   output id2;
   'Since we are doing things sequentially a reg needs to be created for 
   variables that can be assigned to'
   reg id2; 
   reg id3;'a Local id'
 *)
Definition Declarations (st : state) : verilog :=
  state_map.fold
    (fun key (elt : (var_kind*ty)) acc =>
       let (kind,ty1) := elt in
       let decl :=
           acc ++ verilog_of_kind kind ++  " "
               ++ verilog_of_ty (key,ty1) 
               ++ ";" ++ newline in 
       (match kind with
       | Local => acc ++ "reg " ++ verilog_of_ty (key,ty1)
                        ++ ";" ++ newline
       | Input => decl
       | Output => decl ++ "reg " ++ verilog_of_ty (key,ty1)
                        ++ ";" ++ newline
                        
       end)) st "".

Definition TbDeclarations (st : state) : verilog :=
  state_map.fold
    (fun key (elt : (var_kind*ty)) acc =>
       let (kind,ty1) := elt in
       let decl :=
           acc ++  "reg "
               ++ verilog_of_ty (key,ty1)
               ++ ";" ++ newline in
       (match kind with
       | Local => acc 
       | Input => decl
       | Output => acc ++ "wire " ++ verilog_of_ty (key,ty1)
                        ++ ";" ++ newline
                        
       end)) st "".

Definition pretty_print (name: verilog) (p : prog) : verilog :=
  let (v,st) :=
      verilog_of_prog p (state_map.empty (var_kind*ty)) in
  "module " ++ name ++"(" ++ (verilog_of_args st) ++ ");" ++ newline
            ++  Declarations st  
            ++ "always @(*)" ++ newline ++ "begin" ++ newline ++
            v ++ newline ++ "end" ++ newline ++ "endmodule" ++ newline.

Definition default_inst (id : string) (t : ty) :=
  match t with
  | TVec64 => " " ++ id ++ "= 16;"
  | TArr N t =>
    " for(i=0;i<" ++ show (nat_to_prelInt N) ++ ";i=i+1) begin"
    ++ newline ++ "  " ++ id ++ "[i] = i % 10 +1 * 20;" ++ newline ++ " end"
  end.

Inductive Pass : Type := OneDecl | TwoOutput.

Definition default_insts (st : state) (pass : Pass) : verilog :=
  (state_map.fold
      (fun key (elt : (var_kind*ty)) acc =>
         let (kind,ty1) := elt in
         match pass with
         | OneDecl => 
           (match kind with
            | Input => 
              (match ty1 with
               | TVec64 => acc ++ (default_inst key ty1) ++ newline
               | TArr N t => acc ++ (default_inst key ty1) ++ newline
               end)
            | _ => acc
            end)
         | TwoOutput =>
           (match kind with
            | Output => 
              (match ty1 with
               | TVec64 =>
                 acc ++ "#10 " ++ newline ++
                     "  $display (""Value of " ++ key ++
                     " is %d ""," ++ key ++ ");"
               (* ++ (default_inst key ty1) ++ newline *)
               | TArr N t =>
               acc ++ "# 10" ++ newline ++
                   " for (i = 0; i <"
                   ++ show (nat_to_prelInt N) ++
                   "; i=i+1) begin" ++ newline
                 ++ "  $display (""Value at location %g is %d "", i,"
          ++  key ++ "[i]);"
                 ++ newline ++ " end"
               end)
            | _ => acc
            end)
         end) st "").

(* This got really messy I'll try to clean it up sometime. *)
Definition pretty_print_tb_results (name : verilog)
           (Expected : string) (p : prog) : verilog :=
  let (v,st) :=  verilog_of_prog p (state_map.empty (var_kind*ty)) in
  "module " ++ name ++ "_tb();" ++  newline ++ (TbDeclarations st)
   ++ name ++ " " ++ name ++ "1"
   ++ "("  ++ (verilog_of_args st) ++ ");" ++ newline ++
   (* "// Make some instantiation here is a default" ++ newline ++ *)
   (* "integer i;" ++ newline ++ *)
   "initial begin" ++ newline
   ++ default_insts st OneDecl ++ newline
   ++ default_insts st TwoOutput ++ newline ++
   "  $display (""Expected Results of Testbench: " ++ Expected ++ """);"
   ++ newline ++ "end" ++ newline ++ "endmodule" ++ newline
   ++ pretty_print name p.
   
Definition pretty_print_tb (name : verilog)
           (p : prog) : verilog :=
  let (v,st) :=  verilog_of_prog p (state_map.empty (var_kind*ty)) in
  "module " ++ name ++ "_tb();" ++  newline ++ (TbDeclarations st)
   ++ name ++ " " ++ name ++ "1"
   ++ "("  ++ (verilog_of_args st) ++ ");" ++ newline ++
   (* "// Make some instantiation here is a default" ++ newline ++ *)
   (* "integer i;" ++ newline ++ *)
   "initial begin" ++ newline
   ++ default_insts st OneDecl ++ newline
   ++ default_insts st TwoOutput ++ newline
   ++ "end" ++ newline ++ "endmodule" ++ newline
   ++ pretty_print name p.

(* Haskell implementation of axioms *)
Extract Constant prelInt => "Prelude.Int".
Extract Constant show => "Prelude.show".
Extract Constant nat_to_prelInt =>
"(\n -> 
     case n of {
       O -> 0;
       S n' -> 1 Prelude.+ (nat_to_prelInt n');
})".

Extract Constant int_of_ps =>
"(\p ->
  case p of {
    XI p0 -> 2 Prelude.* (int_of_ps p0) Prelude.+ 1;
    XO p0 -> 2 Prelude.* (int_of_ps p0);
    XH -> 1})".

(* This could be made to look nicer once I figure out the right
   indentation Scheme *)
Extract  Constant Z_to_prelInt =>
"let { int_of_ps p =   (case p of { XI p0 -> 2 Prelude.* (int_of_ps p0) Prelude.+ 1; XO p0 -> 2 Prelude.* (int_of_ps p0); XH -> 1})} in (\z -> case z of {  Z0 -> 0;    Zpos p ->  (int_of_ps p); Zneg p -> - (int_of_ps p); })".


Extraction Language Haskell.
(* The haskell extraction library doesn't have this defined *)
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Constant IO => "Prelude.IO ()".

