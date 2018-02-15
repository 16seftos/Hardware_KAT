Require Import hdl.

Record semantics (G C M : Type) : Type :=
  mkSemantics {
      at_external : C -> ee -> Prop;
      after_external : C -> C;
      step : G -> C*M -> C*M (*bigstep*)
    }.

Definition hdl_process : semantics st st env :=
  mkSemantics
    _ _ _
    guarded
    unguard
    (fun restart p => 
       let (c,m) := p in
       match interp m c with
       | (m', stskip) => (restart, m')
       | (m', c') => (c', m')
       end).
