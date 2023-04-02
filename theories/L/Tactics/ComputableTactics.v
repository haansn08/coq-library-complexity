Require Export Undecidability.L.Tactics.ComputableTactics.
Require Import Complexity.L.Tactics.ComputableTime.

Require Import MetaCoq.Template.All.

Ltac infer_instancesT :=
  repeat match goal with
         | [ |- context [ int_ext ?t ] ] => first [change (int_ext t) with (extT t) | fail 3 "Could not fold extT-instance for " t]
         | [ |- context [ ext ?t ] ] => first [change (ext t) with (extT t) | fail 3 "Could not fold extT-instance for " t]
         end.

Ltac computable_using_noProof Lter:=
  once lazymatch goal with
  | [ |- computable ?t ] => Undecidability.L.Tactics.ComputableTactics.Intern.computable_using_noProof Lter
  | [ |- computableTime ?t _] =>
    eexists Lter;unfold Lter;try clear Lter;
    let t' := (eval hnf in t) in
    let h := Undecidability.L.Tactics.ComputableTactics.Intern.visibleHead t' in
    try unfold h; Undecidability.L.Tactics.ComputableTactics.Intern.computable_prepare t; infer_instancesT
  end.

Tactic Notation "computable" "using" open_constr(Lter) :=
  computable_using_noProof Lter;repeat Undecidability.L.Tactics.ComputableTactics.Intern.cstep.

Tactic Notation "extract" "constructor":=
  let term := fresh "used_term" in
        once lazymatch goal with
        | [ |- computable ?t ] => extract constructor
        | [ |- computableTime ?t _] =>
          run_template_program (tmExtractConstr' None t)
                               (fun e =>  pose (term:= ( e : extracted t)); computable using term)
   end.
