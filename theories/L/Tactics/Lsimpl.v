Require Export Undecidability.L.Tactics.Lsimpl.
From Undecidability.L.Tactics Require Import Lbeta Lrewrite.

Require Import Complexity.L.Util.L_facts.
Import L_Notations.

(*Lsimpl that uses correctnes lemmas*)
Ltac Lsimpl_old :=intros;
  once lazymatch goal with
  | |- _ >(<= _ ) _ => Lreduce;try Lreflexivity
  | |- _ ⇓(_ ) _ => repeat progress Lbeta;try Lreflexivity
  | |- _ ⇓(<= _ ) _ => Lreduce;try Lreflexivity
  | |- _ >(_) _ => repeat progress Lbeta;try Lreflexivity
  | |- _ >* _ => Lreduce;try Lreflexivity (* test *)
  | |- eval _ _ => Lreduce;try Lreflexivity (* test *) 
  (*| |- _ >* _  => repeat Lsimpl';try reflexivity'
  | |- eval _ _  => repeat Lsimpl';try reflexivity'*)
  | |- _ == _  => repeat Lsimpl';try reflexivity'
  end.

Ltac Lsimpl :=
  lazymatch goal with
  | |- _ >( _ ) _ => Lsimpl_old
  | |- _ => LrewriteSimpl
  end.