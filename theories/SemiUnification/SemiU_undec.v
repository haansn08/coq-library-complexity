(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Result(s):
    Simple Semi-unification (SSemiU)
    Semi-unification (SemiU)
*)

(*
  Literature:
  [1] Andrej Dudenhefner. "Undecidability of Semi-Unification on a Napkin"
      5th International Conference on Formal Structures for Computation and Deduction (FSCD 2020): 9:1-9:16
      https://drops.dagstuhl.de/opus/volltexte/2020/12331
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.SemiUnification.SemiU.

Require Undecidability.SemiUnification.Reductions.CSSM_UB_to_SSemiU.
Require Undecidability.SemiUnification.Reductions.SSemiU_to_SemiU.
Require Import Undecidability.StackMachines.SSM_undec.

(* Undecidability of Simple Semi-unification *)
Theorem SSemiU_undec : undecidable SSemiU.
Proof.
  apply (undecidability_from_reducibility CSSM_UB_undec).
  exact CSSM_UB_to_SSemiU.reduction.
Qed.

Check SSemiU_undec.

(* Undecidability of Semi-unification *)
Theorem SemiU_undec : undecidable SemiU.
Proof.
  apply (undecidability_from_reducibility SSemiU_undec).
  exact SSemiU_to_SemiU.reduction.
Qed.

Check SemiU_undec.
