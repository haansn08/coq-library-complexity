(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** A Coq computable reduction from n-registers MM termination
    to 2-registers MMA termination. Beware that the semantics
    of MMA is a bit different than the semantics of MM: 

       the DEC instruction jumps when not zero instead of when zero 

    Compare mm_sss  (ILL/Mm/mm_defs.v)
    and     mma_sss (MM/mma_defs.v)                   

    The reduction goes via regular FRACTRAN termination *)

Require Import Undecidability.ILL.Definitions.

From Undecidability.Shared.Libs.DLW Require Import Utils.utils Vec.pos Vec.vec.
From Undecidability.ILL.Code Require Import sss.
From Undecidability.H10 Require Import Fractran.fractran_defs MM_FRACTRAN.
From Undecidability.MM Require Import mma_defs fractran_mma.

Set Implicit Arguments.

Local Notation "P /MMA/ s ↓" := (sss_terminates (@mma_sss 2) P s) (at level 70, no associativity). 

Theorem fractran_reg_mma2 l : 
          Forall (fun c => snd c <> 0) l
       ->   { Q : list (mm_instr (pos 2)) 
            | forall x, l /F/ x ↓ <-> (1,Q) /MMA/ (1,x##0##vec_nil) ↓ }.
Proof.
  intros Hl.
  exists (fractran_reg_mma l).
  apply fractran_reg_mma_reduction; auto.
Qed.

Section FRACTRAN_REG_MMA2.

  Let f : FRACTRAN_REG_PROBLEM -> MMA2_PROBLEM.
  Proof.
    intros (l & x & Hl).
    destruct (fractran_reg_mma2 Hl) as (Q & HQ).
    exact (Q, (x##0##vec_nil)).
  Defined.

  Theorem FRACTRAN_REG_MMA2_HALTING : FRACTRAN_REG_HALTING ⪯ MMA2_HALTING.
  Proof.
    exists f. 
    intros (l & x & Hl); simpl.
    destruct (fractran_reg_mma2 Hl) as (Q & HQ); apply HQ.
  Qed.

End FRACTRAN_REG_MMA2.

Check FRACTRAN_REG_MMA2_HALTING.
Print Assumptions FRACTRAN_REG_MMA2_HALTING.
