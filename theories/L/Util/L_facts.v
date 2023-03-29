Require Export Undecidability.L.Util.L_facts.
Require Import Complexity.L.Prelim.ARS.
Require Import Lia.

Definition evalIn i s t := s >(i) t /\ lambda t.

Notation "s '⇓(' l ')' t" := (evalIn l s t) (at level 50, format "s  '⇓(' l ')'  t").

Definition evalLe l s t := s >(<=l) t /\ lambda t.
Notation "s '⇓(<=' l ')' t" := (evalLe l s t) (at level 50, format "s  '⇓(<=' l ')'  t").

#[global]
Instance evalLe_eval_subrelation i: subrelation (evalLe i) eval.
Proof.
  intros ? ? [[? []] ?]. split. eapply pow_star_subrelation. all:eauto. 
Qed.

Lemma evalLe_evalIn s t k:
  s ⇓(<=k) t -> exists k', k' <= k /\ s ⇓(k') t.
Proof.
  unfold evalLe,redLe,evalIn. firstorder.
Qed.

Lemma evalIn_evalLe s t k k':
  k' <= k -> s ⇓(k') t -> s ⇓(<=k) t.
Proof.
  unfold evalLe,redLe,evalIn. firstorder.
Qed.

#[global]
Instance evalIn_evalLe_subrelation i: subrelation (evalIn i) (evalLe i).
Proof.
  intros s t (R & lt). split;[now exists i|trivial]. 
Qed.

#[global]
Instance evalLe_redLe_subrelation i: subrelation (evalLe i) (redLe i).
Proof.
  now intros ? ? [].
Qed.

#[global]
Instance evalIn_eval_subrelation i: subrelation (evalIn i) eval.
Proof.
  intros ? ? [?  ?]. split. eapply pow_star_subrelation. all:eauto. 
Qed.

#[global]
Instance le_evalLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) evalLe.
Proof.
  intros ? ? H' ? ? -> ? ? -> [H p].
  split. 2:tauto. now rewrite <- H'.
Qed.

Lemma evalIn_mono s t n n' :
  s ⇓(<=n) t -> n <= n' -> s ⇓(<=n') t.
Proof.
  intros ? <-. easy.
Qed.

Lemma evalIn_trans s t u i j :
  s >(i) t -> t ⇓(j) u -> s ⇓(i+j) u.
Proof.
  intros R1 [R2 lam].
  split; eauto using pow_trans.  
Qed.

Lemma evalle_trans s t u i j :
  s >(<=i) t -> t ⇓(<=j) u -> s ⇓(<=i+j) u.
Proof.
  intros R1 [R2 lam].
  split; eauto using redle_trans.  
Qed.

Lemma evalIn_unique s k1 k2 v1 v2 :
  s ⇓(k1) v1 -> s ⇓(k2) v2 -> k1 = k2 /\ v1 = v2.
Proof.
  intros (R1&L1) (R2&L2).
  eapply uniform_confluence_parameterized_both_terminal.
  all:eauto using lam_terminal,uniform_confluence.
Qed.

(* Helpful Lemmas*)

Lemma pow_trans_lam' t v s k j:
  lambda v -> pow step j t v -> pow step k t s  -> j>=k /\ pow step (j-k) s v.
Proof.
  intros lv A B.
  destruct (parametrized_confluence uniform_confluence A B) 
     as [m' [l [u [m_le_Sk [l_le_n [C [D E]]]]]]].
  cut (m' = 0).
  -intros ->. split. lia. replace (j-k) with l by lia. hnf in C. subst v. tauto. 
  -destruct m'; eauto. destruct C. destruct H. inv lv. inv H.
Qed.

Lemma evalle_trans_rev t v s k j:
  evalLe j t v -> pow step k t s  -> j>=k /\ evalLe (j-k) s v.
Proof.
  intros [(i&lti&R) lv] B.
  edestruct (pow_trans_lam' lv R B). split. lia. split. 2:tauto. eexists;split. 2:eauto. lia. 
Qed.

Lemma pow_trans_lam t v s k n :
  lambda v -> pow step n t v -> pow step (S k) t s  -> exists m, m < n /\ pow step m s v.
Proof.
  intros H1 H2 H3. edestruct (pow_trans_lam' H1 H2 H3) as (H'1&H'2). do 2 eexists. 2:eassumption. lia.
Qed.

Lemma powSk t t' s : t ≻ t' -> t' >* s -> exists k, pow step (S k) t s.
Proof.
  intros A B.
  eapply star_pow in B. destruct B as [n B]. exists n.
  unfold pow. simpl. econstructor. unfold pow in B. split; eassumption.
Qed.