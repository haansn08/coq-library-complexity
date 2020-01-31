From PslBase Require Import Base FiniteTypes. 
From Undecidability.L.Complexity.Cook Require Import Prelim.
Require Import Lia.

(** *Uniform homomorphisms *)

(*We define uniform homomorphisms (of strings): Given strings of the same length, they output strings of the same length.*)
Section fixX.
  Variable (X Y : Type). 

  Definition homomorphism (h : list X -> list Y) := forall x1 x2, h (x1 ++ x2) = h x1 ++ h x2. 

  Lemma homo_nil h : homomorphism h -> h [] = []. 
  Proof. 
    intros. unfold homomorphism in H. specialize (H [] []). 
    cbn in H; rewrite H. destruct (h []) eqn:Heqn; cbn; [ congruence | ].  
    assert (|y :: l| = |(y :: l) ++ y :: l|) as H0 by congruence. 
    cbn in H0. rewrite app_length in H0. cbn in H0; lia. 
  Qed. 

  Lemma homo_cons h x l : homomorphism h -> h (x::l) = h [x] ++ h l.
  Proof. 
    intros. replace (x :: l) with ([x] ++ l) by now cbn. apply H. 
  Qed.

  Lemma homo_concat h : homomorphism h -> forall x, h (concat x) = concat (map h x). 
  Proof. 
    intros. induction x. 
    - cbn. apply homo_nil, H. 
    - cbn. rewrite H. now rewrite IHx. 
  Qed. 

  (*given an arbitrary function mapping elements of X into strings over Y, we can derive a homomorphism in a canonical way*)
  Definition canonicalHom (h' : X -> list Y) := fun (l : list X) => concat (map h' l). 
  Lemma canonicalHom_is_homomorphism h' : homomorphism (canonicalHom h'). 
  Proof. 
    unfold homomorphism. intros. unfold canonicalHom. 
    now rewrite map_app, concat_app. 
  Qed. 

  Lemma canonicalHom_is_unique h' : forall h'', homomorphism h'' ->  (forall x, h'' [x] = h' x) -> forall x, h'' x = canonicalHom h' x. 
  Proof. 
    intros. induction x. 
    - cbn. erewrite homo_nil; easy.
    - erewrite homo_cons; [ | easy]; cbn. rewrite IHx. now rewrite H0. 
  Qed. 

  (** uniform homomorphisms *)

  (*a uniform homomorphism is ε-free and maps all strings of the same length to strings of the same length *)
  (*(stated differently: |h x| = n * |x| for n > 0)*)
  Definition uniform_homomorphism (h : list X -> list Y) := 
    homomorphism h 
    /\ (forall x y, |h [x]| = |h [y]|) 
    /\ (forall x, |h[x]| >= 1).

  Lemma unif_homo_length h x y : uniform_homomorphism h -> |x| = |y| -> |h x| = |h y|. 
  Proof. 
    intros (H1 & H2 & _). 
    revert y. induction x; intros. 
    - destruct y; cbn in *; [ | congruence]. now cbn. 
    - destruct y; cbn in *; [ congruence | ]. 
      replace (a :: x) with ([a] ++ x) by now cbn. replace (x0 :: y) with ([x0] ++ y) by now cbn. 
      rewrite !H1. rewrite !app_length. erewrite H2 with (y := x0). 
      rewrite IHx with (y := y); eauto. 
  Qed. 

  Variable (h : list X -> list Y). 
  Context (h_unifHom : uniform_homomorphism h). 
  Lemma h_nil_cons x l : not (|h []| = |h (x :: l)|). 
  Proof. 
    intros H. replace (x ::l) with ([x] ++ l) in H by now cbn.
    rewrite (proj1 h_unifHom) in H. rewrite (homo_nil (proj1 h_unifHom)) in H. 
    rewrite !app_length in H. cbn in H.  
    specialize (proj2 (proj2 h_unifHom) x). lia.
  Qed. 

  Lemma h_length_inv l1 l2 : |h l1| = |h l2| -> |l1| = |l2|. 
  Proof. 
    revert l2. induction l1; intros. 
    + destruct l2; [easy | now apply h_nil_cons in H].  
    + destruct l2; [ symmetry in H; now apply h_nil_cons in H | ]. 
      cbn. f_equal. apply IHl1. 
      rewrite homo_cons in H; [ | apply h_unifHom]. 
      rewrite homo_cons with (x := x) in H; [ | apply h_unifHom].
      rewrite !app_length in H.
      rewrite (proj1 (proj2 h_unifHom)) with (y := x) in H. lia. 
  Qed. 

  Lemma h_length_inv' l1 l2 : h l1 = h l2 -> |l1| = |l2|. 
  Proof. intros; now apply h_length_inv. Qed. 

  Lemma h_nil_inv a : h a = [] -> a = []. 
  Proof. 
    intros H. destruct a; [ easy | ]. replace (x ::a) with ([x] ++ a) in H by now cbn.
    rewrite (proj1 h_unifHom) in H.  apply list_eqn_length in H. rewrite app_length in H. 
    specialize (proj2 (proj2 h_unifHom) x). cbn in H; lia.
  Qed. 
End fixX. 


