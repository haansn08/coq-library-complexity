From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability Require Import L.Complexity.Cook.Prelim.
From Undecidability.L.Complexity.Cook Require Export PR.
Require Import Lia.

Record FlatPR := {
  Sigma : nat;
  offset : nat;
  width : nat;
  init : list nat;
  windows : list (PRWin nat);
  final : list (list nat);
  steps : nat
  }.

Definition list_ofFlatType (k : nat) (l : list nat) := forall a, a el l -> a < k.

Lemma list_ofFlatType_app (l1 l2 : list nat) (k : nat) : list_ofFlatType k (l1 ++ l2) <-> list_ofFlatType k l1 /\ list_ofFlatType k l2. 
Proof. 
  split; intros; unfold list_ofFlatType in *. 
  - setoid_rewrite in_app_iff in H. split; intros; apply H; eauto. 
  - destruct H as (H1 & H2); setoid_rewrite in_app_iff; intros a [ | ]; eauto. 
Qed. 

Definition PRWin_ofFlatType k (win : PRWin nat) := list_ofFlatType k (prem win) /\ list_ofFlatType k (conc win). 

Definition FlatPR_wellformed fpr := 
  width fpr > 0 
  /\ offset fpr > 0 
  /\ (exists k, k > 0 /\ width fpr = k * offset fpr)
  /\ length (init fpr) >= width fpr
  /\ (forall win, win el windows fpr -> PRWin_of_size win (width fpr)) 
  /\ (exists k, length (init fpr) = k * offset fpr)
  /\ list_ofFlatType (Sigma fpr) (init fpr) 
  /\ (forall s, s el final fpr -> list_ofFlatType (Sigma fpr) s)
  /\ (forall win, win el windows fpr -> PRWin_ofFlatType (Sigma fpr) win). 

Section fixParams. 
  Variable (Sigma : nat).
  Variable (offset : nat). 
  Variable (width : nat).
  Variable (windows : list (PRWin nat)). 
  Context (G0 : width > 0).

  (*validity of a rewrite *)
  (*we use a modified version that enforces (even in the case of vacuous rewrites which are unconstrained by the rewrite windows) that the resulting strings are strings over the finite alphabet *)
  (*(for the non-flat version, this is already enforced by typing) *)
  (*Inductive validFlat: list nat -> list nat -> Prop :=*)
  (*| validFlatB: validFlat [] [] *)
  (*| validFlatSA a b u v : validFlat a b -> length a < width - offset -> list_ofFlatType u Sigma -> list_ofFlatType v Sigma -> length u = offset -> length v = offset -> validFlat (u++ a) (v++ b)*)
  (*| validFlatS a b u v rule: validFlat a b -> list_ofFlatType u Sigma -> list_ofFlatType v Sigma -> length u = offset -> length v = offset -> rule el windows -> rewritesHead rule (u ++ a) (v ++ b) -> validFlat (u ++ a) (v ++ b). *)

  (*Lemma validFlat_length_inv a b : validFlat a b -> length a = length b. *)
  (*Proof.*)
    (*induction 1. *)
    (*- now cbn.*)
    (*- repeat rewrite app_length. firstorder. *)
    (*- repeat rewrite app_length; firstorder. *)
  (*Qed. *)
End fixParams. 

Definition FlatPRLang (C : FlatPR) := FlatPR_wellformed C 
  /\ exists (sf : list nat), list_ofFlatType (Sigma C) sf 
      /\ relpower (valid (offset C) (width C) (windows C)) (steps C) (init C) sf 
      /\ satFinal (offset C) (length (init C)) (final C) sf.

Section fixInstance.
  Variable (fpr : FlatPR). 
  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation windows := (windows fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  Context (A : FlatPR_wellformed fpr). 

  (*Lemma validFlat_multiple_of_offset a b : validFlat Sigma offset width windows a b -> exists k, |a| = k * offset. *)
  (*Proof. *)
    (*induction 1 as [ | ? ? ? ? ? IH | ? ? ? ? ? ? IH]. *)
    (*- exists 0. cbn; lia. *)
    (*- destruct IH as (k & IH). exists (S k). now rewrite app_length. *)
    (*- destruct IH as (k & IH). exists (S k). now rewrite app_length. *)
  (*Qed. *)

  Lemma app_length_split (X : Type) (v u b c : list X) : v ++ b = u ++ c -> |v| <= |u| -> exists u', u = v ++ u'. 
  Proof. 
    intros. apply list_length_split1 in H0 as (s1 & s2 & H0 & _ & ->). 
    rewrite <- app_assoc in H. apply app_eq_length in H as (-> & ->); [ | easy]. 
    now exists s2. 
  Qed. 

  Lemma p_invariant (p : list nat -> Prop) (a b : list nat) : 
    p a 
    -> (forall x y, p (x ++ y) <-> p x /\ p y) 
    -> |a| >= width 
    -> (forall x y u v rule, rewritesHead rule (u ++ x) (v ++ y) -> rule el windows -> |u| = offset -> |v| = offset -> p v)
    -> (forall rule, rule el windows -> p (conc rule))
    -> valid offset width windows a b 
    -> p b. 
  Proof. 
    intros H H0 H1 G1 G2 H2. induction H2. 
    - apply H.
    - rewrite app_length in H1. lia. 
    - rewrite app_length in H1. apply H0 in H. 
      destruct (le_lt_dec width (|a|)). 
      + apply H0. 
        split; [ | apply IHvalid; [ easy | lia]]. 
        clear IHvalid H2 l. 
        now eapply G1. 
      + clear IHvalid. clear G1. 
        destruct A as (_ & _ & (k & _ & A2) & _ & A6 & _ & _ & _ & A5).  
        specialize (A5 _ H5) as (A5 & A7). 
        specialize H6 as ((rest' & H6') & (rest & H6)). (*show rest = [] *)
        (*we need some structural assumptions *)
        assert (rest = []) as ->. 
        { 
          assert (|u ++ a| = width). 
          { 
            specialize (valid_multiple_of_offset H2) as (k1 & H1').
            rewrite app_length. rewrite A2 in *. 
            enough (k = S k1) by nia. nia. 
          }
          specialize (A6 _ H5) as (A6 & A6'). 
          assert (rest' = []) as ->. 
          { (*we now know: | u ++ a| = width, but also |prem (window rule')| = width *)
            destruct rule as (prem & conc); cbn in *. 
            rewrite H6', app_length, A6 in H7. destruct rest'; cbn in H7; [easy | nia]. 
          } 
          rewrite app_nil_r in H6'. 
          assert (|v ++ b| = |conc rule ++ rest|) by congruence. 
          rewrite !app_length in H8. rewrite app_length in H7. 
          apply valid_length_inv in H2. destruct rest; cbn in *; [easy | lia]. 
        }       
        rewrite app_nil_r in H6. rewrite H6. 
        now apply G2. 
  Qed. 

  Lemma valid_list_ofFlatType_invariant a b : 
    list_ofFlatType Sigma a -> |a| >= width -> valid offset width windows a b -> list_ofFlatType Sigma b. 
  Proof.
    intros H H0 H1. eapply (@p_invariant (list_ofFlatType Sigma)).
    - apply H. 
    - intros. apply list_ofFlatType_app. 
    - apply H0. 
    - intros. destruct H2 as (_ & (c & H2)). 
        destruct A as (_ & _ & A3 & _ & A1 & _ & _ & _ & A2). 
        specialize (A1 _ H3) as (_ & A1). specialize (A2 _ H3) as (_ & A2). 
        apply app_length_split in H2 as (u' & H2). 
        * rewrite H2 in A2. now apply list_ofFlatType_app in A2. 
        * destruct A3 as (ak & A3 & A4). nia.  
    - intros. destruct A as (_ & _ & _ & _ & _ & _ & _ & _ & A1). 
      apply A1 in H2 as (_ & H2). apply H2. 
    - apply H1. 
  Qed. 

  Lemma relpower_valid_list_ofFlatType_invariant steps a b: 
    list_ofFlatType Sigma a -> |a| >= width -> relpower (valid offset width windows) steps a b -> list_ofFlatType Sigma b. 
  Proof. 
    intros. induction H1; [easy | ]. 
    apply IHrelpower. eapply valid_list_ofFlatType_invariant, H1; [ apply H | ]. 
    - apply H0.  
    - apply valid_length_inv in H1. lia. 
  Qed. 
End fixInstance.
