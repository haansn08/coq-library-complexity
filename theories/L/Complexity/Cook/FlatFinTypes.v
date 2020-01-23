From PslBase Require Import FiniteTypes.
Require Import PslBase.FiniteTypes.BasicDefinitions.
Require Import Lia.
From Undecidability.L.Complexity.Cook Require Import Prelim.
Require Export smpl.Smpl. 

(*a finite type is represented by the number of its elements *)
Definition finRepr (X : finType) (n : nat) := n = length (elem X ). 
(*we just enumerate the elements starting at 0 *)
Definition finReprEl (X : finType) (n : nat) k (x : X) := finRepr X n /\ k < n /\ index x = k.  

(*a weaker version that does not explicitly enforce x to have a flat type *)
Definition finReprEl' (X : finType) (k : nat) (x : X) := index x = k. 

Lemma finReprEl_finReprEl' (X : finType) (n k : nat) (x : X) : finReprEl n k x -> finReprEl' k x.
Proof. unfold finReprEl, finReprEl'. easy. Qed.

(*for some of the proofs below, the stronger version of finReprEl is much more pleasant (e.g. for sum types)*)

Definition flatOption (n : nat) := S n.
Definition flatProd (a b : nat) := a * b.
Definition flatSum (a b : nat) := a + b.

Definition flatNone := 0.
Definition flatSome k := S k. 
Definition flatInl (k : nat) := k.
Definition flatInr (a: nat) k := a + k. 
Definition flatPair (a b : nat) x y := x * b + y. 

Smpl Create finRepr. 
Ltac finRepr_simpl := smpl finRepr; repeat smpl finRepr. 

Lemma finReprOption (X : finType) (n : nat) : finRepr X n -> finRepr (FinType (EqType (option X))) (flatOption n).
Proof. 
  intros. unfold finRepr in *. unfold flatOption; cbn -[enum]. rewrite H; cbn.
  rewrite map_length. reflexivity. 
Qed. 
Smpl Add (apply finReprOption) : finRepr.

Lemma finReprElSome (X : finType) n k x : finReprEl n k x -> @finReprEl (FinType (EqType (option X))) (flatOption n) (flatSome k) (Some x). 
Proof. 
  intros (H1 & H2 & H3). split; [ | split]; cbn in *.
  - now apply finReprOption. 
  - unfold flatSome, flatOption; lia. 
  - rewrite getPosition_map. 2: unfold injective; congruence. now rewrite <- H3. 
Qed. 
Smpl Add (apply finReprElSome) : finRepr.

Lemma finReprElNone (X : finType) n : finRepr X n -> @finReprEl (FinType (EqType (option X))) (flatOption n) flatNone None. 
Proof. 
  intros. split; [ | split]; cbn. 
  - now apply finReprOption.
  - unfold flatNone, flatOption. lia. 
  - now unfold flatNone. 
Qed. 
Smpl Add (apply finReprElNone) : finRepr. 

Lemma finReprSum (A B: finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (FinType (EqType (sum A B))) (flatSum a b). 
Proof. 
  intros. unfold finRepr in *. unfold flatSum; cbn in *.
  rewrite app_length. rewrite H, H0.
  unfold toSumList1, toSumList2. now rewrite !map_length.
Qed. 
Smpl Add (apply finReprSum) : finRepr. 

Lemma finReprElInl (A B : finType) (a b : nat) k x : finRepr B b -> finReprEl a k x -> @finReprEl (FinType (EqType (sum A B))) (flatSum a b) (flatInl k) (inl x). 
Proof. 
  intros H0 (H1 & H2 & H3). split; [ | split]. 
  - now apply finReprSum. 
  - now unfold flatInl, flatSum. 
  - unfold finRepr in H1. rewrite H1 in *. 
    clear H0 H1. cbn. unfold toSumList1, toSumList2, flatInl. 
    rewrite getPosition_app1 with (k := k).
    + reflexivity. 
    + now rewrite map_length. 
    + unfold index in H3. rewrite <- getPosition_map with (f := (@inl A B)) in H3. 2: now unfold injective.
      easy. 
Qed. 
Smpl Add (apply finReprElInl) : finRepr.

Lemma finReprElInr (A B : finType) (a b : nat) k x : finRepr A a -> finReprEl b k x -> @finReprEl (FinType (EqType (sum A B))) (flatSum a b) (flatInr a k) (inr x). 
Proof. 
  intros H0 (H1 & H2 & H3). split; [ | split ]. 
  - now apply finReprSum. 
  - now unfold flatInr, flatSum. 
  - unfold finRepr in H1; rewrite H1 in *. clear H1. 
    cbn. unfold toSumList1, toSumList2, flatInr. 
    rewrite getPosition_app2 with (k := k). 
    + rewrite map_length. unfold finRepr in H0. now cbn. 
    + now rewrite map_length.
    + intros H1. apply in_map_iff in H1. destruct H1 as (? & ? &?); congruence. 
    + unfold index in H3. rewrite <- getPosition_map with (f := (@inr A B)) in H3. 2: now unfold injective. 
      easy. 
Qed. 
Smpl Add (apply finReprElInr) : finRepr. 

Lemma finReprProd (A B : finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (FinType (EqType (prod A B))) (flatProd a b).  
Proof. 
  intros. unfold finRepr in *. unfold flatProd.
  cbn. now rewrite prodLists_length. 
Qed. 
Smpl Add (apply finReprProd) : finRepr.

Lemma finReprElPair (A B : finType) (a b : nat) k1 k2 x1 x2 : finReprEl a k1 x1 -> finReprEl b k2 x2 -> @finReprEl (FinType (EqType (prod A B))) (flatProd a b) (flatPair a b k1 k2) (pair x1 x2).
Proof. 
  intros (H1 & H2 & H3) (F1 & F2 & F3). split; [ | split]. 
  - now apply finReprProd. 
  - unfold flatPair, flatProd. nia. 
  - cbn. unfold flatPair. unfold finRepr in *. rewrite H1, F1 in *.
    rewrite getPosition_prodLists with (k1 := k1) (k2 := k2); eauto. 
Qed. 
Smpl Add (apply finReprElPair) : finRepr.

(*flattened lists *)
Definition isFlatListOf (X : finType) (l : list nat) (l' : list X) := l = map index l'.

Lemma isFlatListOf_cons (X : finType) (A : X) a l L: isFlatListOf (a :: l) (A :: L) <-> finReprEl' a A /\ isFlatListOf l L.
Proof. 
  unfold isFlatListOf in *. cbn. split; intros. 
  - inv H. easy. 
  - destruct H as (-> & ->). easy.
Qed. 

Lemma isFlatListOf_functional (X: finType) (L1 L2 : list X) (l : list nat) : 
  isFlatListOf l L1 -> isFlatListOf l L2 -> L1 = L2. 
Proof. 
  unfold isFlatListOf. intros. rewrite H0 in H. apply Prelim.map_inj in H; [easy | ].  
  intros a b H2. now apply injective_index, H2. 
Qed. 

Lemma isFlatListOf_injective (X : finType) (L : list X) (l1 l2 : list nat) :
  isFlatListOf l1 L -> isFlatListOf l2 L -> l1 = l2. 
Proof. 
  unfold isFlatListOf. intros. easy.
Qed. 

Lemma isFlatListOf_Some1 (T : finType) (T' : nat) (a : list nat) (b : list T) (n : nat) (x : nat):
  finRepr T T' -> isFlatListOf a b -> nth_error a n = Some x -> exists x', nth_error b n = Some x' /\ finReprEl T' x x'.
Proof. 
  intros. rewrite H0 in H1. rewrite utils.nth_error_map in H1. 
  destruct (nth_error b n); cbn in H1; [ | congruence ]. 
  inv H1. exists e.
  split; [reflexivity | repeat split]. 
  + apply H. 
  + rewrite H. apply index_le. 
Qed. 

Lemma seq_isFlatListOf (X : finType) : isFlatListOf (seq 0 (|elem X|)) (elem X).  
Proof. 
  unfold isFlatListOf. unfold index. rewrite dupfree_map_getPosition. 
  2: apply dupfree_elements. 
  now change (fun x => getPosition (elem X) x) with (getPosition (elem X)). 
Qed.

(*we define what it means for a number to be of a flat type *)
Definition ofFlatType (k : nat) (e : nat) := e < k. 
Definition list_ofFlatType (k : nat) (l : list nat) := forall a, a el l -> ofFlatType k a. 

Lemma list_ofFlatType_app (l1 l2 : list nat) (k : nat) : list_ofFlatType k (l1 ++ l2) <-> list_ofFlatType k l1 /\ list_ofFlatType k l2. 
Proof. 
  split; intros; unfold list_ofFlatType in *. 
  - setoid_rewrite in_app_iff in H. split; intros; apply H; eauto. 
  - destruct H as (H1 & H2); setoid_rewrite in_app_iff; intros a [ | ]; eauto. 
Qed. 

Lemma list_ofFlatType_cons x y k : list_ofFlatType k (x :: y) <-> ofFlatType k x /\ list_ofFlatType k y. 
Proof. 
  split; unfold list_ofFlatType; intros. 
  - split; [ apply H; eauto | intros; apply H; eauto]. 
  - destruct H0 as [-> | H0]. 
    + apply (proj1 H). 
    + apply (proj2 H), H0. 
Qed. 

(*given a representation of a finite type by natural numbers, we can restore original elements *)
Lemma finRepr_exists (X : finType) (x : nat) (a : nat) : 
  finRepr X x -> ofFlatType x a -> sigT (fun (a' : X) => finReprEl x a a'). 
Proof. 
  intros. unfold ofFlatType in H0. 
  assert (sigT (fun a' =>nth_error (elem X) a = Some a')) as (a' & H2).
  { 
    unfold ofFlatType in H0. rewrite H in H0.
    apply nth_error_Some in H0. destruct nth_error; easy. 
  } 
  exists a'. repeat split; [ easy | easy | ].
  unfold index. specialize (nth_error_nth H2) as <-.
  apply getPosition_nth. 
  + apply Cardinality.dupfree_elements. 
  + eapply utils.nth_error_Some_length, H2. 
Qed. 

Lemma finRepr_exists_list (X : finType) (x : nat) (l : list nat) : 
  finRepr X x -> list_ofFlatType x l -> sigT (fun (L : list X) => isFlatListOf l L). 
Proof. 
  revert x. induction l; intros.
  - exists []. unfold isFlatListOf. now cbn. 
  - apply list_ofFlatType_cons in H0 as (H0 & (L & H1)%IHl). 2: apply H.
    specialize (finRepr_exists H H0) as (a' & (_ & _ & H2)). 
    exists (a' :: L). unfold isFlatListOf. 
    now rewrite H1, <- H2. 
Qed. 
 
