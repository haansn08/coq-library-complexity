From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic LinTimeDecodable Tactics Problems.LGraph.
From Undecidability.L.Functions Require Import Size.


(* k-Clique: duplicate-free list of k nodes such that all pairwise-distinct nodes are connected *)
Inductive isClique (g : UndirectedGraph) : list (Fin.t (V g)) -> nat -> Prop :=
| isCliqueB : isClique [] 0
| isCliqueS (cl : list (Fin.t (V g))) (node : Fin.t (V g)) (k : nat):
    isClique cl k -> (not (node el cl)) -> (forall (node' : Fin.t (V g)), node' el cl -> E node node') -> isClique (node :: cl) (S k).

Definition Clique (input : UndirectedGraph * nat) :=
  let (g, k) := input in exists cl, @isClique g cl k. 

Inductive isLClique (g : Lgraph) : list Lnode -> nat -> Prop :=
| isLCliqueB : isLClique g [] 0
| isLCliqueS (cl : list Lnode) (node : Lnode) (k : nat) : isLClique g cl k ->
    (not (node el cl)) -> Lgraph_node_in_dec g node = true -> (forall (node' : Lnode), node' el cl -> Lgraph_edge_in_dec g node node' = true) -> isLClique g (node :: cl) (S k).                                                     

Definition LClique (input : Lgraph * nat) :=
  let (g, k) := input in exists cl, @isLClique g cl k. 

Definition LClique_verifier (input : Lgraph * nat) (cert : list Lnode) :=
  let (g, k) := input in isLClique g cert k. (*this includes that l is short enough*)

Lemma isLClique_node_in (g : Lgraph) (k : nat) (cl : list Lnode) : isLClique g cl k -> forall n, n el cl -> Lgraph_node_in_dec g n = true. 
Proof.
  induction 1. 
  -intros n [].
  - intros n [-> | H3]. apply H1. now apply IHisLClique. 
Qed. 

Lemma isLClique_length (g : Lgraph) (k : nat) (cl : list Lnode) : isLClique g cl k -> k = (|cl|).
Proof. induction 1; now cbn. Qed. 


Lemma size_nat_enc_mono (n  :nat) (m : nat) :
  n <= m -> size (enc n) <= size(enc m). 
Proof. 
  intros H; repeat rewrite size_nat_enc. lia. 
Qed. 

Fixpoint connectedb (g : Lgraph) (cl : list Lnode) :=
  match cl with [] => true
           | (n :: cl) => forallb (Lgraph_edge_in_dec g n) cl && connectedb g cl
  end. 

(*TODO: maybe factor out the 2nd induction*)
Lemma connectedb_correct (g : Lgraph) (cl : list Lnode) : dupfree cl -> connectedb g cl = true <-> forall u v, u <> v -> u el cl -> v el cl -> Lgraph_edge_in_dec g u v = true. 
Proof. 
  intros F0. 
  destruct g. induction cl. 
  + cbn. tauto. 
  + split; cbn.
  - intros H%andb_prop; destruct H as [F1 F2]. intros u v neq [H1 | H1] [H2 | H2].
    * congruence.
    * rewrite H1 in *; clear H1.
      apply (proj1 (forallb_forall (Lgraph_edge_in_dec (n, l) u) cl) F1 v H2 ).
    * rewrite H2 in *; clear H2.
      specialize (proj1 (forallb_forall (Lgraph_edge_in_dec (n, l) v) cl) F1 u H1) as H0.
      apply Lgraph_edge_in_dec'_correct. apply Lgraph_edge_in_dec'_correct in H0. tauto.
    * inv F0. apply IHcl; tauto. 
  - intros H. apply utils.andb_and; split.
    2: {apply IHcl. firstorder. now inv F0. firstorder. }
    clear IHcl. induction cl. reflexivity. 
    cbn. apply utils.andb_and; split.
    2: {inv F0. inv H3. assert (dupfree (a :: cl)). constructor. firstorder. apply H5. apply IHcl;firstorder. }
    apply H. inv F0. 1-2: firstorder. right; left; reflexivity. 
Qed. 

Definition LClique_verifierb (g : Lgraph) (k : nat) (cl : list Lnode) :=
  forallb (Lgraph_node_in_dec g) cl && dupfreeb Nat.eqb cl && connectedb g cl && Nat.eqb (|cl|) k.   

Definition nat_eqb_correct := (fun a b => conj (proj2 (Nat.eqb_eq a b)) (proj1 (Nat.eqb_eq a b))). 

Lemma LClique_verifierb_correct (g : Lgraph) (k : nat) (cl : list Lnode) :
  reflect (isLClique g cl k) (LClique_verifierb g k cl). 
Proof.
  destruct LClique_verifierb eqn:H; constructor.
  - unfold LClique_verifierb in H; simp_bool.
    revert k H1; induction cl; intros k H1; cbn in H1; destruct k; try discriminate H1; constructor.
    + apply IHcl.
      * cbn in H0;simp_bool; tauto. 
      * cbn in H3; simp_bool; tauto. 
      * cbn in H2; simp_bool; tauto. 
      * apply H1. 
    + specialize (dupfreeb_correct nat_eqb_correct (a::cl)) as H; inv H.
      -- symmetry in H4. simp_bool. intros H7.
         apply (list_in_decb_iff nat_eqb_correct) in H7. congruence.
      -- exfalso. simp_bool. cbn in H3; simp_bool. cbn in H3; simp_bool. 
    + cbn in H0. simp_bool. 
    + assert (dupfree (a::cl)) by ( now apply (proj1 (dupfreeb_iff nat_eqb_correct (a::cl)))).
      specialize (connectedb_correct g H) as [H4 _]. specialize (H4 H2). 
      intros b H5. apply H4. intros ->. now inv H. now left. now right. 
  - intros H0; induction H0. now cbn in H. 
    apply IHisLClique. clear IHisLClique. unfold LClique_verifierb in H.
    simp_bool; cbn in H; simp_bool.
    all: unfold LClique_verifierb; simp_bool; try tauto.
    + apply (list_in_decb_iff) in H. tauto. apply nat_eqb_correct.   
    + exfalso. specialize (forallb_forall (Lgraph_edge_in_dec g node) cl) as H4.
      now apply H4 in H3.  
Qed. 

From Undecidability.L.Complexity Require Import PolyBounds ONotation Monotonic. 

(*extraction of needed functions and derivation of runtime bounds in terms of encoding size*)

  Fixpoint connectedb_time (g : Lgraph) (cl : list Lnode) :=
    let (n, e) := g in 
    match cl with [] => 4
                | (cl :: cls) => forallb_time
   (fun (v : Lnode) (_ : unit) =>
    (list_in_decb_time pair_eqb_nat_time e (cl, v) +
     list_in_decb_time pair_eqb_nat_time e (v, cl) + 29, tt)) cls + 19 + connectedb_time g cls
              end. 

Instance term_connectedb : computableTime' connectedb (fun g _ => (5, fun cl _ => (connectedb_time g cl, tt))).
Proof.
  extract. 
  solverec. 
Qed. 

Lemma connectedb_time_bound : exists (f : nat -> nat), (forall (g : Lgraph) (cl : list Lnode), connectedb_time g cl <= f (size(enc g) + size(enc cl))) /\ inOPoly f /\ monotonic f.
Proof.
  pose (forallb_step_t := fun (e : list Ledge) (cl_check : nat) => (fun (v : nat) (_ : unit) =>
            (list_in_decb_time pair_eqb_nat_time e (cl_check, v) + list_in_decb_time pair_eqb_nat_time e (v, cl_check) + 29, tt))).
  specialize (list_in_decb_time_bound pair_eqb_nat_time_bound) as (fin & H1 & H2 & H3). 
  (* specialize (forallb_time_bound) *)
  evar (f : nat -> nat). exists f. split.
  - intros g cl. unfold connectedb_time.

Admitted.  

Definition Lclique_verifierb_time (g : Lgraph) (k:nat) (cl : list Lnode):= forallb_time (fun n _ => (33 + 14 * n, tt)) cl
  + dupfreeb_time (fun x _ => (5, fun y _ => (min x y * 17 + 9, tt))) cl
  + connectedb_time g cl + 11 * (|cl|) + 17 * min (|cl|) k + 53.

Instance term_LClique_verifierb : computableTime' LClique_verifierb (fun g _ => (1, fun k _ => (1, fun cl _ => (Lclique_verifierb_time g k cl, tt)))). 
Proof.
  extract. 
  solverec. unfold Lclique_verifierb_time. solverec. 
Qed. 

Lemma Lclique_verifierb_time_bound : exists (f : nat -> nat) , (forall (g: Lgraph) (k : nat) (cl : list Lnode), Lclique_verifierb_time g k cl <= f(size(enc g) + size(enc k) + size(enc cl))) /\ inOPoly f /\ monotonic f. 
Proof.
Admitted. 
                 
Lemma clique_inNP : inNP LClique. 
Proof.
  apply (inNP_intro) with (R:= LClique_verifier).
  1: { apply linDec_polyTimeComputable. }
  3 : {
    intros [g k]; split.
    - destruct g. intros (cert & H1). exists cert. easy.  
    - intros (cert & H). now exists cert. 
  }
  2 : {
    evar (f' : nat -> nat). 
    exists f'. split. 2: split. 
    2: {
      intros [g k] cert H. cbn in H.
      assert (k = (|cert|)) by (now apply isLClique_length with (g:= g)).
      rewrite H0 in *; clear H0 k. rewrite size_prod; cbn [fst snd].
      rewrite size_nat_enc. rewrite size_list.
      (*LHS is in O(max_node * |cert|) *)
      specialize (isLClique_node_in H) as H2. 
      unfold Lgraph_node_in_dec in H2. destruct g.
      assert (sumn (map (fun (x : nat ) => size (enc x) + 5) cert) <= (size(enc n) + 5) * (|cert|)).
      - induction cert. cbn; lia.
        cbn. assert (a <= n).
        { assert (Lgraph_node_in_dec (n, l) a = true ).
          apply isLClique_node_in with (k:= |a::cert|) (cl:= a::cert); easy.
          cbn in H0. destruct n. congruence. dec_bool. lia.
        }
        apply size_nat_enc_mono in H0. rewrite H0. rewrite IHcert. solverec.
        now inv H. firstorder. 
      - rewrite H0. rewrite size_prod with (w := (n, l)); cbn [fst snd].
        instantiate (f' := fun n => 4 * n * n). subst f'.
        solverec.
    }
    all: (subst f'; smpl_inO).
  }

  destruct (Lclique_verifierb_time_bound) as (f' & H1 & H2 & H3).
  evar (f : nat -> nat). exists f. split; try split.
  - exists (fun inp => match inp with ((g, k), cert) => LClique_verifierb g k cert end).
    split.
    + constructor. extract. solverec.
      repeat (rewrite size_prod; cbn [fst snd]).
      rewrite H1. rewrite size_prod; cbn [fst snd].
      instantiate (f:= fun n => f'(n) + 11). subst f.
      cbn. unfold monotonic in H3. rewrite H3 at 1.
      2 : {
        assert (size(enc a) + size(enc b1) + 4 + size(enc b0) + size(enc b) <= size(enc a) + size(enc b1) + 4 + size(enc b0) + 4+ size(enc b) + 4).
        2: apply H. lia.
      }
      reflexivity. 
  + intros [[g k] b]. specialize (LClique_verifierb_correct g k) as H4.
    destruct (reflect_iff (isLClique g b k) (LClique_verifierb g k b)) as (F1 & F2). apply H4.
    split; cbn; tauto. 
 - subst f; smpl_inO. 
 - subst f; smpl_inO. 
Qed. 
