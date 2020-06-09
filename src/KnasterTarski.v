Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Definitions.

Class OrderedSet A : Type :=
  { leq : relation A;
    leq_order : order A leq;
  }.

Definition upperBound {A : Type} {OS : OrderedSet A} (X: Ensemble A) (ub: A) : Prop :=
  forall (x: A), In A X x -> leq x ub.

Definition leastUpperBound {A : Type} {OS : OrderedSet A} (X: Ensemble A) (lub: A) : Prop :=
  upperBound X lub /\
  forall (ub : A), upperBound X ub -> leq lub ub.

Definition lowerBound {A : Type} {OS : OrderedSet A} (X: Ensemble A) (lb: A) : Prop :=
  forall (x : A), In A X x ->  leq lb x.

Definition greatestLowerBound {A : Type} {OS : OrderedSet A} (X : Ensemble A) (glb : A) : Prop :=
  lowerBound X glb /\
  forall (lb : A), lowerBound X lb -> leq lb glb.

Definition upperBoundsOf {A : Type} {OS : OrderedSet A} (X : Ensemble A) : Ensemble A :=
  fun x => upperBound X x.

Definition lowerBoundsOf {A : Type} {OS : OrderedSet A} (X : Ensemble A) : Ensemble A :=
  fun x => lowerBound X x.

Definition isMeet {A : Type} {OS : OrderedSet A} (meet : Ensemble A -> A) : Prop :=
  forall (X : Ensemble A), greatestLowerBound X (meet X).

Definition isJoin {A : Type} {OS : OrderedSet A} (join : Ensemble A -> A) : Prop :=
  forall (X : Ensemble A), leastUpperBound X (join X).

Definition joinFromMeet {A : Type} {OS : OrderedSet A} (meet : Ensemble A -> A)
  : Ensemble A -> A :=
  fun X => meet (upperBoundsOf X).

Lemma joinFromMeet_lub: forall (A : Type) (OS : OrderedSet A)
                                (meet : Ensemble A -> A),
     isMeet meet -> isJoin (joinFromMeet meet).
Proof.
  intros. unfold isJoin. intros. unfold leastUpperBound.
   split.
   - (* upper bound *)
     unfold upperBound. intros.
     unfold joinFromMeet.
     assert (xlower: lowerBound (upperBoundsOf X) x).
     unfold lowerBound. intros. unfold upperBoundsOf in H1. unfold In in H1.
     unfold In in H0. unfold upperBound in H1. apply H1. unfold In. apply H0.
     unfold isMeet in H.
     assert (meetX_glb: greatestLowerBound (upperBoundsOf X) (meet (upperBoundsOf X))).
     apply H. unfold greatestLowerBound in meetX_glb. destruct meetX_glb. apply H2. apply xlower.
   - (* least *)
     intros. unfold joinFromMeet. unfold isMeet in H.
     specialize (H (upperBoundsOf X)).
     assert (ub_in : In A (upperBoundsOf X) ub). unfold In. apply H0.
     destruct H. unfold lowerBound in H. apply H. apply ub_in.
Qed.

Definition meetFromJoin {A : Type} {OS : OrderedSet A} (join : Ensemble A -> A)
   : Ensemble A -> A :=
  fun X => join (lowerBoundsOf X).

(* Exactly a dual of joinFromMeet_lub. But there should be some way to avoid duplication. *)
Lemma meetFromJoin_glb: forall (A : Type) (OS : OrderedSet A)
                                (join : Ensemble A -> A),
     isJoin join -> isMeet (meetFromJoin join).
Proof.
  intros. unfold isMeet. intros. unfold greatestLowerBound.
   split.
   - (* lower bound *)
     unfold lowerBound. intros.
     unfold meetFromJoin.
     assert (xupper: upperBound (lowerBoundsOf X) x).
     unfold upperBound. intros. unfold lowerBoundsOf in H1. unfold In in H1.
     unfold In in H0. unfold lowerBound in H1. apply H1. unfold In. apply H0.
     unfold isJoin in H.
     assert (meetX_lub: leastUpperBound (lowerBoundsOf X) (join (lowerBoundsOf X))).
     apply H. unfold leastUpperBound in meetX_lub. destruct meetX_lub. apply H2. apply xupper.
   - (* greatest *)
     intros. unfold meetFromJoin. unfold isJoin in H.
     specialize (H (lowerBoundsOf X)).
     assert (lb_in : In A (lowerBoundsOf X) lb). unfold In. apply H0.
     destruct H. unfold upperBound in H. apply H. apply lb_in.
Qed.


Record CompleteLattice :=
  { orderedSet : OrderedSet;
    meet : Ensemble (carrier orderedSet) -> (carrier orderedSet);
    join : Ensemble (carrier orderedSet) -> (carrier orderedSet);
    meet_isMeet : isMeet meet;
    join_isJoin : isJoin join;
  }.

Definition MonotonicFunction {L:CompleteLattice}
           (f : carrier (orderedSet L) -> carrier (orderedSet L)) :=
  forall (x y : carrier (orderedSet L)), leq (orderedSet L) x y -> leq (orderedSet L) (f x) (f y).

Definition PrefixpointsOf {L:CompleteLattice} (f : carrier L -> carrier L) : Ensemble (carrier L) :=
  fun x => leq L (f x) x.

Definition LeastFixpointOf {L:CompleteLattice}
           (f : carrier L -> carrier L) : carrier L :=
  meet L (PrefixpointsOf f).

Definition PostfixpointsOf {L:CompleteLattice} (f : carrier L -> carrier L) : Ensemble (carrier L) :=
  fun x => leq L x (f x).

Definition GreatestFixpointOf {L:CompleteLattice}
           (f : carrier L -> carrier L) : carrier L :=
  join L (PostfixpointsOf f).
