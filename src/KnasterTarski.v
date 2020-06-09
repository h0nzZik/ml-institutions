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


Class CompleteLattice A `{OrderedSet A} :=
  {
    meet : Ensemble A -> A;
    join : Ensemble A -> A;
    meet_isMeet : isMeet meet;
    join_isJoin : isJoin join;
  }.

Definition MonotonicFunction {A : Type} {OS : OrderedSet A}
           (f : A -> A) :=
  forall (x y : A), leq x y -> leq (f x) (f y).

Definition PrefixpointsOf {A : Type} {OS : OrderedSet A} (f : A -> A) : Ensemble A :=
  fun x => leq (f x) x.

Definition LeastFixpointOf {A : Type} {OS : OrderedSet A} {L : CompleteLattice A}
           (f : A -> A) : A :=
  meet (PrefixpointsOf f).

Definition PostfixpointsOf {A : Type} {OS : OrderedSet A} (f : A -> A) : Ensemble A :=
  fun x => leq x (f x).

Definition GreatestFixpointOf {A : Type} {OS : OrderedSet A} {L : CompleteLattice A}
           (f : A -> A) : A :=
  join (PostfixpointsOf f).
