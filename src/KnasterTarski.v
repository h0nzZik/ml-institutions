Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Definitions.

Record OrderedSet :=
  { carrier : Type;
    leq : relation carrier;
    leq_order : order carrier leq;
  }.

Definition upperBound {OS : OrderedSet} (X: Ensemble (carrier OS)) (ub: carrier OS) : Prop :=
  forall (x: carrier OS), In (carrier OS) X x -> leq OS x ub.

Definition leastUpperBound {OS : OrderedSet} (X: Ensemble (carrier OS)) (lub: carrier OS) : Prop :=
  upperBound X lub /\
  forall (ub : carrier OS), upperBound X ub -> leq OS lub ub.

Definition lowerBound {OS : OrderedSet} (X: Ensemble (carrier OS)) (lb: carrier OS) : Prop :=
  forall (x: carrier OS), In (carrier OS) X x ->  leq OS lb x.

Definition greatestLowerBound {OS : OrderedSet} (X: Ensemble (carrier OS)) (glb: carrier OS) : Prop :=
  lowerBound X glb /\
  forall (lb : carrier OS), lowerBound X lb -> leq OS lb glb.

Definition upperBoundsOf {OS : OrderedSet} (X : Ensemble (carrier OS)) : Ensemble (carrier OS) :=
  fun x => upperBound X x.

Definition lowerBoundsOf {OS : OrderedSet} (X : Ensemble (carrier OS)) : Ensemble (carrier OS) :=
  fun x => lowerBound X x.

Definition isMeet {OS : OrderedSet} (meet : Ensemble (carrier OS) -> carrier OS) : Prop :=
  forall (X : Ensemble (carrier OS)), greatestLowerBound X (meet X).

Definition isJoin {OS : OrderedSet} (join : Ensemble (carrier OS) -> carrier OS) : Prop :=
  forall (X : Ensemble (carrier OS)), leastUpperBound X (join X).

 Definition joinFromMeet {OS : OrderedSet}
            (meet : Ensemble (carrier OS) -> carrier OS)
   : Ensemble (carrier OS) -> carrier OS :=
  fun X => meet (upperBoundsOf X).


 
 Lemma joinFromMeet_lub: forall (OS : OrderedSet)
                                (meet : Ensemble (carrier OS) -> carrier OS),
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
     assert (ub_in : In (carrier OS) (upperBoundsOf X) ub). unfold In. apply H0.
     destruct H. unfold lowerBound in H. apply H. apply ub_in.
 Qed.
 

Record CompleteLattice :=
  { orderedSet : OrderedSet;
    meet : Ensemble (carrier orderedSet) -> (carrier orderedSet);
    meet_glb :
      forall (X : Ensemble (carrier orderedSet)),
        greatestLowerBound X (meet X);
                                       
  }.

Definition join (L:CompleteLattice) (S : Ensemble (carrier L)) : carrier L :=
  meet L (fun ub : carrier L => forall x : carrier L, In (carrier L) S x -> leq L x ub).

(* TODO: prove properties of join *)
Lemma join_upper_bound : forall (L:CompleteLattice) (X : Ensemble (carrier L)),
    join L 

Definition MonotonicFunction {L:CompleteLattice} (f : carrier L -> carrier L) :=
  forall (x y : carrier L), leq L x y -> leq L (f x) (f y).

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
