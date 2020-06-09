Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Definitions.

Record CompleteLattice :=
  { carrier : Type;
    leq : relation carrier;
    meet : Ensemble carrier -> carrier;
    leq_order : order carrier leq;
    meet_lower_bound :
      forall (X : Ensemble carrier) (x : carrier),
        In carrier X x -> leq (meet X) x;
    meet_greatest_lower_bound :
      forall (X : Ensemble carrier) (lb : carrier),
        (forall x : carrier, In carrier X x -> leq lb x) -> leq lb (meet X);
                                       
  }.

Definition join {L:CompleteLattice} (S : Ensemble (carrier L)) : carrier L :=
  meet L (fun ub : carrier L => forall x : carrier L, In (carrier L) S x -> leq L x ub).

(* TODO: prove properties of join *)

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
  join (PostfixpointsOf f).