Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Definitions.
Require Import Lib.KnasterTarski.

Variable U : Type.

Program Instance EnsembleOrderedSet : OrderedSet (Ensemble U) :=
  {| leq := Ensembles.Included U;
  |}.
Next Obligation.
  constructor.
  * unfold reflexive. unfold Included. auto.
  * unfold transitive. unfold Included. auto.
  * unfold antisymmetric. intros.
    apply Extensionality_Ensembles. split; auto.
Qed.

Definition Meet (ee : Ensemble (Ensemble U)) : Ensemble U :=
  fun m => forall e : Ensemble U,
      Ensembles.In (Ensemble U) ee e -> Ensembles.In U e m.

Lemma Meet_is_meet : isMeet Meet.
Proof.
  unfold isMeet. unfold greatestLowerBound. unfold Meet.
  intro X. split.
  - 

(* TODO lemma that Meet behaves like a meet. We will use the lemma in the two obligations
   from the following definition: *)
Program Instance ModelCompleteLattice
        {M : Model} {s : sort sigma} : CompleteLattice (Ensemble (mod_carrier M s)) :=
  {| meet := Meet;
     join := joinFromMeet Meet;
  |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
