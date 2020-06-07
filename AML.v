(* Applicative Matching logic *)
Require Import Coq.Sets.Ensembles.

Class CompleteLattice A : Type :=
  {
    meet : Ensemble A -> A
  }.

Record Signature : Type :=
    { evars : Set;
      svars : Set;
      symbols : Set;
      (* we need to be able to create distinct variables *)
      evars_idx : nat -> evars;
      svars_idx : nat -> svars;
      evars_idx_inj: forall (x y : nat), evars_idx(x) = evars_idx(y) -> x = y;
      svars_idx_inj: forall (x y : nat), svars_idx(x) = svars_idx(y) -> x = y;
    }.

Parameter sigma : Signature.

Check sigma.

Inductive Pattern : Type :=
| Bottom : Pattern
| EVar : evars(sigma) -> Pattern
| SVar : svars(sigma) -> Pattern
| Sym : symbols(sigma) -> Pattern
| Impl : Pattern -> Pattern -> Pattern
| Ex : evars(sigma) -> Pattern -> Pattern
| Mu : svars(sigma) -> Pattern -> Pattern
.

Record Model : Type :=
{
  carrier : Set;
  apply : carrier -> carrier -> Ensemble carrier;
  interpretation : symbols(sigma) -> Ensemble carrier;
}.

Inductive Apply_ex(m : Model) (X Y : Ensemble (carrier m)) : Ensemble (carrier m):=
| Apply_ex_intro : forall (x y : carrier m),
                   In (carrier m) X x -> In (carrier m) Y y ->
                   Included (carrier m) (apply m x y) (Apply_ex m X Y)
.
Check Apply_ex.



