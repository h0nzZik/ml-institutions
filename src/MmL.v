(* Matching mu logic *)
Require Import Coq.Sets.Ensembles.
(* Require Import Coq.Lists.List. *)

Record Signature : Type :=
  { sort: Set;
    evar : sort -> Set;
    svar : sort -> Set;
    symbol : list sort * sort -> Set;

    evar_idx : forall s:sort, nat -> evar s;
    svar_idx : forall s:sort, nat -> svar s;
    evar_idx_inj: forall (s : sort) (x y : nat),
        (evar_idx s x) = (evar_idx s y) -> x = y;
    svar_idx_inj: forall (s : sort) (x y : nat),
        (svar_idx s x) = (svar_idx s y) -> x = y;
  }.

Parameter sigma : Signature.

Check sigma.

Inductive Pattern {s : sort sigma} : Type :=
| Bottom : Pattern
| EVar : evar sigma s -> Pattern
| SVar : svar sigma s -> Pattern
(* TODO parameters of the symbol *)                           
| Sym : forall (xs : list (sort sigma)), symbol sigma (xs, s) -> list Pattern -> Pattern
| Impl : Pattern -> Pattern -> Pattern
                                 (*
| Ex : evar(sigma) -> Pattern -> Pattern
| Mu : svar(sigma) -> Pattern -> Pattern*)
.
Check EVar.

