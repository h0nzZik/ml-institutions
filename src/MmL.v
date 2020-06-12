(* Matching mu logic *)
Require Import Coq.Sets.Ensembles.
(* Require Import Coq.Lists.List. *)

Record Signature : Type :=
  { sort: Set;
    evar : sort -> Set;
    svar : sort -> Set;
    symbol : list sort * sort -> Set;
    (*sortOfSymbol : symbol -> list sort * sort;*)
    evar_idx : (s:sort) -> nat -> evar s; }.
    svar_idx : sort -> nat -> svar;
    }.
    evar_idx_inj: forall (s1 s2 : sort) (x y : nat),
        (evar_idx s1 x) = (evar_idx s2 y) -> x = y /\ s1 = s2;
    svar_idx_inj: forall (s1 s2 : sort) (x y : nat),
        (svar_idx s1 x) = (svar_idx s2 y) -> x = y /\ s1 = s2;
    }.

Parameter sigma : Signature.

Check sigma.

Inductive Pattern {s : sort sigma} : Type :=
| Bottom : Pattern
| EVar : forall (x : evar(sigma)), sortOfEvar sigma x = s -> x -> Pattern
| SVar : svar(sigma) -> Pattern
| Sym : symbol(sigma) -> Pattern
| Impl : Pattern -> Pattern -> Pattern
| Ex : evar(sigma) -> Pattern -> Pattern
| Mu : svar(sigma) -> Pattern -> Pattern
.
Check EVar.

