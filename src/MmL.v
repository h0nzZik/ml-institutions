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

(* The first parameter of all the constructor is the target sort of the pattern.
   We do not have it as a parameter of the inductive type, because for the Sym constructor
   we would need to somehow pass sorts to the types of arguments,
 *)
Inductive Pattern : Type :=
| Bottom : forall (s : sort sigma), Pattern
| EVar : forall (s : sort sigma), evar sigma s -> Pattern
| SVar : forall (s : sort sigma), svar sigma s -> Pattern
| Sym : forall (s : sort sigma) (xs : list (sort sigma)), symbol sigma (xs, s)
                                                          -> list Pattern -> Pattern
| Impl : forall (s : sort sigma), Pattern -> Pattern -> Pattern
| Ex : forall (s s': sort sigma), evar sigma s' -> Pattern -> Pattern
| Mu : forall (s s': sort sigma), svar sigma s' -> Pattern -> Pattern
.

Definition sortOf (phi : Pattern) : sort sigma :=
  match phi with
  | Bottom s => s
  | EVar s _ => s
  | SVar s _ => s
  | Sym s _ _ _ => s
  | Impl s _ _ => s
  | Ex s _ _ _ => s
  | Mu s _ _ _ => s
  end.


Fixpoint well_formed (phi : Pattern) : Prop :=
  match phi with
  | Bottom _ => True
  | EVar _ _ => True
  | SVar _ _ => True
  | Sym s sorts sym patterns =>
    ( fix f (ss : list (sort sigma)) (ps : list Pattern) :=
        match ss,ps with
        | nil,nil => True
        | nil, cons _ _ => False
        | cons _ _, nil => False
        | cons s ss', cons p ps' => sortOf p = s /\ f ss' ps'
        end
    ) sorts patterns
  | Impl s p1 p2 => sortOf p1 = s /\ sortOf p2 = s
  | Ex s _ _ p => sortOf p = s
  | Mu s _ _ p => sortOf p = s                               
  end.

