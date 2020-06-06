(* Applicative Matching logic *)

Record Signature : Type :=
    { evars : Set;
      svars : Set;
      symbols : Set;
      (* we need to be able to create distinct variables *)
      evars_idx : nat -> evars;
      svars_idx : nat -> svars;
      _: forall (x y : nat), evars_idx(x) = evars_idx(y) -> x = y;
      _: forall (x y : nat), svars_idx(x) = svars_idx(y) -> x = y;
    }.

  Parameter sigma : Signature.
  

  Inductive Pattern : Type :=
  | Bottom : Pattern
  | EVar : evars(sigma) -> Pattern
  | SVar : svars(sigma) -> Pattern
  | Sym : symbols(sigma) -> Pattern
  | Impl : Pattern -> Pattern -> Pattern
  | Ex : evars(sigma) -> Pattern -> Pattern
  | Mu : svars(sigma) -> Pattern -> Pattern
  .
