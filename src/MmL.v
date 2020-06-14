(* Matching mu logic *)
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Record Signature : Type :=
  { sort: Set;
    sort_eq_dec: forall s1 s2 : sort, {s1 = s2} + {s1 <> s2};
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


Fixpoint well_sorted (phi : Pattern) : Prop :=
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

(* returns a pair (hasPositiveOccurence, hasNegativeOccurence) *)
Fixpoint SetVariableOccurences (phi : Pattern)(s : sort sigma)(v: svar sigma s) : Prop * Prop :=
  match phi with
  | Bottom _ => (False, False)
  | EVar _ _ => (False, False)
  |  SVar s' v' =>
     (
       (match sort_eq_dec sigma s s' with
          (* magic: https://stackoverflow.com/a/59189036/6209703 *)
        | left e => (eq_rec _ (svar sigma) v _ e) = v'
        | right _ => False
        end
       ), False)
  | Sym _ _ _ patterns =>
    ( fix f (ps : list Pattern) :=
        match ps with
        | nil => (False, False)
        | cons p ps' => let (b1, b2) := SetVariableOccurences p s v in
                        let (b3, b4) := f ps'
                        in (b1 \/ b3, b2 \/ b4)
        end             
    ) patterns
  | Impl _ p1 p2 =>
    let (pos_p1, neg_p1) := SetVariableOccurences p1 s v in
    let (pos_p2, neg_p2) := SetVariableOccurences p2 s v in
    (neg_p1 \/ pos_p2, pos_p1 \/ neg_p2)
  | Ex _ _ _ p => SetVariableOccurences p s v
  | Mu _ s' v' p =>
    match sort_eq_dec sigma s s' with
    | left e =>
      let v_v'_equal := (eq_rec _ (svar sigma) v _ e) = v' in
      let (pos, neg) := SetVariableOccurences p s v in
      ( (not v_v'_equal) /\ pos, (not v_v'_equal) /\ neg)
    | right _ => SetVariableOccurences p s v
    end
  end.

Definition hasNegativeOccurence (phi : Pattern) (s : sort sigma) (v : svar sigma s) : Prop :=
  let (_, has_neg) := SetVariableOccurences phi s v in has_neg.

Fixpoint noNegativeOccurenceOfMuBoundVariable (phi : Pattern) : Prop :=
  match phi with
  | Bottom _ => True
  | EVar _ _ => True
  | SVar _ _ => True
  | Sym _ _ _ patterns
    => fold_left (fun (b:Prop) (p:Pattern) => b /\ noNegativeOccurenceOfMuBoundVariable p)
                 patterns True
  | Impl _ p1 p2
    => noNegativeOccurenceOfMuBoundVariable p1
       /\ noNegativeOccurenceOfMuBoundVariable p2
  | Ex _ _ _ p => noNegativeOccurenceOfMuBoundVariable p
  | Mu _ s v p
    => not (hasNegativeOccurence p s v)
       /\ noNegativeOccurenceOfMuBoundVariable p
  end.

Definition well_formed (p : Pattern) : Prop :=
  well_sorted p /\ noNegativeOccurenceOfMuBoundVariable p
.

Check map.


Record Model : Type :=
  { carrier : forall (s : sort sigma), Set;
    (* nonempty *)
    carrier_el : forall (s : sort sigma), carrier s;
    interpretation :
      forall (s : sort sigma)
             (ss : list (sort sigma))
             (sym : symbol sigma (ss, s))
             (args : map (fun x => carrier x) ss),
        Ensemble (carrier s);
  }.