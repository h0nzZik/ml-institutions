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
  | Impl s p1 p2 => sortOf p1 = s /\ sortOf p2 = s /\ well_sorted p1 /\ well_sorted p2
  | Ex s _ _ p => sortOf p = s /\ well_sorted p
  | Mu s _ _ p => sortOf p = s /\ well_sorted p                               
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

Record WFPattern : Type :=
  { wfp_pattern : Pattern;
    wfp_well_formed : well_formed wfp_pattern;
  }.


Definition CarrierType : Type := forall (s : sort sigma), Set.

Record SortedElement {carrier : CarrierType} :=
  { se_sort : sort sigma;
    se_element : carrier se_sort;
  }.

Fixpoint zipWith {A B C : Type}(f: A -> B -> C)(xs : list A)(ys : list B) : list C :=
  match xs,ys with
  | nil, nil => nil
  | cons _ _, nil => nil
  | nil, cons _ _ => nil
  | cons x xs, cons y ys => cons (f x y) (zipWith f xs ys)
  end.

Check fold_right.
Definition SortedElementList_sorted { carrier : CarrierType }
         (elements : list (@SortedElement carrier))
         (sorts : list (sort sigma))
  := length elements = length sorts
     /\ fold_right and True (zipWith (fun e s => se_sort e = s) elements sorts).

Definition SortedElementEnsemble_hasSort
           { carrier : CarrierType }
           (e : Ensemble (@SortedElement carrier))
           (s : sort sigma)
  : Prop
  :=
    forall x : @SortedElement carrier,
      Ensembles.In (@SortedElement carrier) e x -> se_sort x = s
.

Definition SortedElementEnsembleList_sorted { carrier : CarrierType }
         (elements : list (Ensemble (@SortedElement carrier)))
         (sorts : list (sort sigma)) : Prop
  := length elements = length sorts
     /\ fold_right and True (zipWith SortedElementEnsemble_hasSort elements sorts).

Definition list_in_ensemble_list {a : Type}(elems : list a)(sets : list (Ensemble a)) : Prop :=
  length elems = length sets
  /\ fold_right and True (zipWith (Ensembles.In a) sets elems).

Lemma ensemble_list_sorted_implies_list_sorted:
  forall
      { carrier : CarrierType }
      ( setList : list (Ensemble (@SortedElement carrier)))
      ( sortList : list (sort sigma)),
    (SortedElementEnsembleList_sorted setList sortList) ->
    forall ( elementList : list (@SortedElement carrier)),
      list_in_ensemble_list elementList setList ->
      SortedElementList_sorted elementList sortList.
Proof.
  intros.
  generalize dependent setList.
  generalize dependent sortList.
  induction elementList.
  - intros. constructor. simpl. destruct H,H0. rewrite <- H. assumption.
    simpl. destruct sortList. simpl. exact I. simpl. exact I.
  - intros.
    destruct H as [HsetListLen HsetListSorted].
    destruct H0 as [HelListLen HelListInSetList].
    assert (Hlen: length (a :: elementList) = length sortList).
    rewrite <- HsetListLen. assumption.
    split. apply Hlen.
    simpl.
    (* sortList and setList are not empty *)
    destruct sortList. simpl. exact I.
    destruct setList. simpl in HsetListLen. inversion HsetListLen.
    (* simplify and clear *)
    simpl in *. inversion HsetListLen. clear HsetListLen. rename H0 into HsetListLen.
    destruct HsetListSorted as [He_hasSort_s HsetList_hasSort_sortList].
    destruct HelListInSetList as [HaIne HelListInSetList].
    split.
    * unfold Ensembles.In in HaIne. unfold SortedElementEnsemble_hasSort in He_hasSort_s. auto.
    * unfold SortedElementList_sorted in IHelementList.
      apply (IHelementList sortList setList).
      split. auto. auto. split. auto. auto.
Qed.            
                      

Record Model : Type :=
  { mod_carrier : forall (s : sort sigma), Set;
    (* nonempty *)
    mod_carrier_el : forall (s : sort sigma), mod_carrier s;

    mod_interpretation :
      forall (s : sort sigma)
             (ss : list (sort sigma))
             (sym : symbol sigma (ss, s))
             (args : list (@SortedElement mod_carrier)),
        SortedElementList_sorted args ss ->
        Ensemble (mod_carrier s);
  }.

(* Pointwise extension of the interpretation *)
Program Definition interpretation_ex {M : Model}
           (s : sort sigma)
           (ss : list (sort sigma))
           (sym : symbol sigma (ss, s))
           (args : list (Ensemble (@SortedElement (mod_carrier M))))
           (sorted: SortedElementEnsembleList_sorted args ss)
  : Ensemble (mod_carrier M s) :=
  fun m =>
    exists (args' : list (@SortedElement (mod_carrier M)))
           (p : list_in_ensemble_list args' args),
    Ensembles.In (mod_carrier M s) (mod_interpretation M s ss sym args' _) m.
Next Obligation.
  apply ensemble_list_sorted_implies_list_sorted with (setList := args).
  assumption. assumption.
Qed.

Record Valuation {M : Model} : Type :=
  {
  val_evar : forall s : sort sigma, evar sigma s -> mod_carrier M s;
  val_svar : forall s : sort sigma, svar sigma s -> Ensemble (mod_carrier M s);
  }.


(* https://stackoverflow.com/a/52518299/6209703 *)
Definition cast {T : Type} {T1 T2 : T} (H : T1 = T2) (f : T -> Type) (x : f T1) :=
  eq_rect T1 (fun T3 : T => f T3) x T2 H.

Definition const {A B : Type} : A -> B -> A :=
  fun x y => x.

Program Definition toSortedElementEnsemble {carrier : CarrierType}
           (s : sort sigma) (els : Ensemble (carrier s)) : Ensemble (@SortedElement carrier) :=
  fun el =>
    match sort_eq_dec sigma s (se_sort el) with
    | left eq => els (cast _ carrier (se_element el))
    | right _ => False
    end.

Program Fixpoint Valuation_ext {M : Model} (val : @Valuation M) (p : Pattern) (ws : well_sorted p)
  : Ensemble (mod_carrier M (sortOf p)) :=
  let carrier := mod_carrier M (sortOf p) in
  match p with
  | Bottom _ => Empty_set carrier
  | EVar s v => Singleton carrier (val_evar val s v)
  | SVar s v => val_svar val s v
  | Sym s ss sym xs =>
    (* const (fun p => False) (map (fun p' => toSortedElementEnsemble (sortOf p') (Valuation_ext val p' _)) xs) *)
    interpretation_ex
      s ss sym
      (map (fun p' => toSortedElementEnsemble (sortOf p') (Valuation_ext val p' _)) xs)
      _
  | Impl s p1 p2 => Union carrier
                          (Complement carrier (Valuation_ext val p1 _))
                          (Valuation_ext val p2 _)
  | Ex s s' v p => fun m => False
  | Mu s s' v p => fun m => False
  end.
Next Obligation.
Next Obligation.
  destruct ws as [H1 [H2 [H3 H4]]]. assumption.
Qed.
Next Obligation.
  destruct ws as [H1 [H2 [H3 H4]]].
  simpl. symmetry. assumption.
Qed.
Next Obligation.
  destruct ws as [H1 [H2 [H3 H4]]]. assumption.
Qed.
Next Obligation.
  simpl. destruct ws as [H1 [H2 [H3 H4]]].
  symmetry. assumption.
Qed.
