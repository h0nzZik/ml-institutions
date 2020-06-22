(* Matching mu logic *)
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Record Signature : Type :=
  { sort: Set;
    sort_eq_dec: forall s1 s2 : sort, {s1 = s2} + {s1 <> s2};
    evar : Set;
    svar : Set;
    symbol : Set;
    sort_of_evar : evar -> sort;
    sort_of_svar : svar -> sort;
    sort_of_symbol : symbol -> list sort * sort;

    evar_idx : sort -> nat -> evar;
    svar_idx : sort -> nat -> svar;

    evar_idx_sort : forall (s:sort) (n:nat),
        sort_of_evar (evar_idx s n) = s;
    svar_idx_sort : forall (s:sort) (n:nat),
        sort_of_svar (svar_idx s n) = s;
    
    evar_idx_inj: forall (x y : nat) (s1 s2 : sort),
        evar_idx s1 x = evar_idx s2 y -> s1 = s2 /\ x = y;
    svar_idx_inj: forall (x y : nat) (s1 s2 : sort),
        svar_idx s1 x = svar_idx s2 y -> s1 = s2 /\ x = y;
  }.

Parameter sigma : Signature.

Inductive Pattern : Type :=
| Bottom : sort sigma -> Pattern
| EVar : evar sigma -> Pattern
| SVar : svar sigma -> Pattern
| Sym : symbol sigma -> list Pattern -> Pattern
| Impl : Pattern -> Pattern -> Pattern
| Ex : evar sigma -> Pattern -> Pattern
| Mu : svar sigma -> Pattern -> Pattern
.

Fixpoint zipWith {A B C : Type}(f: A -> B -> C)(xs : list A)(ys : list B) : list C :=
  match xs,ys with
  | nil, nil => nil
  | cons _ _, nil => nil
  | nil, cons _ _ => nil
  | cons x xs, cons y ys => cons (f x y) (zipWith f xs ys)
  end.


Fixpoint sortOf (phi : Pattern) : sort sigma :=
  match phi with
  | Bottom s => s
  | EVar v => sort_of_evar sigma v
  | SVar v => sort_of_svar sigma v
  | Sym sym _ => let (_, s) := sort_of_symbol sigma sym in s
  | Impl l r => sortOf r
  | Ex _ p => sortOf p
  | Mu _ p => sortOf p
  end.

Fixpoint well_sorted (phi : Pattern) : Prop :=
  match phi with
  | Bottom _ => True
  | EVar v => True
  | SVar v => True
  | Sym sym patterns =>
    let (sorts, _) := sort_of_symbol sigma sym in
    length patterns = length sorts
    /\ fold_right and True (map well_sorted patterns)
    /\ fold_right and True (zipWith (fun p s => sortOf p = s) patterns sorts)
  | Impl p1 p2 => sortOf p1 = sortOf p2 /\ well_sorted p1 /\ well_sorted p2
  | Ex _ p => well_sorted p
  | Mu _ p => well_sorted p
end.

(* returns a pair (hasPositiveOccurence, hasNegativeOccurence) *)
Fixpoint SetVariableOccurences (v : svar sigma) (phi : Pattern) : Prop * Prop :=
  match phi with
  | Bottom _ => (False, False)
  | EVar _ => (False, False)
  | SVar v' => (v' = v, False)
  | Sym _ patterns
    => fold_right (fun (x y : Prop * Prop) =>
                     let (a,b) := x in
                     let (c,d) := y in
                     ((a \/ c), (b \/ d)))
                  (False, False)
                  (map (SetVariableOccurences v) patterns)
  | Impl p1 p2 =>
    let (pos_p1, neg_p1) := SetVariableOccurences v p1 in
    let (pos_p2, neg_p2) := SetVariableOccurences v p2 in
    (neg_p1 \/ pos_p2, pos_p1 \/ neg_p2)
  | Ex _ p => SetVariableOccurences v p
  | Mu v' p =>
    let (pos, neg) := SetVariableOccurences v p in
    (not (v = v') /\ pos, not (v = v') /\ neg)
  end.

Definition hasNegativeOccurence (phi : Pattern) (v : svar sigma) : Prop :=
  let (_, has_neg) := SetVariableOccurences v phi in has_neg.

Print Sym.
Fixpoint noNegativeOccurenceOfMuBoundVariable (phi : Pattern) : Prop :=
  match phi with
  | Bottom _ => True
  | EVar _ => True
  | SVar _ => True
  | Sym _ patterns
    => fold_right and True (map noNegativeOccurenceOfMuBoundVariable patterns)
  | Impl p1 p2
    => noNegativeOccurenceOfMuBoundVariable p1
       /\ noNegativeOccurenceOfMuBoundVariable p2
  | Ex _ p => noNegativeOccurenceOfMuBoundVariable p
  | Mu v p
    => not (hasNegativeOccurence p v)
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

Check SortedElementEnsemble_hasSort.
Lemma toSortedElementEnsemble_sorted :
  forall (carrier : CarrierType)(s : sort sigma)(els : Ensemble (carrier s)),
    SortedElementEnsemble_hasSort (toSortedElementEnsemble s els) s.
Proof.

Admitted.


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
