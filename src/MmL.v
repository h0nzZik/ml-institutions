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

Definition sorts_of_symbol_args (sym : symbol sigma) : list (sort sigma) :=
  fst (sort_of_symbol sigma sym).

Definition sort_of_symbol_result (sym : symbol sigma) : sort sigma :=
  snd (sort_of_symbol sigma sym).

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

Record Model : Type :=
  { mod_carrier : Set;
    mod_el_sort : mod_carrier -> sort sigma;

    (* helper functions *)
    mod_el_have_sort (s : sort sigma) (x : mod_carrier) : Prop :=
      mod_el_sort x = s;
    
    mod_set_have_sort (s : sort sigma) (e : Ensemble mod_carrier) : Prop :=
      forall x : mod_carrier,
        Ensembles.In mod_carrier e x -> mod_el_have_sort s x;
    
    mod_els_have_sorts (ss : list (sort sigma)) (xs : list mod_carrier) : Prop :=
      fold_right and True (zipWith mod_el_have_sort ss xs);
      
    mod_carrier_nonempty : forall (s : sort sigma), exists (x : mod_carrier), mod_el_have_sort s x;

    mod_interpretation : symbol sigma -> list mod_carrier -> Ensemble (mod_carrier);

    mod_interpretation_sorted :
      forall (sym : symbol sigma)
             (args : list mod_carrier),
        mod_els_have_sorts (sorts_of_symbol_args sym) args
        -> mod_set_have_sort (sort_of_symbol_result sym) (mod_interpretation sym args);

    mod_interpretation_ill :
      forall (sym : symbol sigma)
             (args : list mod_carrier),
        ~mod_els_have_sorts (sorts_of_symbol_args sym) args
        -> mod_interpretation sym args = Empty_set mod_carrier;
  }.

Definition sets_have_sorts
           {M : Model}
           (ss : list (sort sigma))
           (es : list (Ensemble (mod_carrier M)))
  : Prop := 
  length ss = length es /\ fold_right and True (zipWith (mod_set_have_sort M) ss es)
.

Definition list_in_ensemble_list {a : Type}(sets : list (Ensemble a))(elems : list a) : Prop :=
  length elems = length sets
  /\ fold_right and True (zipWith (Ensembles.In a) sets elems).

Lemma list_in_ensemble_list_sorted :
  forall (M : Model)
         (ss : list (sort sigma))
         (es : list (Ensemble (mod_carrier M)))
         (xs : list (mod_carrier M)),
    sets_have_sorts ss es ->
    list_in_ensemble_list es xs ->
    mod_els_have_sorts M ss xs.
Proof.
  induction ss; intros; unfold mod_els_have_sorts; destruct xs; simpl; try exact I.
  (* `es` cannot be `nil` *)
  destruct es; inversion H; try inversion H1.
  split.
  - unfold mod_el_have_sort.
    destruct H,H0. simpl in *. destruct H2.
    unfold mod_set_have_sort in H2. firstorder. 
  - unfold mod_els_have_sorts in IHss. apply (IHss es). inversion H0.
    unfold sets_have_sorts. split. assumption. simpl in H2. destruct H2. assumption.
    inversion H0. unfold list_in_ensemble_list. split. simpl in H3. inversion H3. reflexivity.
    simpl in H5. destruct H5. assumption.
Qed.    

(* Pointwise extension of the interpretation *)
Definition interpretation_ex
        {M : Model}
        (sym : symbol sigma)        
        (args : list (Ensemble (mod_carrier M)))
  : Ensemble (mod_carrier M) :=
  fun m =>
    exists (args' : list (mod_carrier M)),
    list_in_ensemble_list args args' /\ 
    Ensembles.In (mod_carrier M) (mod_interpretation M sym args') m
.

Lemma interpretation_ex_sorted :
  forall (M : Model)(sym : symbol sigma)(args : list (Ensemble (mod_carrier M))),
    sets_have_sorts (sorts_of_symbol_args sym) args ->
    mod_set_have_sort M (sort_of_symbol_result sym) (interpretation_ex sym args).
Proof.
  intros. unfold mod_set_have_sort.
  intros. unfold mod_el_have_sort.
  unfold Ensembles.In in H0. unfold interpretation_ex in H0.
  destruct H0 as [args' [H1 H2]].
  remember (list_in_ensemble_list_sorted M (sorts_of_symbol_args sym) args args' H H1) as args'_sorts.
  clear Heqargs'_sorts.
  remember (mod_interpretation_sorted M sym args' args'_sorts) as interp_sorts.
  clear Heqinterp_sorts.
  unfold mod_set_have_sort in interp_sorts.
  remember (interp_sorts x H2) as x_sort.
  clear Heqx_sort.
  unfold mod_el_have_sort in x_sort. assumption.
Qed.

Record Valuation {M : Model} : Type :=
  {
  val_evar : evar sigma -> mod_carrier M;
  val_svar : svar sigma -> Ensemble (mod_carrier M);

  val_evar_sorted :
    forall v : evar sigma, mod_el_have_sort M (sort_of_evar sigma v) (val_evar v);
  val_svar_sorted :
    forall v : svar sigma, mod_set_have_sort M (sort_of_svar sigma v) (val_svar v);
  }.

Fixpoint Valuation_ext {M : Model} (val : @Valuation M) (p : Pattern)
  : Ensemble (mod_carrier M) :=
  let carrier := mod_carrier M  in
  match p with
  | Bottom _ => Empty_set carrier
  | EVar v => Singleton carrier (val_evar val v)
  | SVar v => val_svar val v
  | Sym sym xs =>
    interpretation_ex sym (map (Valuation_ext val) xs)
  | Impl p1 p2 => Union carrier
                          (Complement carrier (Valuation_ext val p1)) (* WRONG *)
                          (Valuation_ext val p2)
  | Ex v p => fun m => False
  | Mu v p => fun m => False
  end.
Print Model.
(* TODO: lemma: If a pattern is well-sorted, then valuation_ext has the same sort as the pattern *)
Lemma Valuation_ext_sorted :
  forall (M : Model) (val : @Valuation M) (p : Pattern),
    mod_set_have_sort M (sortOf p) (Valuation_ext val p).
Proof.
  intros M val p.
  generalize dependent val.
  induction p.
  - (* Bottom *) admit.
  - (* EVar *) admit.
  - (* SVar *) admit.
  - (* Sym *) admit.
  - (* Impl *) admit.
  - (* Ex *) admit.
  - (* Mu *) admit.
Admitted.
