(* Matching mu logic *)
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Record Signature : Type :=
  { sort: Set;
    sort_eq_dec: forall s1 s2 : sort, {s1 = s2} + {s1 <> s2};
    evar : Set;
    evar_eq_dec : forall v1 v2 : evar, {v1 = v2} + {v1 <> v2};
    svar : Set;
    svar_eq_dec : forall v1 v2 : svar, {v1 = v2} + {v1 <> v2};
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
| EVar : evar sigma -> Pattern
| SVar : svar sigma -> Pattern
| And : Pattern -> Pattern -> Pattern
| Neg : Pattern -> Pattern                                
| Sym : symbol sigma -> list Pattern -> Pattern
| Ex : evar sigma -> Pattern -> Pattern
| Mu : svar sigma -> Pattern -> Pattern
.

(* A custom induction principle.
   https://stackoverflow.com/q/47097928/6209703
 *)
Section Pattern_nested_ind.
  Variable P : Pattern -> Prop.
  Hypothesis EVar_case : forall (v : evar sigma), P (EVar v).
  Hypothesis SVar_case : forall (v : svar sigma), P (SVar v).
  Hypothesis And_case : forall (p1 p2 : Pattern), P p1 -> P p2 -> P (And p1 p2).
  Hypothesis Neg_case : forall (p : Pattern), P p -> P (Neg p).
  Hypothesis Sym_case : forall (sym : symbol sigma)(args : list Pattern),
      List.Forall P args -> P (Sym sym args).
  Hypothesis Ex_case : forall (v : evar sigma)(p : Pattern), P p -> P (Ex v p).
  Hypothesis Mu_case : forall (v : svar sigma)(p : Pattern), P p -> P (Mu v p).

  Print Forall.
  Fixpoint Pattern_nested_ind (p : Pattern) : P p :=
    match p with
    | EVar v => EVar_case v
    | SVar v => SVar_case v
    | And p1 p2 => And_case p1 p2 (Pattern_nested_ind p1) (Pattern_nested_ind p2)
    | Neg p' => Neg_case p' (Pattern_nested_ind p')
    | Sym sym args =>
      let H := (fix f (xs : list Pattern) : Forall P xs :=
                  match xs with
                  | nil => Forall_nil _
                  | cons x xs => Forall_cons _ (Pattern_nested_ind x) (f xs)
                  end
               ) args in
      Sym_case sym args H
    | Ex v p' => Ex_case v p' (Pattern_nested_ind p')
    | Mu v p' => Mu_case v p' (Pattern_nested_ind p')
    end.
End Pattern_nested_ind.


(* TODO need better induction *)
Check Pattern_ind.

Fixpoint zipWith {A B C : Type}(f: A -> B -> C)(xs : list A)(ys : list B) : list C :=
  match xs,ys with
  | nil, nil => nil
  | cons _ _, nil => nil
  | nil, cons _ _ => nil
  | cons x xs, cons y ys => cons (f x y) (zipWith f xs ys)
  end.


Fixpoint sortOf (phi : Pattern) : sort sigma :=
  match phi with
  | EVar v => sort_of_evar sigma v
  | SVar v => sort_of_svar sigma v
  | And l r => sortOf l
  | Neg p => sortOf p
  | Sym sym _ => sort_of_symbol_result sym
  | Ex _ p => sortOf p
  | Mu _ p => sortOf p
  end.

Definition Pattern_has_sort (s : sort sigma) (phi : Pattern) : Prop :=
  sortOf phi = s.

Definition Patterns_have_sorts (ss : list (sort sigma)) (ps : list Pattern) : Prop :=
  length ss = length ps /\ fold_right and True (zipWith Pattern_has_sort ss ps).

Fixpoint well_sorted (phi : Pattern) : Prop :=
  match phi with
  | EVar v => True
  | SVar v => True
  | And p1 p2 => sortOf p1 = sortOf p2 /\ well_sorted p1 /\ well_sorted p2
  | Neg p => well_sorted p
  | Sym sym patterns =>
    fold_right and True (map well_sorted patterns)
    /\ Patterns_have_sorts (sorts_of_symbol_args sym) patterns
  | Ex _ p => well_sorted p
  | Mu _ p => well_sorted p
end.

(* returns a pair (hasPositiveOccurence, hasNegativeOccurence) *)
Fixpoint SetVariableOccurences (v : svar sigma) (phi : Pattern) : Prop * Prop :=
  match phi with
  | EVar _ => (False, False)
  | SVar v' => (v' = v, False)
  | And p1 p2 =>
    let (pos_p1, neg_p1) := SetVariableOccurences v p1 in
    let (pos_p2, neg_p2) := SetVariableOccurences v p2 in
    (pos_p1 \/ pos_p2, neg_p1 \/ neg_p2)
  | Neg p =>
    let (pos, neg) := SetVariableOccurences v p in
    (neg, pos)
  | Sym _ patterns
    => fold_right (fun (x y : Prop * Prop) =>
                     let (a,b) := x in
                     let (c,d) := y in
                     ((a \/ c), (b \/ d)))
                  (False, False)
                  (map (SetVariableOccurences v) patterns)
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
  | EVar _ => True
  | SVar _ => True
  | And p1 p2 =>
    noNegativeOccurenceOfMuBoundVariable p1
    /\ noNegativeOccurenceOfMuBoundVariable p2
  | Neg p => noNegativeOccurenceOfMuBoundVariable p
  | Sym _ patterns
    => fold_right and True (map noNegativeOccurenceOfMuBoundVariable patterns)
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

Definition sort_carrier (M : Model) (s : sort sigma) : Ensemble (mod_carrier M) :=
  fun m =>
    mod_el_have_sort M s m.

Lemma in_sort_carrier_implies_have_sort :
  forall (M : Model) (s : sort sigma) (m : mod_carrier M),
    Ensembles.In (mod_carrier M) (sort_carrier M s) m ->
    mod_el_have_sort M s m.
Proof.
  auto.
Qed.

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

Program Definition Valuation_update_evar
           {M : Model}
           (V : @Valuation M)
           (v : evar sigma)
           (m : mod_carrier M)
           (ws : mod_el_have_sort M (sort_of_evar sigma v) m)
  : Valuation :=
  {| val_evar := fun v' =>
                   match evar_eq_dec sigma v v' with
                   | left _ => m
                   | right _ => val_evar V v'
                   end;
     val_svar := val_svar V;
     val_svar_sorted := val_svar_sorted V;
  |}.
Next Obligation.
  destruct (evar_eq_dec sigma v v0).
  - rewrite <- e. assumption.
  - exact (val_evar_sorted V v0).
Qed.

Program Definition Valuation_update_svar
           {M : Model}
           (V : @Valuation M)
           (v : svar sigma)
           (m : Ensemble (mod_carrier M))
           (ws : mod_set_have_sort M (sort_of_svar sigma v) m)
  : Valuation :=
  {| val_evar := val_evar V;
     val_svar := fun v' =>
                   match svar_eq_dec sigma v v' with
                   | left _ => m
                   | right _ => val_svar V v'
                   end;
     val_evar_sorted := val_evar_sorted V;
  |}.
Next Obligation.
  destruct (svar_eq_dec sigma v v0).
  - rewrite <- e. assumption.
  - exact (val_svar_sorted V v0).
Qed.

Fixpoint Valuation_ext {M : Model} (val : @Valuation M) (p : Pattern)
  : Ensemble (mod_carrier M) :=
  let carrier := mod_carrier M  in
  match p with
  | EVar v => Singleton carrier (val_evar val v)
  | SVar v => val_svar val v
  | And p1 p2 =>
    Intersection carrier (Valuation_ext val p1) (Valuation_ext val p2)
  | Neg p' => Setminus carrier (sort_carrier M (sortOf p')) (Valuation_ext val p')
  | Sym sym xs =>
    interpretation_ex sym (map (Valuation_ext val) xs)
  | Ex v p =>
    fun m =>
      exists m' : mod_carrier M,
        exists H : Ensembles.In (mod_carrier M) (sort_carrier M (sort_of_evar sigma v)) m',
          Ensembles.In
            (mod_carrier M)
            (Valuation_ext
               (Valuation_update_evar
                  val v m'
                  (in_sort_carrier_implies_have_sort M (sort_of_evar sigma v) m' H)
               )p)m
            
  | Mu v p => fun m => False
  end.


Lemma Valuation_ext_sorted :
  forall (M : Model) (val : @Valuation M) (p : Pattern),
    well_sorted p ->
    mod_set_have_sort M (sortOf p) (Valuation_ext val p).
Proof.
  intros M val p.
  generalize dependent val.
  induction p using Pattern_nested_ind.
  - (* EVar *)
    intros. simpl in *.
    unfold mod_set_have_sort.
    intros.
    unfold mod_el_have_sort.
    inversion H0.
    apply val_evar_sorted.
  - (* SVar *)
    intros.
    simpl.
    apply val_svar_sorted.
  - (* And *)
    intros.
    simpl.
    simpl in H.
    unfold mod_set_have_sort in *.
    intros.
    inversion H0.
    apply IHp1 in H1.
    assumption.
    destruct H as [Hsortp2 [Hwsp1 Hwsp2]].
    assumption.
  - (* Neg *)
    intros.
    simpl.
    unfold mod_set_have_sort.
    intros.
    unfold Ensembles.In in H0.
    inversion H0.
    unfold Ensembles.In in H1.
    inversion H1.
    rewrite -> H4.
    assumption.
  - (* Sym *)
    intros val Hsymws.
    simpl.
    apply interpretation_ex_sorted.
    Check mod_els_have_sorts.
    assert (Hstronger: forall ss : list (sort sigma),
               fold_right and True (map well_sorted args) ->
               Patterns_have_sorts ss args ->
               sets_have_sorts ss (map (Valuation_ext val) args)).
    {
    (* well_sorted (Sym sym args) gets into the induction hypothesis, which is then unprovable. *)
    clear Hsymws.
    induction args.
    * intros ss Hwellsorted Hsorts.
      destruct ss. simpl. constructor.
      simpl. reflexivity. simpl. exact I.
      inversion Hsorts as [Hlen _]. simpl in Hlen. inversion Hlen.
    * intros [| s ss] [Ha_ws Hargs_ws] [Hlen Hsorts]; simpl in *.
      inversion Hlen.
      inversion H as [|x l Ha Hargs]. subst.
      destruct Hsorts as [Hsort_a Hsort_args].
      split. simpl. rewrite -> map_length. assumption.
      simpl.
      split. unfold Pattern_has_sort in Hsort_a. rewrite -> Hsort_a in Ha. auto.
      destruct IHargs with (ss := ss). assumption. assumption.
      split. inversion Hlen. reflexivity. assumption.
      assumption.
    }
    inversion Hsymws. auto.

      
  - (* Ex *)
    unfold mod_set_have_sort.
    intros.
    unfold mod_set_have_sort in IHp.
    simpl.
    unfold Ensembles.In in H0.
    
    simpl in H0. destruct H0 as [m' [Hm' Hx]].
    unfold Ensembles.In in *.
    
    apply IHp with (val := Valuation_update_evar val v m' (in_sort_carrier_implies_have_sort M (sort_of_evar sigma v) m' Hm')).
    auto. auto.
  - (* Mu *) admit.
Admitted.
