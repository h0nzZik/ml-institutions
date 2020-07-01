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

(* List of set variables that are not allowed to be used positively or negatively. *)
Record SVarBlacklist : Set :=
  { blacklistNegative : list (svar sigma);
    blacklistPositive : list (svar sigma);
  }.

Definition SVB_empty : SVarBlacklist :=
  {| blacklistNegative := nil;
     blacklistPositive := nil;
  |}.

Definition SVB_add (v : svar sigma) (b : SVarBlacklist) : SVarBlacklist :=
  {| blacklistNegative := cons v (blacklistNegative b);
     blacklistPositive := blacklistPositive b;
  |}.

Definition SVB_swap (b : SVarBlacklist) : SVarBlacklist :=
  {| blacklistNegative := blacklistPositive b;
     blacklistPositive := blacklistNegative b;
  |}.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.
  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls)
  .

  Definition hhead (x : A) (xs : list A) (l : hlist (cons x xs)) : B x :=
    match l with
    | HCons _ _ h _ => h
    end.

  Definition htail x xs (l : hlist (cons x xs)) : hlist xs :=
    match l with
    | HCons _ _ _ tl => tl
    end.

  Variable P : forall a : A, B a -> Prop.
  Inductive Forall : forall (ts : list A), hlist ts -> Prop :=
  | Forall_nil : Forall nil HNil
  | Forall_cons : forall (t : A) (ts : list A) (x : B t) (xs : hlist ts),
      P t x -> Forall ts xs -> Forall (cons t ts) (HCons t ts x xs)
  .
End hlist.

Inductive Pattern : SVarBlacklist -> sort sigma -> Type :=
| EVar : forall (v : evar sigma)(b : SVarBlacklist),
    Pattern b (sort_of_evar sigma v)
| SVar : forall (v : svar sigma)(b : SVarBlacklist),
    ~List.In v (blacklistPositive b) -> Pattern b (sort_of_svar sigma v)
| And : forall (s : sort sigma)(b : SVarBlacklist),
    Pattern b s -> Pattern b s -> Pattern b s
| Neg : forall (s : sort sigma)(b : SVarBlacklist),
    Pattern (SVB_swap b) s -> Pattern b s
| Sym : forall (sym : symbol sigma)(b : SVarBlacklist),
    hlist (sort sigma) (Pattern b) (sorts_of_symbol_args sym) -> Pattern b (sort_of_symbol_result sym)
| Ex : forall (s : sort sigma)(b : SVarBlacklist),
    evar sigma -> Pattern b s -> Pattern b s
| Mu : forall (s : sort sigma)(b : SVarBlacklist) (v : svar sigma),
    Pattern (SVB_add v b) s -> Pattern b s
.

(* A custom induction principle.
   https://stackoverflow.com/q/47097928/6209703
 *)
Section Pattern_nested_ind.
  Variable P : forall (b : SVarBlacklist) (s : sort sigma), Pattern b s -> Prop.
  Hypothesis EVar_case : forall (v : evar sigma)(b : SVarBlacklist), P b (sort_of_evar sigma v) (EVar v b).
  Hypothesis SVar_case : forall (v : svar sigma)(b : SVarBlacklist)(pf : ~ In v (blacklistPositive b)), P b (sort_of_svar sigma v) (SVar v b pf).
  Hypothesis And_case : forall (s : sort sigma) (b : SVarBlacklist) (p1 p2 : Pattern b s), P b s p1 -> P b s p2 -> P b s (And s b p1 p2).
  Hypothesis Neg_case : forall (s : sort sigma)(b : SVarBlacklist)(p : Pattern (SVB_swap b) s), P (SVB_swap b) s p -> P b s (Neg s b p).
  Hypothesis Sym_case :
    forall (sym : symbol sigma)(b : SVarBlacklist)
           (args : hlist (sort sigma) (Pattern b) (sorts_of_symbol_args sym)),
      Forall (sort sigma) (Pattern b) (P b) (sorts_of_symbol_args sym) args ->
      P b (sort_of_symbol_result sym) (Sym sym b args).
  Hypothesis Ex_case : forall (s : sort sigma)(b : SVarBlacklist) (v : evar sigma)(p : Pattern b s),
      P b s p -> P b s (Ex s b v p).
  Hypothesis Mu_case : forall (s : sort sigma)(b : SVarBlacklist)(v : svar sigma)
                              (p : Pattern (SVB_add v b) s), P (SVB_add v b) s p -> P b s (Mu s b v p).

  Fixpoint Pattern_nested_ind (s : sort sigma) (b : SVarBlacklist) (p : Pattern b s) : P b s p :=
    match p with
    | EVar v b => EVar_case v b
    | SVar v b pf => SVar_case v b pf 
    | And s b p1 p2 => And_case s b p1 p2 (Pattern_nested_ind s b p1) (Pattern_nested_ind s b p2)
    | Neg s b p' => Neg_case s b p' (Pattern_nested_ind s (SVB_swap b) p')
    | Sym sym b args =>
      let H := (fix f (ss : list (sort sigma))
                    (xs : hlist (sort sigma) (Pattern b) ss) : Forall (sort sigma) (Pattern b) (P b) ss xs :=
                  match xs with
                  | HNil _ _ => Forall_nil (sort sigma) (Pattern b) (P b)
                  | HCons _ _ s ss x xs => Forall_cons (sort sigma) (Pattern b) (P b) s ss x xs (Pattern_nested_ind s b x) (f ss xs)
                  end
               ) (sorts_of_symbol_args sym) args in
      Sym_case sym b args H
    | Ex s b v p' => Ex_case s b v p' (Pattern_nested_ind s b p')
    | Mu s b v p' => Mu_case s b v p' (Pattern_nested_ind s (SVB_add v b) p')
    end.
End Pattern_nested_ind.

Fixpoint zipWith {A B C : Type}(f: A -> B -> C)(xs : list A)(ys : list B) : list C :=
  match xs,ys with
  | nil, nil => nil
  | cons _ _, nil => nil
  | nil, cons _ _ => nil
  | cons x xs, cons y ys => cons (f x y) (zipWith f xs ys)
  end.

Record Model : Type :=
  { mod_carrier : sort sigma -> Set;
      
    mod_carrier_nonempty : forall (s : sort sigma), mod_carrier s;

    mod_interpretation : forall sym : symbol sigma,
        hlist (sort sigma) mod_carrier (sorts_of_symbol_args sym) ->
        Ensemble (mod_carrier (sort_of_symbol_result sym));
  }.

(* https://stackoverflow.com/a/62679065/6209703 *)
Fixpoint hlist_in_ensemble_hlist {A : Type}{B : A -> Type}(types : list A)
        (sets : hlist A (fun a => Ensemble (B a)) types) (elems : hlist A B types) : Prop :=
  match types with
  | nil => fun _ _ => True
  | cons t ts =>
    fun sets elems =>
      Ensembles.In (B t) (hhead A (fun a => Ensemble (B a)) t ts sets) (hhead A B t ts elems)
      /\ hlist_in_ensemble_hlist ts (htail A (fun a => Ensemble (B a)) t ts sets) (htail A B t ts elems)
  end sets elems.

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
