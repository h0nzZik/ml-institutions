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

Section hlist_hmap.
  Variable A : Type.
  Variable B C : A -> Type.
  Variable F : forall a : A, B a -> C a.
(*
  Fixpoint hmap (ts : list A) : hlist A B ts -> hlist A C ts :=
    match ts with
    | nil => fun _ => HNil A C
    | cons x xs =>
      fun l =>
        HCons A C x xs (F x (hhead A B x xs l)) (hmap xs (htail A B x xs l))             
    end.
 *)
  (* This version of hmap is uglier than the above one, but it does explicit
     matching on its second argument, and therefore can be used when reasoning
     about termination of `Valuation_ext`. *)
  Fixpoint hmap (ts : list A) (l : hlist A B ts) : hlist A C ts :=
    match ts with
    | nil => fun _ => HNil A C
    | cons x xs =>
      fun l : hlist A B (cons x xs) =>
        match l with
        | HCons _ _ x xs h t =>
          HCons A C x xs (F x h) (hmap xs t)
        end
    end l.
End hlist_hmap.


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
(*
Locate "+".
Locate sum.
Check Nat.add.
Check Sym.
Fixpoint Pattern_measure b s (p : Pattern b s) : nat :=
  match p with
  | EVar _ _ => 0
  | SVar _ _ _ => 0
  | And s b p1 p2 => S (Nat.add (Pattern_measure b s p1) (Pattern_measure b s p2))
  | Neg s b p => S (Pattern_measure (SVB_swap b) s p)
  | Sym sym b args
    => S (
           (fix f (ts : list (sort sigma)) (args : hlist (sort sigma) (Pattern b) ts) : nat :=
              match ts with
              | nil => 0
              | cons x xs => Nat.add () ()
             0
           ) (sorts_of_symbol_args sym) args
         )
  | Ex s b v p => S (Pattern_measure b s p)
  | Mu s b v p => S (Pattern_measure (SVB_add v b) s p)
  end.
*)

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
        (args : hlist (sort sigma) (fun s => Ensemble (mod_carrier M s)) (sorts_of_symbol_args sym))
  : Ensemble (mod_carrier M (sort_of_symbol_result sym)) :=
  fun m =>
    exists (args' : hlist (sort sigma) (mod_carrier M) (sorts_of_symbol_args sym)),
    hlist_in_ensemble_hlist (sorts_of_symbol_args sym) args args' /\ 
    Ensembles.In (mod_carrier M (sort_of_symbol_result sym)) (mod_interpretation M sym args') m
.

Record Valuation {M : Model} : Type :=
  {
  val_evar : forall v : evar sigma, mod_carrier M (sort_of_evar sigma v);
  val_svar : forall v : svar sigma, Ensemble (mod_carrier M (sort_of_svar sigma v));
  }.

Definition Valuation_update_evar
           {M : Model}
           (V : @Valuation M)
           (v : evar sigma)
           (m : mod_carrier M (sort_of_evar sigma v))
  : Valuation :=
  {| val_evar := fun v' =>
                   match evar_eq_dec sigma v v' with
                   | left e =>
                     match e with
                     | eq_refl _ => fun m => m
                     end
                   | right _ => fun _ => val_evar V v'
                   end m;
     val_svar := val_svar V;
  |}.

Definition Valuation_update_svar
           {M : Model}
           (V : @Valuation M)
           (v : svar sigma)
           (m : Ensemble (mod_carrier M (sort_of_svar sigma v)))
  : Valuation :=
  {| val_evar := val_evar V;
     val_svar := fun v' =>
                   match svar_eq_dec sigma v v' with
                   | left e =>
                     match e with
                     | eq_refl _ => m
                     end
                   | right _ => val_svar V v'
                   end;
  |}.

Check Ex.
Fixpoint Valuation_ext {M : Model} (val : @Valuation M)
         (b : SVarBlacklist) (s : sort sigma) (p : Pattern b s) {struct p}
  : Ensemble (mod_carrier M s) :=
  match p with
  | EVar v _ => Singleton (mod_carrier M (sort_of_evar sigma v)) (val_evar val v)
  | Neg s b p' => Complement (mod_carrier M s) (Valuation_ext val (SVB_swap b) s p')
  | Sym sym b args =>
    interpretation_ex sym (hmap (sort sigma)
                                (Pattern b)
                                (fun s => Ensemble (mod_carrier M s))
                                (Valuation_ext val b)
                                (sorts_of_symbol_args sym)
                                args
                          )

  | Ex s b v p =>
    fun m =>
      exists m' : mod_carrier M (sort_of_evar sigma v),
          Ensembles.In
            (mod_carrier M s)
            (Valuation_ext (Valuation_update_evar val v m') b s p)
            m
  | _ => fun m => False
  end.
