Require Import Categories.Essentials.Notations.
Require Import Categories.Category.Main.
Require Import Categories.Cat.Cat.
Require Import Categories.Coq_Cats.Main.
Require Import Categories.Functor.Main.
Require Import Categories.NatTrans.Main.

Class Institution : Type :=
  { Sign : Category;
    Mod : Functor Sign (Cat^op);
    (* We may need to generalize the following to `Coq_Cat Type` *)
    Sen : Functor Sign Set_Cat;
    (* Sign-indexed relation on objects of (Mod s) x (Sen s) *)
    satisfies: forall s:Sign, (FO Mod s) -> (FO Sen s) -> Prop;

    inst_satisfies_cond : forall (s1 s2 : Sign) (phi : Hom s1 s2) (m' : FO Mod s2) (f : FO Sen s1),
        satisfies s2 m' ((FA Sen phi) f) <-> satisfies s1 (FO (FA Mod phi) m') f;
  }.

Check Functor_compose.
Record InstitutionMorphism (I1 I2 : Institution) :=
  { sign_transform : Functor (@Sign I1) (@Sign I2);
    (* The paper requires mod_transform to be defined like this: *)
    (* mod_transform : NatTrans (@Mod I1) (Functor_compose sign_transform (@Mod I2)); *)
    (* But then Coq complains, since in the satisfaction condition, m has wrong type *)
    mod_transform : NatTrans (Functor_compose sign_transform (@Mod I2)) (@Mod I1);
    sen_transform : NatTrans (Functor_compose sign_transform  (@Sen I2)) (@Sen I1);
    instmorph_satisf_condition :
      forall (sigma : @Sign I1)
             (m : (FO (@Mod I1)) sigma)
             (f' : (FO (@Sen I2)) (FO sign_transform sigma)),
        @satisfies I1 sigma m (Trans sen_transform sigma f')
        <-> @satisfies I2 (FO sign_transform sigma) (FO (Trans mod_transform sigma) m) f';
  }.
