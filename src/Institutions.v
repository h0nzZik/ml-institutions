Require Import Categories.Essentials.Notations.
Require Import Categories.Category.Main.
Require Import Categories.Cat.Cat.
Require Import Categories.Coq_Cats.Main.
Require Import Categories.Functor.Main.

Class Institution : Type :=
  { Sign : Category;
    Mod : Functor Sign (Opposite Cat);
    (* We may need to generalize the following to `Coq_Cat Type` *)
    Sen : Functor Sign Set_Cat;
    (* Sign-indexed relation on objects of (Mod s) x (Sen s) *)
    satisfies: forall s:Sign, (FO Mod s) -> (FO Sen s) -> Prop;

    satisfies_cond : forall (s1 s2 : Sign) (phi : Hom s1 s2) (m' : FO Mod s2) (f : FO Sen s1),
        satisfies s2 m' ((FA Sen phi) f) <-> satisfies s1 (FO (FA Mod phi) m') f;
  }.

