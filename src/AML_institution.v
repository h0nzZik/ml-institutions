(*Require Import Coq.Program.Basics.*)
Require Import Lib.AML.
Require Import Categories.Essentials.Notations.
Require Import Categories.Category.Main.

Print Signature.
Record SignatureMorphism{from to : Signature} : Type :=
  { evarsMorphism : evars from -> evars to;
    svarsMorphism : svars from -> svars to;
    symbolsMorphism : symbols from -> symbols to;
  }.
Check evarsMorphism.
Print Signature.
Definition SignatureMorphism_id{sig:Signature} : @SignatureMorphism sig sig :=
  {| evarsMorphism := fun x => x;
     svarsMorphism := fun x => x;
     symbolsMorphism := fun x => x;
  |}.

Definition SignatureMorphism_compose{A B C : Signature}(g: @SignatureMorphism B C)(f: @SignatureMorphism A B) :=
  {| evarsMorphism := fun x : evars A => evarsMorphism g (evarsMorphism f x);
     svarsMorphism := fun x : svars A => svarsMorphism g (svarsMorphism f x);
     symbolsMorphism := fun x => symbolsMorphism g (symbolsMorphism f x);
  |}.

Definition SignatureMorphism_compose_assoc :
  forall (A B C D : Signature)
         (f: @SignatureMorphism A B)
         (g: @SignatureMorphism B C)
         (h: @SignatureMorphism C D),
    SignatureMorphism_compose h (SignatureMorphism_compose g f)
    = SignatureMorphism_compose (SignatureMorphism_compose h g) f.
Proof.
  intros. auto.
Qed.

Definition Signature_Cat : Category :=
  {| Obj := Signature;
     Hom := fun A B => @SignatureMorphism A B;
     compose := fun _ _ _ f g => SignatureMorphism_compose g f;
     assoc := SignatureMorphism_compose_assoc;
     assoc_sym := fun A B C D f g h => eq_sym (SignatureMorphism_compose_assoc A B C D f g h);
     id := @SignatureMorphism_id;
  |}.
