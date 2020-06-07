(*Require Import Coq.Program.Basics.*)
Require Import Lib.AML.
Require Import Categories.Essentials.Notations.

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
