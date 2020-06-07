Require Import Lib.AML.

(* A test signature / model *)

Inductive SomeSymbols : Set :=
| f : SomeSymbols
| g : SomeSymbols
.

Definition nat_id(x: nat) : nat := x.
Lemma nat_id_inj: forall (x y : nat), nat_id x = nat_id y -> x = y.
Proof. intros. unfold nat_id in H. apply H. Qed.

Definition a_signature := {|
  evars := nat;
  svars := nat;
  symbols := SomeSymbols;
  evars_idx := nat_id;
  svars_idx := nat_id;
  evars_idx_inj := nat_id_inj;
  svars_idx_inj := nat_id_inj;
|}.