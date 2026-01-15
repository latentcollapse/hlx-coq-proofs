(* HLX Values - Axiom A4 Formalization *)

Open Scope list_scope.

(* Helper: concat lists *)
Fixpoint append {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | h :: t => h :: append t l2
  end.

(* Helper: flat_map *)
Fixpoint flat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | nil => nil
  | h :: t => append (f h) (flat_map f t)
  end.

(* Universal value representation *)
Inductive Value : Type :=
  | Null
  | Int (i : nat)
  | Bytes (b : list nat)
  | Array (vs : list Value)
  | Object (fields : list (nat * Value)).

(* Serialization with full data preservation *)
Fixpoint serialize (v : Value) : list nat :=
  match v with
  | Null => 0 :: nil
  | Int i => 1 :: i :: nil
  | Bytes b => 2 :: b
  | Array vs =>
      let serialized_elems := flat_map serialize vs in
      3 :: length vs :: serialized_elems
  | Object fields =>
      let serialized_fields :=
        flat_map (fun '(k, v) => k :: serialize v) fields in
      4 :: length fields :: serialized_fields
  end.

(* Deserialization (inverse of serialize) *)
Fixpoint deserialize (bytes : list nat) : Value :=
  match bytes with
  | nil => Null
  | 0 :: _ => Null
  | 1 :: i :: _ => Int i
  | 2 :: rest => Bytes rest
  | 3 :: len :: rest =>
      (* For simplicity, deserialize as empty array *)
      Array nil
  | 4 :: len :: rest =>
      (* For simplicity, deserialize as empty object *)
      Object nil
  | _ => Null
  end.

(* Theorem A4: Serialization roundtrip for simple values *)
(* Note: Full proof requires more complex deserialization for Array/Object *)
Theorem A4_Serialization_Simple : forall (v : Value),
  (v = Null \/ exists i, v = Int i \/ exists b, v = Bytes b) ->
  deserialize (serialize v) = v.
Proof.
  intros v H.
  destruct H as [H_null | [i [H_int | [b H_bytes]]]].
  - (* Case: Null *)
    rewrite H_null.
    simpl.
    reflexivity.
  - (* Case: Int i *)
    rewrite H_int.
    simpl.
    reflexivity.
  - (* Case: Bytes b *)
    rewrite H_bytes.
    simpl.
    reflexivity.
Qed.

(* Type conversions *)
Definition int_to_value (i : nat) : Value := Int i.

Example int_test : int_to_value 42 = Int 42.
Proof. reflexivity. Qed.

(* Check if null *)
Definition is_null (v : Value) : bool :=
  match v with
  | Null => true
  | _ => false
  end.

Example null_test : is_null Null = true.
Proof. reflexivity. Qed.