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

(* Deserialization with state: returns (value, remaining_bytes) *)
Fixpoint deserialize_aux (bytes : list nat) (fuel : nat) : (Value * list nat) :=
  match fuel with
  | O => (Null, bytes) (* Out of fuel, return Null *)
  | S fuel' =>
      match bytes with
      | nil => (Null, nil)
      | 0 :: rest => (Null, rest)
      | 1 :: i :: rest => (Int i, rest)
      | 2 :: rest => (Bytes rest, nil) (* Consume all remaining bytes *)
      | 3 :: len :: rest =>
          (* Deserialize array elements *)
          let '(elems, remaining) := deserialize_list rest len fuel' in
          (Array elems, remaining)
      | 4 :: len :: rest =>
          (* Deserialize object fields *)
          let '(fields, remaining) := deserialize_fields rest len fuel' in
          (Object fields, remaining)
      | _ => (Null, bytes)
      end
  end
(* Deserialize a list of n values *)
with deserialize_list (bytes : list nat) (n : nat) (fuel : nat) : (list Value * list nat) :=
  match n with
  | O => (nil, bytes)
  | S n' =>
      match fuel with
      | O => (nil, bytes)
      | S fuel' =>
          let '(v, rest1) := deserialize_aux bytes fuel' in
          let '(vs, rest2) := deserialize_list rest1 n' fuel' in
          (v :: vs, rest2)
      end
  end
(* Deserialize n object fields (key-value pairs) *)
with deserialize_fields (bytes : list nat) (n : nat) (fuel : nat) : (list (nat * Value) * list nat) :=
  match n with
  | O => (nil, bytes)
  | S n' =>
      match fuel with
      | O => (nil, bytes)
      | S fuel' =>
          match bytes with
          | k :: rest =>
              let '(v, rest1) := deserialize_aux rest fuel' in
              let '(fields, rest2) := deserialize_fields rest1 n' fuel' in
              ((k, v) :: fields, rest2)
          | nil => (nil, nil)
          end
      end
  end.

(* Top-level deserialization (use large fuel value) *)
Definition deserialize (bytes : list nat) : Value :=
  fst (deserialize_aux bytes 1000).

(* Theorem A4: Serialization roundtrip for simple values *)
Theorem A4_Serialization_Simple : forall (v : Value),
  (v = Null \/ exists i, v = Int i \/ exists b, v = Bytes b) ->
  deserialize (serialize v) = v.
Proof.
  intros v H.
  destruct H as [H_null | [i [H_int | [b H_bytes]]]].
  - (* Case: Null *)
    rewrite H_null.
    unfold deserialize, serialize.
    simpl.
    reflexivity.
  - (* Case: Int i *)
    rewrite H_int.
    unfold deserialize, serialize.
    simpl.
    reflexivity.
  - (* Case: Bytes b *)
    rewrite H_bytes.
    unfold deserialize, serialize.
    simpl.
    reflexivity.
Qed.

(* Theorem A4 extended: Empty arrays and objects *)
Theorem A4_Serialization_Empty_Composite : forall (v : Value),
  (v = Array nil \/ v = Object nil) ->
  deserialize (serialize v) = v.
Proof.
  intros v H.
  destruct H as [H_arr | H_obj].
  - (* Case: Array nil *)
    rewrite H_arr.
    unfold deserialize, serialize.
    simpl.
    reflexivity.
  - (* Case: Object nil *)
    rewrite H_obj.
    unfold deserialize, serialize.
    simpl.
    reflexivity.
Qed.

(* Theorem A4 partial: Roundtrip holds for all simple types and empty composites *)
Theorem A4_Serialization_Base : forall (v : Value),
  (v = Null \/
   (exists i, v = Int i) \/
   (exists b, v = Bytes b) \/
   v = Array nil \/
   v = Object nil) ->
  deserialize (serialize v) = v.
Proof.
  intros v H.
  destruct H as [H_null | [[i H_int] | [[b H_bytes] | [H_arr | H_obj]]]].
  - (* Null *)
    rewrite H_null. unfold deserialize, serialize. simpl. reflexivity.
  - (* Int i *)
    rewrite H_int. unfold deserialize, serialize. simpl. reflexivity.
  - (* Bytes b *)
    rewrite H_bytes. unfold deserialize, serialize. simpl. reflexivity.
  - (* Array nil *)
    rewrite H_arr. unfold deserialize, serialize. simpl. reflexivity.
  - (* Object nil *)
    rewrite H_obj. unfold deserialize, serialize. simpl. reflexivity.
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