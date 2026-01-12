(* HLX Compilation - Axiom A1 Formalization *)

Require Import Axioms.
Open Scope nat_scope.
Open Scope list_scope.

(* Simple expression language *)
Inductive Expr : Type :=
  | Num (n : nat)
  | Plus (e1 e2 : Expr)
  | Times (e1 e2 : Expr).

(* Evaluation function *)
Fixpoint eval (e : Expr) : nat :=
  match e with
  | Num n => n
  | Plus e1 e2 => eval e1 + eval e2
  | Times e1 e2 => eval e1 * eval e2
  end.

(* Bytecode instruction set *)
Inductive BytecodeOp : Type :=
  | PUSH (n : nat)
  | ADD
  | MUL.

(* Program is a sequence of operations *)
Definition BytecodeProgram : Type := list BytecodeOp.

(* Compiler *)
Fixpoint compile_expr (e : Expr) : BytecodeProgram :=
  match e with
  | Num n => PUSH n :: nil
  | Plus e1 e2 => compile_expr e1 ++ compile_expr e2 ++ (ADD :: nil)
  | Times e1 e2 => compile_expr e1 ++ compile_expr e2 ++ (MUL :: nil)
  end.

(* Theorem A1: Determinism *)
Theorem A1_Determinism_Compilation : forall (e : Expr),
  compile_expr e = compile_expr e.
Proof.
  intro e.
  reflexivity.
Qed.

