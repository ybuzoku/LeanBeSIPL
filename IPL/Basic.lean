import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

/-
structure Atom : Type
-/

--Define Atoms as a natural number like construction

/-
inductive Atom
  | zero : Atom
  | succ (a : Atom) : Atom
-/

structure AtSeq where
  hypo : Finset Nat
  conc : Nat

structure Rule where
  seq : Finset AtSeq
  conc : Nat

inductive AtDer : Set Rule -> Finset Nat -> Nat -> Prop where
  | Ref (B : Set Rule) (S : Finset Nat) (p : Nat) : p ∈ S → AtDer B S p
  | App (B : Set Rule) (S : Finset Nat) (r : Nat) (R : Rule) : R ∈ B → (R.conc = r) → (∀ seq ∈ R.seq, AtDer B (seq.hypo ∪ S) seq.conc) → AtDer B S r

theorem lem21 (B : Set Rule) (P U : Finset Nat) (q : Nat) : AtDer B P q -> AtDer B (P ∪ U) q := by
  intro hAtDer
  induction hAtDer with
  | Ref =>
    apply AtDer.Ref
    simp
    left
    trivial
  | App _ _ _ _ _ hDers i =>
    simp [hDers] at i
    apply AtDer.App
    . trivial
    . trivial
    . trivial


theorem lem22 (B : Set Rule) (S L : Finset Nat) (p : Nat) :
  AtDer B S p <-> ∀ C ⊇ B, (∀ s ∈ S, AtDer C ∅ s) -> AtDer C ∅ p := by
  apply Iff.intro
  . intro h
    intro C
    intro C_Ext_B
    intro all_s_axiom_deriv
    induction h with
    | Ref hS hp p_in_S =>
      apply all_s_axiom_deriv
      trivial
    | App hS hp hR hR_in_B hR_conc_is_hp iDers ih =>
      apply
      sorry
  . intro h
    sorry

theorem rulesInExtension (B: Set Rule) :
  ∀ X ⊇ B, ∀ x, x ∈ B -> x ∈ X := by
  intro C
  intro baseGeq
  intro R
  intro RinB
  exact baseGeq RinB
