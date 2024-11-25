import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

set_option diagnostics true

/-
structure Atom : Type
-/

structure AtSeq where
  hypo : Finset Nat
  conc : Nat

structure Rule where
  seq : Finset AtSeq
  conc : Nat
/-
structure Base where
  rules : Set Rule
-/

/-
inductive AtDer : (Base × Finset Nat × Nat) -> Prop where
  | Ref (B : Base) (S : Finset Nat) (p : Nat) : p ∈ S → AtDer (B, S, p)
  | App (B : Base) (S : Finset Nat) (p : Nat) (R : Rule) : R ∈ B.rules → R.conc = p → ∀ seq ∈ R.seq, AtDer (B, seq.hypo ∪ S, seq.conc) → AtDer (B, S, p)
-/

inductive AtDer : (Set Rule × Finset Nat × Nat) -> Prop where
  | Ref (B : Set Rule) (S : Finset Nat) (p : Nat) : p ∈ S → AtDer (B, S, p)
  | App (B : Set Rule) (S : Finset Nat) (p : Nat) (R : Rule) : R ∈ B → R.conc = p → ∀ seq ∈ R.seq, AtDer (B, seq.hypo ∪ S, seq.conc) → AtDer (B, S, p)

theorem lem21 (B : Set Rule) (S L : Finset Nat) (p : Nat) : AtDer (B, S, p) -> AtDer (B, S∪L, p) := sorry

theorem lem22 (B : Set Rule) (S L : Finset Nat) (p : Nat) :
  AtDer (B, S, p) <-> ∀C ⊇ B, ∀ s ∈ S, AtDer (C, ∅, s) -> AtDer (C, ∅, p) := sorry
