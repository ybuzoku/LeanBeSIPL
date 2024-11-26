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

inductive AtDer : (Set Rule × Finset Nat × Nat) -> Prop where
  | Ref (B : Set Rule) (S : Finset Nat) (p : Nat) : p ∈ S → AtDer (B, S, p)
  | App (B : Set Rule) (S : Finset Nat) (p : Nat) (R : Rule) : (R ∈ B) → (R.conc = p) → (∀ seq ∈ R.seq, AtDer (B, seq.hypo ∪ S, seq.conc)) → AtDer (B, S, p)

theorem lem21 (B : Set Rule) (S L : Finset Nat) (p : Nat) : AtDer (B, S, p) -> AtDer (B, S∪L, p) := by
  intro x
  cases x with
  | Ref hB hS hp hpInS =>
  apply AtDer.Ref
  simp --Turns membership of union into a disjunction of memberships
  left
  exact hpInS
  | App hB hS hp hR hRInhB hRconcIshp iDerivations =>
  apply AtDer.App
  . exact hRInhB
  . exact hRconcIshp
  . intro ruleAtSeq
    specialize iDerivations ruleAtSeq
    intro ruleAtSeqInRule
    constructor
    simp

theorem lem22 (B : Set Rule) (S L : Finset Nat) (p : Nat) :
  AtDer (B, S, p) <-> ∀C ⊇ B, ∀ s ∈ S, AtDer (C, ∅, s) -> AtDer (C, ∅, p) := by
  apply Iff.intro
  . intro h
    sorry
  . intro h
    sorry
