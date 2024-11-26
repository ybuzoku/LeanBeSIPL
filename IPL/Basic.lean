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
  | Ref (B : Set Rule) (L : Finset Nat) (p : Nat) : p ∈ L → AtDer (B, L, p)
  | App (B : Set Rule) (L : Finset Nat) (p : Nat) (R : Rule) : R ∈ B → R.conc = p → ∀ seq ∈ R.seq, AtDer (B, seq.hypo ∪ L, seq.conc) → AtDer (B, L, p)

theorem lem21 (B : Set Rule) (P U : Finset Nat) (q : Nat) : AtDer (B, P, q) -> AtDer (B, P ∪ U, q) := by
  intro x
  cases x with
  | Ref hB hP hq hqInP =>
  apply AtDer.Ref
  simp --Turns membership of union into a disjunction of memberships
  left
  exact hqInP
  | App hB hP hq hR ruleInBase ruleConcIsOk aseqFromRule aseqFromRuleInRule atDerForSeq =>
  apply AtDer.App
  . exact ruleInBase
  . exact ruleConcIsOk
  . refine aseqFromRuleInRule
  cases atDerForSeq with
  | Ref _ _ _ hqInHypoU  =>
  apply AtDer.Ref
  sorry
  | App _ _ _ _ => sorry











theorem lem22 (B : Set Rule) (S L : Finset Nat) (p : Nat) :
  AtDer (B, S, p) <-> ∀C ⊇ B, ∀ s ∈ S, AtDer (C, ∅, s) -> AtDer (C, ∅, p) := by
  apply Iff.intro
  . intro h
    sorry
  . intro h
    sorry
