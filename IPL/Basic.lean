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
  | App (B : Set Rule) (S : Finset Nat) (r : Nat) (R : Rule) : R ∈ B → (R.conc = r) -> (∀ seq ∈ R.seq, AtDer (B, seq.hypo ∪ S, seq.conc)) → AtDer (B, S, r)

theorem lem21 (B : Set Rule) (P U : Finset Nat) (q : Nat) : AtDer (B, P, q) -> AtDer (B, P ∪ U, q) := by
  intro hAtDer
  generalize hArgs : (B, P, q) = args
  rw [hArgs] at hAtDer
  induction hAtDer with
  | Ref hB hP hq hqInhP =>
    apply AtDer.Ref
    simp
    simp at hArgs
    obtain ⟨hBisB, t⟩ := hArgs
    obtain ⟨hPisP, hqIsq⟩ := t
    left
    rw [<-hPisP] at hqInhP
    rw [<-hqIsq] at hqInhP
    exact hqInhP
  | App hB hP hr hR hRinhB hConcIshr hAders i =>
    simp at hArgs
    obtain ⟨hBisB, t⟩ := hArgs
    obtain ⟨hPisP, hqIsq⟩ := t
    apply AtDer.App
    . sorry
    . sorry
    . sorry
    . exact hR


theorem lem22 (B : Set Rule) (S L : Finset Nat) (p : Nat) :
  AtDer (B, S, p) <-> ∀C ⊇ B, ∀ s ∈ S, AtDer (C, ∅, s) -> AtDer (C, ∅, p) := by
  apply Iff.intro
  . intro h
    sorry
  . intro h
    sorry
