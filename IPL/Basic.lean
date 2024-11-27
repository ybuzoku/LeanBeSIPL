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
  | App (B : Set Rule) (S : Finset Nat) (r : Nat) (R : Rule) : R ∈ B → ∀ seq ∈ R.seq, AtDer (B, seq.hypo ∪ S, seq.conc) → AtDer (B, S, R.conc)


theorem lem21 (B : Set Rule) (P U : Finset Nat) (q : Nat) : AtDer (B, P, q) -> AtDer (B, P ∪ U, q) := by
  intro hAtDer
  generalize hArgs : (B, P, q) = args
  rw [hArgs] at hAtDer
  induction hAtDer with
  | Ref hB hP hq hqInP =>
    apply AtDer.Ref
    simp
    simp at hArgs
    obtain ⟨hBisB, t⟩ := hArgs
    obtain ⟨hPisP, hqIsq⟩ := t
    left
    rw [<-hPisP] at hqInP
    rw [<-hqIsq] at hqInP
    exact hqInP
  | App hB hP hq hR hRinhB hAtseq hAtseqInR hDer i =>
    simp [hArgs] at *
    sorry
/-
example (B : Set Rule) (P U : Finset Nat) (q : Nat) : AtDer (B, P, q) -> AtDer (B, P ∪ U, q) := by
  intro hAtDer
  generalize hArgs : (B, P, q) = args
  simp [hArgs] at *
  induction hAtDer
  case Ref hB hP hq hqInP =>
    apply AtDer.Ref
    simp
    left


  case App hB hP hq hR hRinhB hAtseq hAtseqInR hDer' i =>
    apply i
-/

/-
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
  | App hB hP hq hR hRinhB hRConcIshq hAtSeq hAtSeqInRule hDer i =>
    simp at hArgs
    obtain ⟨hBisB, t⟩ := hArgs
    obtain ⟨hPisP, hqIsq⟩ := t
    apply AtDer.App
    . rw [<-hBisB] at hRinhB
      refine hRinhB
    . rw [<-hqIsq] at hRConcIshq
      exact hRConcIshq
    . exact hAtSeqInRule
    . rw [<-hBisB] at i
      rw [<-hBisB] at hDer
      simp at i
      induction hDer with
      | Ref _ _ _ hConcInSeqHypo =>
        apply AtDer.Ref
        rw [<-hPisP] at hConcInSeqHypo
        simp
        simp at hConcInSeqHypo
        cases hConcInSeqHypo with
        | inl h =>
          left
          exact h
        | inr h =>
          right
          left
          exact h
      | App ihB ihP ihq ihR ihRinihB ihRConcIsihq ihAtSeq ihAtSeqInRule ihDer =>
-/

      /-
        apply AtDer.App
        . exact ihRinihB
        . exact ihRConcIsihq
        . exact ihAtSeqInRule
        .
      -/













theorem lem22 (B : Set Rule) (S L : Finset Nat) (p : Nat) :
  AtDer (B, S, p) <-> ∀C ⊇ B, ∀ s ∈ S, AtDer (C, ∅, s) -> AtDer (C, ∅, p) := by
  apply Iff.intro
  . intro h
    sorry
  . intro h
    sorry
