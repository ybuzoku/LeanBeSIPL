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


-- Reference theorems and proofs below --

theorem AtDerMono (B: Set Rule) (S : Finset Nat) (p : Nat) :
  ∀ X ⊇ B, AtDer B S p -> AtDer X S p := by
  intro C
  intro baseGeq
  intro aDer
  induction aDer with
  | Ref =>
    apply AtDer.Ref
    trivial
  | App _ _ _ R_in_B _ _ _ =>
    apply AtDer.App
    . exact baseGeq R_in_B
    . trivial
    . trivial

theorem rulesInExtension (B: Set Rule) :
  ∀ X ⊇ B, ∀ x, x ∈ B -> x ∈ X := by
  intro C
  intro baseGeq
  intro R
  intro RinB
  exact baseGeq RinB

-- Main Lemmas and Theorems from the paper --

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

lemma xx1 (P S T : Finset Nat) :
  ((P ∪ S) \ T ∪ P) = P ∪ (S \ T) := by
  sorry

lemma xx2 (B : Set Rule) (S T : Finset Nat) (r : Nat) (R : Rule) :
  ∀ C ⊇ B, (∀ t ∈ T, AtDer C ∅ t) -> R ∈ B → (R.conc = r) → (∀ seq ∈ R.seq, AtDer C ((seq.hypo ∪ S)\T) seq.conc) → AtDer C (S\T) r := by
  intro C
  intro CextB
  intro axiomDers
  intro rule
  intro ruleconc_Is_r
  intro hDers
  apply AtDer.App
  . exact CextB rule
  . trivial
  . intro atSeq
    intro atSeqInRule
    specialize hDers atSeq
    specialize hDers atSeqInRule
    have hDersWeak := lem21 C ((atSeq.hypo ∪ S) \ T) atSeq.hypo atSeq.conc hDers
    have x := xx1 atSeq.hypo S T
    rw [x] at hDersWeak
    trivial

theorem lem22 (B : Set Rule) (T : Finset Nat) (u : Nat) :
  AtDer B T u <-> ∀ C ⊇ B, (∀ t ∈ T, AtDer C ∅ t) -> AtDer C ∅ u := by
  apply Iff.intro
  . intro h
    intro C
    intro C_Ext_B
    intro all_t_axiom_deriv
    induction h with
    | Ref hL hp p_in_L =>
      apply all_t_axiom_deriv
      trivial
    | App hL hp hR hR_in_B hR_conc_is_hp iDers ih =>
      apply AtDer.App
      . exact C_Ext_B hR_in_B
      . trivial
      . intro hAtseq
        intro hAtseq_In_Rule
        simp
        specialize iDers hAtseq
        specialize iDers hAtseq_In_Rule
        specialize ih hAtseq
        specialize ih hAtseq_In_Rule
        --generalize hDer_Args : (hAtseq.hypo ∪ T) = x11
        --generalize hDer_Conc : hAtseq.conc = x21
        --rw [hDer_Args] at iDers
        --rw [hDer_Conc] at iDers

        cases iDers with
        | Ref hS hp conc_in_hypo_or_hS =>
          --rw [<-hDer_Args] at conc_in_hypo_or_hS
          simp at conc_in_hypo_or_hS
          cases conc_in_hypo_or_hS with
          | inl =>
            apply AtDer.Ref
            trivial
          | inr hh=>
            --rw [<-hDer_Conc] at hh
            specialize all_t_axiom_deriv hAtseq.conc
            specialize all_t_axiom_deriv hh
            have x := lem21 C ∅ hAtseq.hypo hAtseq.conc all_t_axiom_deriv
            simp at x
            --rw [hDer_Conc] at x
            trivial
        | App hS hr hR2 hR2inB hR2conc_is_hr hDers2 =>
            apply AtDer.App
            . exact C_Ext_B hR2inB
            . trivial
            . intro hAtseq2
              intro hAtseq2inseqs
              specialize hDers2 hAtseq2
              specialize hDers2 hAtseq2inseqs
              have x1 := Finset.union_assoc hAtseq2.hypo hAtseq.hypo hL
              rw [<-x1] at hDers2
              sorry

  . intro h
    sorry
