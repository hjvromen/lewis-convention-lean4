/-
Copyright (c) 2022 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

/- Type for individuals -/
variable {indiv : Type}
variable {i j : indiv}

/- Type for reasons to believe -/
variable {reason : Type} [Mul reason]
variable {r s t : reason}

/- These reasons will be used in the axioms for reasoning with reasons -/
-- In Lean 4, we declare these as variables that will be fixed in the context
variable (a b c : reason)

/- A and φ are propositions that are used in the definition of a basis for common knowledge -/
-- In Lean 4, we declare these as variables
variable (A φ : Prop)

variable {α β γ : Prop}

/- `rb` is the property of being a reason for an individual to believe a
    proposition -/
variable (rb : reason → indiv → Prop → Prop)

/-- R is defined as having `a` reason to believe a proposition -/
def R (rb : reason → indiv → Prop → Prop) (i : indiv) (φ : Prop) : Prop :=
  ∃ r, rb r i φ

/-- Indication is defined as having `a` reason to believe that φ implies ψ -/
def Ind (rb : reason → indiv → Prop → Prop) (φ : Prop) (i : indiv) (ψ : Prop) : Prop :=
  R rb i (φ → ψ)

/-- Our logic of reasons has the `application rule` as an axiom. This rule is
based on the justification logic of Artemov (2019). -/
axiom AR (rb : reason → indiv → Prop → Prop) :
  ∀ {s t : reason} {i : indiv} {α β : Prop},
  rb s i (α → β) → rb t i α → rb (s * t) i β

/-- The following axioms define a minimal logic of reasons -/
axiom T1 (rb : reason → indiv → Prop → Prop) (a : reason) :
  ∀ {i : indiv} {α β : Prop}, rb a i (α → β → (α ∧ β))

axiom T2 (rb : reason → indiv → Prop → Prop) (b : reason) :
  ∀ {i : indiv} {α β γ : Prop}, rb b i (((α → β) ∧ (β → γ)) → (α → γ))

axiom T3 (rb : reason → indiv → Prop → Prop) (c : reason) :
  ∀ {i j : indiv} {α β : Prop}, rb c i (R rb j (α → β) → (R rb j α → R rb j β))

/-- This lemma is a direct consequence of the application rule `AR` -/
lemma E1 (rb : reason → indiv → Prop → Prop) :
    ∀ {i : indiv} {α β : Prop}, R rb i (α → β) → R rb i α → R rb i β := by
  intro i α β h1 h2
  rw [R] at *
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  use s * t
  exact AR rb hs ht

/-- This lemma is needed for proving lemma (E2) -/
lemma L1 (rb : reason → indiv → Prop → Prop) (a : reason) :
    ∀ {i : indiv} {α β : Prop}, R rb i α → R rb i β → R rb i (α ∧ β) := by
  intro i α β h1 h2
  rw [R] at *
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have h3 : rb (a * s) i (β → (α ∧ β)) := by
    have h4 : rb a i (α → (β → (α ∧ β))) := T1 rb a
    exact AR rb h4 hs
  use a * s * t
  exact AR rb h3 ht

/-- The lemmas (E2) and (E3) are needed for proving lemma (A6) -/
lemma E2 (rb : reason → indiv → Prop → Prop) (a b : reason) :
    ∀ {i : indiv} {α β γ : Prop}, R rb i (α → β) → R rb i (β → γ) → R rb i (α → γ) := by
  intro i α β γ h1 h2
  have h3 : R rb i ((α → β) ∧ (β → γ)) := L1 rb a h1 h2
  obtain ⟨s, hs⟩ := h3
  use b * s
  exact AR rb (T2 rb b) hs

lemma E3 (rb : reason → indiv → Prop → Prop) (c : reason) :
    ∀ {i j : indiv} {α β : Prop}, R rb i (R rb j (α → β)) → R rb i (R rb j α → R rb j β) := by
  intro i j α β h1
  obtain ⟨s, hs⟩ := h1
  use c * s
  exact AR rb (T3 rb c) hs

/-- (A1) follows immediately from the definition of indication and the application
    rule. So it does not have to be taken as an axiom, like Cubitt and Sugden did. -/
lemma A1 (rb : reason → indiv → Prop → Prop) (A : Prop) :
    ∀ {i : indiv} {α : Prop}, Ind rb A i α → R rb i A → R rb i α := by
  intro i α h1 h2
  rw [Ind] at h1
  rw [R] at *
  obtain ⟨t, ht⟩ := h2
  obtain ⟨s, hs⟩ := h1
  use s * t
  exact AR rb hs ht

/-- Using (E1) provides a simpler proof -/
lemma A1_alternative_proof (rb : reason → indiv → Prop → Prop) (A : Prop) :
    ∀ {i : indiv} {α : Prop}, Ind rb A i α → R rb i A → R rb i α :=
  fun h1 h2 => E1 rb h1 h2

/-- (A6) can be proven using lemmas (E2) and (E3). So it does not have to be taken
    as an axiom anymore, like Cubitt and Sugden did. -/
lemma A6 (rb : reason → indiv → Prop → Prop) (A : Prop) (a b c : reason) :
    ∀ α {i j : indiv}, Ind rb A i (R rb j A) → R rb i (Ind rb A j α) → Ind rb A i (R rb j α) := by
  intro p i j h1 h2
  rw [Ind] at *
  have h3 : R rb i (R rb j A → R rb j p) := E3 rb c h2
  have h4 : R rb i (A → R rb j p) := E2 rb a b h1 h3
  exact h4

/-- We are now at the point where we can prove Lewis' theorem -/
inductive G (rb : reason → indiv → Prop → Prop) (φ : Prop) : Prop → Prop
  | base : G rb φ φ
  | step (p : Prop) (i : indiv) : G rb φ p → G rb φ (R rb i p)

lemma Lewis (rb : reason → indiv → Prop → Prop) (A φ : Prop) (a b c : reason) (p : Prop)
    (C1 : ∀ i, R rb i A)
    (C2 : ∀ i j, Ind rb A i (R rb j A))
    (C3 : ∀ i, Ind rb A i φ)
    (C4 : ∀ α i j, Ind rb A i α → R rb i (Ind rb A j α))
    (h7 : G rb φ p) :
    ∀ i, R rb i p := by
  intro i
  have h1 : Ind rb A i p := by
    induction h7 with
    | base => exact C3 _
    | step u j hu ih =>
      have h3 : R rb i (Ind rb A j u) := C4 u _ _ ih
      have h4 : R rb i (Ind rb A j u) → Ind rb A i (R rb j u) := A6 rb A a b c u (C2 _ _)
      have h5 : Ind rb A i (R rb j u) := h4 h3
      exact h5
  exact A1 rb A h1 (C1 _)

#check Lewis
