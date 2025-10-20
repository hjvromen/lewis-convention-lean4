/-
  Formalization of Lewis's convention argument structure.

  This file defines the R-closure (RC) of a proposition and proves key lemmas
  about reasoning (R) and indication (Ind) over a set of individuals.

  Fix RC definition properly: it must take both `R` and `φ` as parameters.
  This avoids the error `(RC φ : Prop → Prop)`.
-/

import Mathlib.Tactic

universe u

section Lewis

variable {indiv : Type u}
-- R i p: individual i reasons to proposition p
variable (R : indiv → Prop → Prop)
-- Ind A i p: given common knowledge A, individual i indicates proposition p
variable (Ind : Prop → indiv → Prop → Prop)
variable (A φ p : Prop)

-- Core axioms for reasoning and indication
variable
  -- A1: If i indicates p (given A) and i reasons to A, then i reasons to p
  (A1 : ∀ {i : indiv} {p : Prop}, Ind A i p → R i A → R i p)
  -- A6: Composition of indication through reasoning
  -- If i indicates "j reasons to A" and i reasons to "j indicates u",
  -- then i indicates "j reasons to u"
  (A6 : ∀ {i j : indiv} {u : Prop}, Ind A i (R j A) ∧ R i (Ind A j u) → Ind A i (R j u))
  -- C1: Everyone reasons to the common knowledge A
  (C1 : ∀ i : indiv, R i A)
  -- C2: Everyone indicates that everyone reasons to A
  (C2 : ∀ i j : indiv, Ind A i (R j A))
  -- C3: Everyone indicates φ (the base proposition)
  (C3 : ∀ i : indiv, Ind A i φ)
  -- C4: If i indicates u, then i reasons to "j indicates u" for any j
  (C4 : ∀ {i j : indiv} {u : Prop}, Ind A i u → R i (Ind A j u))

/--
  R-closure of φ: the set of propositions reachable from φ by iteratively
  applying the reasoning operator R for various individuals.

  This captures the idea of nested reasoning chains like:
  φ, R j φ, R i (R j φ), R k (R i (R j φ)), ...
-/
inductive RC (R : indiv → Prop → Prop) (φ : Prop) : Prop → Prop
| base : RC R φ φ  -- φ is in its own R-closure
| step {u : Prop} (j : indiv) (hu : RC R φ u) : RC R φ (R j u)
  -- If u is in the closure, so is R j u for any individual j

namespace RC

variable {R : indiv → Prop → Prop}
variable {Ind : Prop → indiv → Prop → Prop}
variable {A φ p : Prop}

/--
  Key lemma: If q is in the R-closure of φ, then every individual i indicates q.
  This shows that the R-closure preserves the indication property.
-/
lemma ind_of_rc
  (A6 : ∀ {i j : indiv} {u : Prop}, Ind A i (R j A) ∧ R i (Ind A j u) → Ind A i (R j u))
  (C2 : ∀ i j : indiv, Ind A i (R j A))
  (C3 : ∀ i : indiv, Ind A i φ)
  (C4 : ∀ {i j : indiv} {u : Prop}, Ind A i u → R i (Ind A j u))
  {i : indiv} {q : Prop} (h : RC R φ q) : Ind A i q := by
  induction h with
  | base => exact C3 i  -- Base case: i indicates φ by C3
  | @step v j _ ih =>
      -- Inductive case: if i indicates v, show i indicates R j v
      have h₁ : R i (Ind A j v) := C4 ih  -- By C4, i reasons to "j indicates v"
      have h₂ : Ind A i (R j v) := A6 ⟨C2 i j, h₁⟩  -- By A6 composition
      exact h₂

/--
  Main theorem: If p is in the R-closure of φ, then every individual reasons to p.
  This establishes that propositions in the R-closure achieve common reasoning.
-/
lemma everyone_reason_of_rc
  (A1 : ∀ {i : indiv} {p : Prop}, Ind A i p → R i A → R i p)
  (A6 : ∀ {i j : indiv} {u : Prop}, Ind A i (R j A) ∧ R i (Ind A j u) → Ind A i (R j u))
  (C1 : ∀ i : indiv, R i A)
  (C2 : ∀ i j : indiv, Ind A i (R j A))
  (C3 : ∀ i : indiv, Ind A i φ)
  (C4 : ∀ {i j : indiv} {u : Prop}, Ind A i u → R i (Ind A j u))
  (hp : RC R φ p) : ∀ i : indiv, R i p := by
  intro i
  have hInd : Ind A i p := ind_of_rc A6 C2 C3 C4 hp  -- i indicates p
  exact A1 hInd (C1 i)  -- Since i indicates p and reasons to A, i reasons to p

-- Concrete examples showing specific elements in the R-closure

/-- R j φ is in the R-closure: everyone reasons to it -/
lemma L1
  (A1 : ∀ {i : indiv} {p : Prop}, Ind A i p → R i A → R i p)
  (A6 : ∀ {i j : indiv} {u : Prop}, Ind A i (R j A) ∧ R i (Ind A j u) → Ind A i (R j u))
  (C1 : ∀ i : indiv, R i A)
  (C2 : ∀ i j : indiv, Ind A i (R j A))
  (C3 : ∀ i : indiv, Ind A i φ)
  (C4 : ∀ {i j : indiv} {u : Prop}, Ind A i u → R i (Ind A j u))
  (i j : indiv) : R i (R j φ) := by
  have h₁ : Ind A i φ := C3 i  -- i indicates φ
  have h₂ : R i (Ind A j φ) := C4 h₁  -- i reasons to "j indicates φ"
  have h₃ : Ind A i (R j φ) := A6 ⟨C2 i j, h₂⟩  -- i indicates "j reasons to φ"
  exact A1 h₃ (C1 i)  -- Therefore i reasons to "j reasons to φ"

/-- R j (R k φ) is in the R-closure: depth-2 nesting -/
lemma L2
  (A1 : ∀ {i : indiv} {p : Prop}, Ind A i p → R i A → R i p)
  (A6 : ∀ {i j : indiv} {u : Prop}, Ind A i (R j A) ∧ R i (Ind A j u) → Ind A i (R j u))
  (C1 : ∀ i : indiv, R i A)
  (C2 : ∀ i j : indiv, Ind A i (R j A))
  (C3 : ∀ i : indiv, Ind A i φ)
  (C4 : ∀ {i j : indiv} {u : Prop}, Ind A i u → R i (Ind A j u))
  (i j k : indiv) : R i (R j (R k φ)) := by
  have h₁ : Ind A i φ := C3 i
  have h₂ : R i (Ind A k φ) := C4 h₁
  have h₃ : Ind A i (R k φ) := A6 ⟨C2 i k, h₂⟩
  have h₄ : R i (Ind A j (R k φ)) := C4 h₃
  have h₅ : Ind A i (R j (R k φ)) := A6 ⟨C2 i j, h₄⟩
  exact A1 h₅ (C1 i)

/-- R j (R k (R ℓ φ)) is in the R-closure: depth-3 nesting -/
lemma L3
  (A1 : ∀ {i : indiv} {p : Prop}, Ind A i p → R i A → R i p)
  (A6 : ∀ {i j : indiv} {u : Prop}, Ind A i (R j A) ∧ R i (Ind A j u) → Ind A i (R j u))
  (C1 : ∀ i : indiv, R i A)
  (C2 : ∀ i j : indiv, Ind A i (R j A))
  (C3 : ∀ i : indiv, Ind A i φ)
  (C4 : ∀ {i j : indiv} {u : Prop}, Ind A i u → R i (Ind A j u))
  (i j k ℓ : indiv) : R i (R j (R k (R ℓ φ))) := by
  have h₁ : Ind A i φ := C3 i
  have h₂ : R i (Ind A ℓ φ) := C4 h₁
  have h₃ : Ind A i (R ℓ φ) := A6 ⟨C2 i ℓ, h₂⟩
  have h₄ : R i (Ind A k (R ℓ φ)) := C4 h₃
  have h₅ : Ind A i (R k (R ℓ φ)) := A6 ⟨C2 i k, h₄⟩
  have h₆ : R i (Ind A j (R k (R ℓ φ))) := C4 h₅
  have h₇ : Ind A i (R j (R k (R ℓ φ))) := A6 ⟨C2 i j, h₆⟩
  exact A1 h₇ (C1 i)

end RC

end Lewis
