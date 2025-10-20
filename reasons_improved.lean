/-
Copyright (c) 2022 Huub Vromen. All rights reserved.
Author: Huub Vromen

Formalization of Lewis's convention theorem using justification logic.

This file provides an alternative approach to formalizing Lewis's theory of
common knowledge and conventions, based on Artemov's justification logic (2019).
Unlike Sillari's modal logic approach (which we showed has problems), this
approach uses explicit "reasons" that can be combined and tracked.

Key differences from Sillari's approach:
- Uses explicit reasons (terms) rather than modal operators
- Reasons can be composed using multiplication (application)
- Axioms like A1 and A6 become PROVABLE rather than assumed
- Lewis's theorem has a clear, non-trivial proof

This formalization follows Cubitt and Sugden's framework but improves it by
deriving axioms A1 and A6 from more primitive principles.
-/

import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

-- ============================================================================
-- Core Definitions
-- ============================================================================

/--
  Type for individuals (agents in the epistemic system)
  Type for reasons: explicit justifications or evidence for beliefs.

  In justification logic, a "reason" is a formal object that justifies
  believing a proposition. Reasons can be combined via multiplication,
  representing the application of one reason to another (similar to
  function application or modus ponens).

  R i φ: "Individual i has (some) reason to believe φ"

  This is the existential quantification over reasons: i has reason to believe φ
  if there exists at least one reason r that justifies i in believing φ.

  This corresponds to the box operator □ in modal logic, but is more explicit
  about the justification structure.

  rb r i φ: "Reason r justifies individual i in believing proposition φ"
  This is the primitive relation in justification logic.
-/
def R {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (i : indiv) (φ : Prop) : Prop :=
  ∃ r, rb r i φ

/--
  Ind φ i ψ: "Individual i's reason for φ indicates ψ"

  In Lewis's terminology, φ "indicates" ψ for i if i has reason to believe
  the conditional "φ → ψ". This captures how evidence for one belief can
  serve as evidence for another.

  Note: This definition makes indication explicit as having a reason for an
  implication, which will allow us to prove properties that were axioms in
  other approaches.
-/
def Ind {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (φ : Prop) (i : indiv) (ψ : Prop) : Prop :=
  R rb i (φ → ψ)

-- ============================================================================
-- Axioms of Justification Logic
-- ============================================================================

/-
  The following axioms establish a logic of reasons based on Artemov's
  justification logic. These are presented as axioms for now, but in a
  fuller treatment they would be derived from the semantics of justification logic.

  Note: In an ideal formalization, we would define these as parameters of a
  structure rather than global axioms, to make the dependency structure clearer.
-/

/--
  Application Rule (AR): The fundamental rule of justification logic.

  If s is a reason for i to believe "α → β", and t is a reason for i to believe α,
  then s * t (the "application" of s to t) is a reason for i to believe β.

  This is the justification-logic analog of modus ponens, but with explicit
  tracking of which reasons were used in the inference.
-/
axiom AR {indiv reason : Type} [Mul reason] (rb : reason → indiv → Prop → Prop) :
  ∀ {s t : reason} {i : indiv} {α β : Prop},
  rb s i (α → β) → rb t i α → rb (s * t) i β

/--
  T1: Axiom for conjunction introduction.

  The constant reason 'a' justifies everyone in believing that having α and
  having β together justify believing (α ∧ β).

  This encodes the logical rule: from α and β, infer α ∧ β.
-/
axiom T1 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (a : reason) :
  ∀ {i : indiv} {α β : Prop}, rb a i (α → β → (α ∧ β))

/--
  T2: Axiom for transitivity of implication.

  The constant reason 'b' justifies everyone in believing that implications
  are transitive: if α → β and β → γ, then α → γ.

  This encodes the logical rule of hypothetical syllogism.
-/
axiom T2 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (b : reason) :
  ∀ {i : indiv} {α β γ : Prop}, rb b i (((α → β) ∧ (β → γ)) → (α → γ))

/--
  T3: Axiom for reasoning about others' reasoning.

  The constant reason 'c' justifies everyone in believing a meta-level principle:
  if j has reason to believe "α → β", and j has reason to believe α,
  then j has reason to believe β.

  This allows agents to reason about other agents' reasoning capabilities.
-/
axiom T3 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (c : reason) :
  ∀ {i j : indiv} {α β : Prop},
  rb c i (R rb j (α → β) → (R rb j α → R rb j β))

-- ============================================================================
-- Derived Rules and Lemmas
-- ============================================================================

/--
  E1: Modus ponens for the R operator.

  If i has reason to believe "α → β" and i has reason to believe α,
  then i has reason to believe β.

  This is a direct consequence of the application rule AR, showing how
  the explicit reason structure supports standard logical reasoning.
-/
lemma E1 {indiv reason : Type} [Mul reason] (rb : reason → indiv → Prop → Prop) :
    ∀ {i : indiv} {α β : Prop}, R rb i (α → β) → R rb i α → R rb i β := by
  intro i α β h1 h2
  rw [R] at *
  -- Extract the witnesses: s is a reason for α → β, t is a reason for α
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  -- Apply AR: s * t is a reason for β
  use s * t
  exact AR rb hs ht

/--
  L1: Conjunction introduction for R.

  If i has reason to believe α and reason to believe β,
  then i has reason to believe (α ∧ β).

  This uses the axiom T1 (for conjunction) and applies it twice via AR.
-/
lemma L1 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (a : reason) :
    ∀ {i : indiv} {α β : Prop}, R rb i α → R rb i β → R rb i (α ∧ β) := by
  intro i α β h1 h2
  rw [R] at *
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  -- First, apply T1 to s to get a reason for "β → (α ∧ β)"
  have h3 : rb (a * s) i (β → (α ∧ β)) := by
    have h4 : rb a i (α → (β → (α ∧ β))) := T1 rb a
    exact AR rb h4 hs
  -- Then apply this to t to get a reason for "α ∧ β"
  use a * s * t
  exact AR rb h3 ht

/--
  E2: Transitivity of implications for R.

  If i has reason to believe "α → β" and reason to believe "β → γ",
  then i has reason to believe "α → γ".

  This uses T2 (transitivity axiom) and builds up the required reason
  by combining existing reasons.
-/
lemma E2 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (a b : reason) :
    ∀ {i : indiv} {α β γ : Prop},
    R rb i (α → β) → R rb i (β → γ) → R rb i (α → γ) := by
  intro i α β γ h1 h2
  -- First, form the conjunction of the two implications
  have h3 : R rb i ((α → β) ∧ (β → γ)) := L1 rb a h1 h2
  obtain ⟨s, hs⟩ := h3
  -- Apply T2 to derive the transitive conclusion
  use b * s
  exact AR rb (T2 rb b) hs

/--
  E3: Lifting modus ponens to meta-level reasoning.

  If i has reason to believe "j has reason to believe (α → β)",
  then i has reason to believe "if j has reason to believe α,
  then j has reason to believe β".

  This allows i to reason about j's reasoning capabilities.
  Uses T3 (axiom for meta-reasoning).
-/
lemma E3 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (c : reason) :
    ∀ {i j : indiv} {α β : Prop},
    R rb i (R rb j (α → β)) → R rb i (R rb j α → R rb j β) := by
  intro i j α β h1
  obtain ⟨s, hs⟩ := h1
  use c * s
  exact AR rb (T3 rb c) hs

-- ============================================================================
-- Lewis's Axioms A1 and A6 as Theorems
-- ============================================================================

/-
  CRITICAL RESULT: Unlike Sillari's formalization where A1 and A6 were axioms
  (and A1 was shown to be inconsistent with the modal semantics), here we
  PROVE them from the more primitive justification logic axioms.

  This shows that the justification logic approach provides a more solid
  foundation for Lewis's theory.
-/

/--
  A1 (Lewis's first key axiom): Indication supports reasoning.

  If i's reason for A indicates α (i.e., i has reason to believe "A → α"),
  and i has reason to believe A, then i has reason to believe α.

  PROOF: This is simply an instance of modus ponens (E1), since Ind A i α
  is defined as R rb i (A → α).

  In Cubitt and Sugden's approach, this was taken as an axiom.
  In Sillari's modal approach, this was shown to FAIL (counterexample exists).
  Here, it's a trivial consequence of the definitions.
-/
lemma A1 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (A : Prop) :
    ∀ {i : indiv} {α : Prop}, Ind rb A i α → R rb i A → R rb i α := by
  intro i α h1 h2
  rw [Ind] at h1
  rw [R] at *
  obtain ⟨t, ht⟩ := h2
  obtain ⟨s, hs⟩ := h1
  -- s * t is the reason combining the implication with the antecedent
  use s * t
  exact AR rb hs ht

/-- Alternative proof of A1 using E1 directly (more concise) -/
lemma A1_alternative_proof {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (A : Prop) :
    ∀ {i : indiv} {α : Prop}, Ind rb A i α → R rb i A → R rb i α :=
  fun h1 h2 => E1 rb h1 h2

/--
  A6 (Lewis's composition axiom): Chaining indication through reasoning.

  If i's reason for A indicates "j has reason to believe A"
  (i.e., Ind A i (R j A)), and i has reason to believe "j's reason for A indicates α"
  (i.e., R i (Ind A j α)), then i's reason for A indicates "j has reason to believe α"
  (i.e., Ind A i (R j α)).

  This captures how indication composes through multiple agents' reasoning.

  PROOF: Uses E2 (transitivity) and E3 (meta-level reasoning) to chain
  the implications appropriately.

  In Cubitt and Sugden's approach, this was taken as an axiom.
  Here, it follows from the more primitive principles of justification logic.
-/
lemma A6 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (A : Prop) (a b c : reason) :
    ∀ α {i j : indiv},
    Ind rb A i (R rb j A) →
    R rb i (Ind rb A j α) →
    Ind rb A i (R rb j α) := by
  intro p i j h1 h2
  rw [Ind] at *
  -- h1: R i (A → R j A)
  -- h2: R i (R j (A → p))
  -- Goal: R i (A → R j p)

  -- First, use E3 to get: R i (R j A → R j p)
  have h3 : R rb i (R rb j A → R rb j p) := E3 rb c h2

  -- Then use E2 to chain: (A → R j A) and (R j A → R j p) gives (A → R j p)
  have h4 : R rb i (A → R rb j p) := E2 rb a b h1 h3
  exact h4

-- ============================================================================
-- R-Closure and Lewis's Main Theorem
-- ============================================================================

/--
  G φ p: "p is in the R-closure of φ"

  This is the inductive closure of φ under the operation "R i _" for any individual i.
  It represents the set of propositions that can be reached from φ by repeatedly
  applying "someone has reason to believe _".

  Examples in the closure of φ:
  - φ itself (base case)
  - R i φ (someone believes φ)
  - R j (R i φ) (someone believes that someone believes φ)
  - R k (R j (R i φ)) (three levels of nested belief)
  - etc.

  This is analogous to the RC definition in the first file, but using the
  existentially quantified R operator instead of requiring the individual
  to be a parameter.
-/
inductive G {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (φ : Prop) : Prop → Prop
  | base : G rb φ φ  -- φ is in its own closure
  | step (p : Prop) (i : indiv) : G rb φ p → G rb φ (R rb i p)
    -- If p is in the closure, so is "i has reason to believe p"

/--
  Lewis's Main Theorem: Common knowledge via R-closure

  Given the four conditions that Lewis identifies as constituting common knowledge:
  - C1: Everyone has reason to believe A (the common basis)
  - C2: Everyone indicates that everyone has reason to believe A
  - C3: Everyone indicates φ (the initial observation)
  - C4: If i indicates α, then i reasons that everyone indicates α

  Then: For any proposition p in the R-closure of φ, everyone has reason to believe p.

  This formalizes Lewis's key insight: under the right conditions, an initial
  observation φ becomes "common reason to believe" (everyone believes it, everyone
  believes everyone believes it, ad infinitum).

  PROOF STRATEGY:
  - By induction on the R-closure structure
  - Base case: C3 gives us that everyone indicates φ, then C1 and A1 give that everyone believes φ
  - Inductive case: Use C4 to lift indication, then A6 to compose indication, then A1 to conclude

  This proof is non-trivial and genuinely demonstrates how common knowledge arises
  from Lewis's four conditions, unlike the trivial proof in the global interpretation
  of Sillari's formalization.
-/
lemma Lewis {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (A φ : Prop) (a b c : reason) (p : Prop)
    (C1 : ∀ i, R rb i A)  -- Everyone has reason to believe the common basis
    (C2 : ∀ i j, Ind rb A i (R rb j A))  -- Everyone indicates everyone believes A
    (C3 : ∀ i, Ind rb A i φ)  -- Everyone indicates the initial observation
    (C4 : ∀ α i j, Ind rb A i α → R rb i (Ind rb A j α))  -- Indication propagates
    (h7 : G rb φ p) :  -- p is in the R-closure of φ
    ∀ i, R rb i p := by  -- Conclusion: everyone has reason to believe p
  intro i
  -- Key insight: we prove the stronger claim that Ind A i p, then apply A1
  have h1 : Ind rb A i p := by
    induction h7 with
    | base =>
        -- Base case: p = φ, so Ind A i φ holds by C3
        exact C3 _
    | step u j hu ih =>
        -- Inductive case: p = R j u, and we have ih: Ind A i u
        -- Goal: Ind A i (R j u)

        -- Step 1: From ih and C4, get R i (Ind A j u)
        have h3 : R rb i (Ind rb A j u) := C4 u _ _ ih

        -- Step 2: Apply A6 with C2 to get Ind A i (R j u)
        have h4 : R rb i (Ind rb A j u) → Ind rb A i (R rb j u) :=
          A6 rb A a b c u (C2 _ _)
        have h5 : Ind rb A i (R rb j u) := h4 h3
        exact h5
  -- Apply A1: from Ind A i p and C1, conclude R i p
  exact A1 rb A h1 (C1 _)

-- Verify the statement is well-formed and can be used
#check Lewis

/-
  SUMMARY:

  This justification logic approach to Lewis's convention theorem has several
  advantages over the modal logic approaches:

  1. **Explicit reasons**: Instead of just knowing that someone believes something,
     we can track WHY they believe it (what reason justifies the belief).

  2. **A1 and A6 are provable**: These crucial axioms, which failed in Sillari's
     approach, are theorems here. This gives us confidence that the formalization
     correctly captures Lewis's intended meaning.

  3. **Non-trivial proof**: Lewis's theorem has a genuine inductive proof that
     shows how common knowledge builds up through the R-closure structure.

  4. **Clearer logical structure**: The composition of reasons via multiplication
     makes explicit how different pieces of evidence combine.

  5. **Based on established logic**: Artemov's justification logic is a well-studied
     system with known semantics and proof theory.

  COMPARISON TO OTHER FILES:

  - vs. first file (direct approach): That approach parameterized everything
    by individuals and propositions, which worked but was more abstract.
    This approach makes the reason structure explicit.

  - vs. Sillari's file: Sillari's modal logic approach had fundamental problems
    (B3/A1 failed, theorem was either false or trivial). This approach fixes
    those issues by using explicit reasons.

  PHILOSOPHICAL INSIGHT:

  The success of this formalization suggests that Lewis's theory is best understood
  not purely in terms of modal operators (knowledge, belief), but in terms of
  explicit justifications and evidence. Common knowledge arises when there is a
  public, shared structure of reasons that everyone can access and reason about.
-/
