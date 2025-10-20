/-
Copyright (c) 2023 Huub Vromen. All rights reserved.
Author: Huub Vromen

Formalization of Sillari's modal logic analysis of Lewis's convention theory.

This file examines Sillari's attempted formalization of David Lewis's theory of
common knowledge and conventions. We show that Sillari's axiomatization has issues:
- Some of Lewis's axioms (like B3/A1) fail under Sillari's definitions
- Cubitt and Sugden's axiom C4 also fails
- Lewis's main theorem either lacks proof or becomes trivial depending on interpretation
-/

import Mathlib.Tactic

/-- A multi-agent Kripke frame: for each agent `i : Agent`, an accessibility relation on worlds. -/
structure MultiAgentFrame (Agent : Type) where
  /-- The type of possible worlds -/
  World : Type
  /-- Accessibility relation for each agent: rel i w v means agent i considers v accessible from w -/
  rel : Agent → World → World → Prop

variable {Agent : Type} {frame : MultiAgentFrame Agent}

-- ============================================================================
-- Modal Operators
-- ============================================================================

/-- Modal implication: (φ ⟶ₘ ψ) w means "at world w, φ implies ψ" -/
def modal_imp (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => φ w → ψ w
infixr:90 " ⟶ₘ " => modal_imp

/-- Modal negation: (¬ₘ φ) w means "φ does not hold at world w" -/
def modal_neg (φ : frame.World → Prop) : frame.World → Prop :=
  fun w => ¬φ w
notation "¬ₘ" => modal_neg

/-- Modal conjunction: (φ ∧ₘ ψ) w means "both φ and ψ hold at world w" -/
def modal_conj (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => φ w ∧ ψ w
infixr:70 " ∧ₘ " => modal_conj

/-- Modal disjunction: (φ ∨ₘ ψ) w means "φ or ψ (or both) hold at world w" -/
def modal_disj (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => φ w ∨ ψ w
infixr:65 " ∨ₘ " => modal_disj

/-- Validity: φ is valid if it holds at all worlds -/
def valid (φ : frame.World → Prop) : Prop := ∀ w, φ w
notation "⊢ " φ => valid φ

-- ============================================================================
-- Core Epistemic Operators (Lewis/Sillari)
-- ============================================================================

variable {f : MultiAgentFrame Agent}
variable {s t u v w : frame.World}
variable {A φ ψ γ : frame.World → Prop}
variable (i j i1 i2 : Agent)

/--
  R i φ w: Agent i has "reason to believe" φ at world w.
  This means φ holds at all worlds accessible to i from w.
  This captures Lewis's first central concept: "reason to believe".
-/
def R (i : Agent) (φ : frame.World → Prop) : frame.World → Prop :=
    fun w => ∀ v, frame.rel i w v → φ v

/--
  Rg φ w: All agents have reason to believe φ at world w.
  This is the "group" or "everyone" version of R.
-/
def Rg (φ : frame.World → Prop) : frame.World → Prop :=
    fun w => ∀ i, R i φ w

/--
  Ind i φ ψ w: Agent i's belief in φ "indicates" ψ at world w.
  This captures Lewis's second central concept: "indication".
  It means: (1) i has reason to believe φ, and (2) φ materially implies ψ at w.
-/
def Ind (i : Agent) (φ : frame.World → Prop) (ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => R i φ w ∧ (φ w → ψ w)

-- ============================================================================
-- Common Reason to Believe (CRB) via Reachability
-- ============================================================================

/--
  connected w1 w2: There exists some agent i who relates w1 to w2.
  This is the union of all agents' accessibility relations.
-/
def connected (w1 w2 : frame.World) : Prop :=
  ∃ i : Agent, frame.rel i w1 w2

/--
  trcl r: Transitive closure of a binary relation r.
  trcl r x z holds if there's a path from x to z following r one or more times.
-/
inductive trcl (r : frame.World → frame.World → Prop) : frame.World → frame.World → Prop
| base {x y} : r x y → trcl r x y  -- Single step: x → y
| step {x y z} : r x y → trcl r y z → trcl r x z  -- Multi-step: x → y → ... → z

/-- Convenience lemma: prepend a step to an existing path -/
lemma trcl.head {r : frame.World → frame.World → Prop} {x y z : frame.World}
    (h : r x y) (p : trcl r y z) : trcl r x z :=
  trcl.step h p

/--
  CRB ψ s: ψ is "common reason to believe" at world s.
  This means ψ holds at every world reachable from s via the transitive closure
  of the connected relation (i.e., via any sequence of agents' accessibility relations).
-/
def CRB (ψ : frame.World → Prop) (s : frame.World) : Prop :=
  ∀ w, trcl (connected : frame.World → frame.World → Prop) s w → ψ w

/-- If you can reach a world where ψ fails, then CRB ψ does not hold. -/
lemma CRB.counterexample {ψ : frame.World → Prop} {s w : frame.World}
    (hsw : trcl (connected : frame.World → frame.World → Prop) s w) (hnot : ¬ ψ w) :
    ¬ CRB ψ s := by
  intro hCR
  exact hnot (hCR w hsw)

/-- Useful characterization: ¬CRB ψ s iff there exists a reachable world where ψ fails -/
lemma not_CRB_iff_exists {ψ : frame.World → Prop} {s : frame.World} :
    (¬ CRB ψ s) ↔ ∃ w, trcl (connected : frame.World → frame.World → Prop) s w ∧ ¬ ψ w := by
  classical
  unfold CRB
  constructor
  · intro h
    -- Use classical logic: ¬(∀ w, A w → ψ w) ⇒ ∃ w, A w ∧ ¬ ψ w
    by_contra h'
    have : ∀ w, trcl (connected : frame.World → frame.World → Prop) s w → ψ w := by
      intro w hw
      by_contra hψ
      exact h' ⟨w, hw, hψ⟩
    exact h this
  · rintro ⟨w, hw, hψ⟩ hCR
    exact hψ (hCR w hw)

-- ============================================================================
-- Frame Properties (for counterexamples)
-- ============================================================================

/-- A frame has at least three distinct worlds -/
def three_worlds : frame.World → frame.World → frame.World → Prop :=
  fun w1 w2 w3 => w2 ≠ w1 ∧ w3 ≠ w2 ∧ w3 ≠ w1

/-- A frame has at least two distinct worlds -/
def two_worlds : frame.World → frame.World → Prop :=
  fun w1 w2 => w1 ≠ w2

/-- There are exactly two agents -/
def two_agents : Agent → Agent → Prop :=
  fun i1 i2 => i1 ≠ i2 ∧ ∀ i, i = i1 ∨ i = i2

/-- There is exactly one agent -/
def one_agent : Agent → Prop :=
  fun i1 => ∀ i, i = i1

-- ============================================================================
-- Sillari's Axioms B1-B11: Which ones hold?
-- ============================================================================

/-
  Sillari presents eleven axioms (B1-B8, B10-B11) in a proof-theoretic style,
  combined with semantic definitions of R and Ind via Kripke frames.

  We investigate which axioms follow from the semantic definitions.

  Results:
  - B1, B2, B4, B5, B6: These are PROVABLE as lemmas from the definitions
  - B3: This FAILS (we provide a counterexample) - problematic since Lewis needs this
  - B7, B8: Not discussed (positive/negative introspection; require special frame properties)
  - B10, B11: These are PROVABLE
-/

/-- B1: Modal modus ponens for R (K axiom for each agent) -/
lemma B1 : ∀ w, R i φ w → R i (φ ⟶ₘ ψ) w → R i ψ w := by
  intros v h1 h2 u h3
  -- At world u (accessible from v): φ u and (φ → ψ) u both hold, so ψ u holds
  rw [R] at *
  have h4 : φ u := h1 u h3
  have h5 : (φ ⟶ₘ ψ) u := h2 u h3
  exact h5 h4

/-- B2: If i reasons to φ and φ implies ψ at w, then i's reason for φ indicates ψ -/
lemma B2 : ∀ w, R i φ w → (φ ⟶ₘ ψ) w → Ind i φ ψ w := by
  intro w h1 h2
  -- Ind requires: i has reason to believe φ, and φ → ψ at w
  constructor
  { assumption }
  { intro h3
    exact h2 h3 }

/--
  B3 FAILS: The claim "R i φ w ∧ Ind i φ ψ w → R i ψ w" does not hold.

  This is Sillari's version of Lewis's axiom A1, which is crucial for Lewis's argument.
  The failure shows a fundamental problem with Sillari's formalization.

  Counterexample: A two-world frame where i relates s to t but not s to itself.
  Let φ = "world ≠ s" and ψ = "world ≠ t".
  Then R i φ s and Ind i φ ψ s both hold, but R i ψ s fails (since ψ t is false).
-/
lemma B3_fails
  (h1 : two_worlds s t)  -- s and t are distinct
  (h2a : ¬ frame.rel i s s)  -- i doesn't relate s to itself
  (h2b : frame.rel i s t) :  -- i relates s to t
    ¬ (∀ w (φ ψ : frame.World → Prop), R i φ w → Ind i φ ψ w → R i ψ w) := by
  let ψ := fun w => w ≠ t  -- ψ says "not at world t"
  let φ := fun w => w ≠ s  -- φ says "not at world s"
  push_neg
  -- R i φ s holds: the only successor of s is t, and φ t (i.e., t ≠ s) is true
  have h4 : R i φ s := by rw [R]; aesop
  -- Ind i φ ψ s holds: R i φ s ∧ (φ s → ψ s), and both conjuncts are true
  have h5 : Ind i φ ψ s := by rw [Ind]; aesop
  -- But R i ψ s fails: at successor t, we have ¬ψ t (i.e., ¬(t ≠ t))
  have h6 : ¬ R i ψ s := by
    intro hR
    exact (hR t h2b) rfl
  -- Package the counterexample
  refine ⟨s, φ, ψ, ?_, ?_, ?_⟩
  · exact h4
  · exact h5
  · exact h6

/-- B4: Transitivity of indication -/
lemma B4 : ∀ w, Ind i φ γ w → Ind i γ ψ w → Ind i φ ψ w := by
  intro w h1 h2
  constructor
  { exact h1.1 }  -- R i φ w holds from first premise
  { -- Chain the implications: φ → γ → ψ
    have h4 : φ w → γ w := h1.2
    have h5 : γ w → ψ w := h2.2
    intro hw
    exact h5 (h4 hw) }

/-- B5: Modus ponens for valid formulas -/
lemma B5 : (⊢ φ) → (⊢ (φ ⟶ₘ ψ)) → (⊢ ψ) := by
  intro h1 h2 w
  exact h2 w (h1 w)

/-- B6: Necessitation rule - valid formulas are believed by everyone everywhere -/
lemma B6 : (⊢ φ) → (⊢ R i φ) := by
  intro h1 u
  rw [R]
  intro v _
  exact h1 v

/-
  B7 and B8 (positive and negative introspection) are not provable from the semantics alone.
  They would require the accessibility relations to be transitive (B7) and serial (B8).
  Sillari states these axioms but does not use them in his main argument.
-/

/-- B10: If ψ is CRB at s, then everyone at s reasons to "ψ and CRB ψ" -/
lemma B10 : ⊢ CRB φ ⟶ₘ Rg (φ ∧ₘ CRB φ) := by
  intro s hCR i t hst
  -- Show: ∀ i t, frame.rel i s t → (φ ∧ₘ CRB φ) t
  constructor
  · -- φ holds at t because it's reachable from s in one step
    exact hCR t (trcl.base ⟨i, hst⟩)
  · -- CRB φ holds at t: any world reachable from t was reachable from s
    intro w htw
    exact hCR w (trcl.step ⟨i, hst⟩ htw)

/-- B11: If φ always indicates "everyone believes (ψ ∧ φ)", then φ implies CRB ψ -/
lemma B11 : (⊢ φ ⟶ₘ Rg (ψ ∧ₘ φ)) → ⊢ (φ ⟶ₘ CRB ψ) := by
  intro hvalid s hφs
  -- Show: at any world s where φ holds, CRB ψ also holds
  -- Key insight: (ψ ∧ φ) propagates along any reachable path from s
  have propagate :
      ∀ {x y}, φ x →
        trcl (connected : frame.World → frame.World → Prop) x y →
        (ψ y ∧ φ y) := by
    intro x y hφx hxy
    induction hxy with
    | base hconn =>
        -- One-step case: use the hypothesis that φ x implies Rg (ψ ∧ φ) x
        rename_i x y
        rcases hconn with ⟨j, hj⟩
        have hRg : Rg (ψ ∧ₘ φ) x := (hvalid x) hφx
        exact hRg j y hj
    | step hconn hrest ih =>
        -- Multi-step case: apply one step then use induction
        rename_i x y z
        rcases hconn with ⟨j, hj⟩
        have hRg : Rg (ψ ∧ₘ φ) x := (hvalid x) hφx
        have hy : (ψ ∧ₘ φ) y := hRg j y hj
        -- Continue from y using φ y
        exact ih hy.2
  -- Conclude: ψ holds at any world reachable from s
  intro w hsw
  exact (propagate hφs hsw).1

-- ============================================================================
-- Cubitt and Sugden's Axiom C4 Also Fails
-- ============================================================================

/--
  C4 FAILS: The claim "Ind i φ ψ w → R i (Ind j φ ψ) w" does not hold.

  This is Cubitt and Sugden's axiom, which should hold if Sillari's formalization
  correctly captures Lewis's account of common knowledge. The failure is more
  evidence that Sillari's approach is problematic.

  Counterexample: Two-world frame, φ = True, ψ = "world = s".
  Agent i relates s to t. Then Ind i φ ψ s holds, but R i (Ind j φ ψ) s fails
  because at world t, Ind j φ ψ is false (since ψ t is false).
-/
lemma C4_fails
  (h2a : ¬ frame.rel i s s)  -- i doesn't relate s to itself
  (h2b : frame.rel i s t) :  -- i relates s to t
    ¬ ∀ w (φ ψ : frame.World → Prop), (Ind i φ ψ w → R i (Ind j φ ψ) w) := by
  let φ := fun _ : frame.World => True  -- φ is always true
  let ψ := fun w : frame.World => w = s  -- ψ says "at world s"
  push_neg
  -- Ind i φ ψ s holds trivially
  have h3 : Ind i φ ψ s := by
    constructor
    { intro w _; aesop }
    { aesop }
  -- But R i (Ind j φ ψ) s fails: at world t, we have ¬(Ind j φ ψ t)
  have h3a : ¬ R i (Ind j φ ψ) s := by
    rw [R]
    push_neg
    use t
    constructor
    { exact h2b }
    { intro hn
      -- At t, ψ t is false but φ t is true, contradicting the implication in Ind
      have hphi : φ t := by aesop
      have hp : ψ t := hn.2 hphi
      have h3b : ¬ ψ t := by aesop
      aesop }
  use s, φ, ψ

-- ============================================================================
-- Lewis's Theorem: Two Interpretations, Both Problematic
-- ============================================================================

/-
  Sillari attempts to prove Lewis's main theorem about conventions and common knowledge.
  However, it's unclear how to interpret his proof. We examine two possible readings:

  Option 1: Assumptions C1-C3 hold only at the specific world s where we want the conclusion.
           Problem: The theorem is FALSE (we give counterexamples).

  Option 2: Assumptions C1-C3 hold at ALL worlds.
           Problem: The proof becomes TRIVIAL and the theorem is vacuous/useless.
-/

section LewisTheoremOption1

/-
  Option 1: Local assumptions at world s only

  We show this interpretation fails by constructing explicit counterexamples.
  The frames need not be transitive or serial.
-/

/--
  Counterexample 1: One agent, three worlds.

  Frame structure: s → u → v (linear chain)

  We choose φ := (· ≠ s) and demonstrate:
  - R i φ s holds
  - The required Ind conditions hold at s
  - But CRB (fun w => w = u) s fails (because v is reachable and v ≠ u)
-/
lemma Lewis_fails_1i
    (h3w : three_worlds s u v)  -- s, u, v are three distinct worlds
    (hrel :
      frame.rel =
        (fun (_ : Agent) (w1 w2 : frame.World) =>
          (w1 = s ∧ w2 = u) ∨ (w1 = u ∧ w2 = v)))  -- Linear: s → u → v
     : ∃ (φ : frame.World → Prop),
      R i1 φ s ∧
      Ind i1 (R i1 φ) (R i1 (R i1 φ)) s ∧
      Ind i1 (R i1 φ) (R i1 (fun w => w = u)) s ∧
      ¬ CRB (fun w => w = u) s := by
  -- Unpack: s, u, v are pairwise distinct
  obtain ⟨hsu, hvu, hvs⟩ : u ≠ s ∧ v ≠ u ∧ v ≠ s := by
    simpa [three_worlds] using h3w

  -- Define the propositions
  let φ : frame.World → Prop := fun w => w ≠ s  -- "not at s"
  let ψ : frame.World → Prop := fun w => w = u  -- "at u"

  -- Extract the frame structure
  have rel_s_u : frame.rel i1 s u := by
    have : (s = s ∧ u = u) ∨ (s = u ∧ u = v) := Or.inl ⟨rfl, rfl⟩
    simp [hrel]
  have rel_u_v : frame.rel i1 u v := by
    have : (u = s ∧ v = u) ∨ (u = u ∧ v = v) := Or.inr ⟨rfl, rfl⟩
    simp [hrel]

  -- Helper: only successor of s is u
  have succ_s_eq_u :
      ∀ w, frame.rel i1 s w → w = u := by
    intro w hw
    have hw' : (s = s ∧ w = u) ∨ (s = u ∧ w = v) := by
      simpa [hrel] using hw
    cases hw' with
    | inl h => exact h.2
    | inr h => exact (hsu.symm h.1).elim

  -- Helper: only successor of u is v
  have succ_u_eq_v :
      ∀ x, frame.rel i1 u x → x = v := by
    intro x hx
    have hx' : (u = s ∧ x = u) ∨ (u = u ∧ x = v) := by
      simpa [hrel] using hx
    cases hx' with
    | inl h => exact (hsu h.1).elim
    | inr h => exact h.2

  -- (1) R i1 φ s: agent i1 has reason to believe φ at s
  have hRphi_s : R i1 φ s := by
    intro w hw
    have : w = u := succ_s_eq_u w hw
    simpa [φ, this] using hsu

  -- (2) R i1 (R i1 φ) s: agent i1 has reason to believe "i1 has reason to believe φ"
  have hR_Rphi_s : R i1 (R i1 φ) s := by
    intro w hw
    intro x hx
    have hw_u : w = u := succ_s_eq_u w hw
    have hx_v : x = v := by
      subst hw_u
      exact succ_u_eq_v x hx
    simpa [φ, hx_v] using hvs

  -- (3) The first Ind condition holds at s
  have hInd1 : Ind i1 (R i1 φ) (R i1 (R i1 φ)) s := by
    exact ⟨hR_Rphi_s, fun _ => hR_Rphi_s⟩

  -- (4) R i1 ψ s: agent i1 has reason to believe ψ at s
  have hRpsi_s : R i1 ψ s := by
    intro w hw
    have : w = u := succ_s_eq_u w hw
    simp [ψ, this]

  -- (5) The second Ind condition holds at s
  have hInd2 : Ind i1 (R i1 φ) (R i1 ψ) s := by
    exact ⟨hR_Rphi_s, fun _ => hRpsi_s⟩

  -- (6) But CRB fails: there's a 2-step path s → u → v, and ψ v is false
  have hNotCR : ¬ CRB (fun w => w = u) s := by
    intro hCR
    -- Build path: s → u → v
    have hsv : trcl connected s v :=
      trcl.head ⟨i1, rel_s_u⟩ (trcl.base ⟨i1, rel_u_v⟩)
    -- CRB would force v = u, contradicting hvu
    have : v = u := hCR v hsv
    exact hvu this

  -- Package all the witnesses
  exact ⟨φ, hRphi_s, hInd1, hInd2, hNotCR⟩

/--
  Counterexample 2: Two agents, three worlds (with transitive, serial relations if desired).

  This shows the failure persists even with nicer frame properties (for those
  who accept axioms B7/B8 requiring transitivity and seriality).
-/
lemma Lewis_fails_2i
  (h1 : three_worlds s u v)  -- Three distinct worlds
  (h2 : two_agents i1 i2)  -- Two distinct agents
  (h3 : frame.rel = fun i w1 w2 =>
    (i = i1 ∧ w1 = s ∧ w2 = u) ∨
    (i = i1 ∧ w1 = u ∧ w2 = u) ∨  -- i1's relation is transitive at u
    (w1 = v ∧ w2 = v) ∨  -- Reflexive at v for all agents
    (i = i2 ∧ w1 = s ∧ w2 = s) ∨  -- i2 reflexive at s
    (i = i2 ∧ w1 = u ∧ w2 = v))  -- i2 connects u to v
  : ¬ ∀ i φ ψ, Rg φ s → Ind i (Rg φ) (Rg (Rg φ)) s → Ind i (Rg φ) (Rg ψ) s → CRB ψ s := by
  rw [two_agents] at h2
  rw [three_worlds] at h1

  let φ : frame.World → Prop := fun _ => True  -- φ is always true
  let ψ : frame.World → Prop := fun w => w ≠ v  -- ψ says "not at v"
  push_neg
  use i1, φ, ψ

  -- Rg φ s: everyone has reason to believe φ at s (trivial since φ = True)
  have h41 : Rg φ s := by
    intro i w
    have h4a : i = i1 ∨ i = i2 := h2.right i
    cases h4a with
    | inl i1 => aesop
    | inr i2 => aesop

  -- Rg (Rg φ) s: everyone has reason to believe "everyone has reason to believe φ"
  have h42a : Rg (Rg φ) s := by
    rw [Rg]
    intro i x
    rw [Rg]
    intro _ w hw
    aesop

  -- First Ind condition
  have h42 : Ind i1 (Rg φ) (Rg (Rg φ)) s := by
    rw [Ind]
    constructor
    { exact h42a i1 }
    { intro _; exact h42a }

  -- Second Ind condition (Rg ψ holds at s)
  have h43 : Ind i1 (Rg φ) (Rg ψ) s := by
    constructor
    { exact h42a i1 }
    { intro hphi
      rw [Rg]
      intro i
      rw [R]
      intro w
      aesop }

  -- But CRB ψ s fails: v is reachable via s → u → v, and ψ v is false
  have h44 : ¬ CRB ψ s := by
    rw [CRB]
    push_neg
    use v
    simp-- Build the path s → u → v using both agents
    have h5a : connected s u := by use i1; aesop
    have h5b : connected u v := by use i2; aesop
    exact trcl.head h5a (trcl.base h5b)

  aesop

end LewisTheoremOption1

-- ============================================================================
-- Lewis's Theorem: Option 2 (Global assumptions - trivial proof)
-- ============================================================================

section LewisTheoremOption2

/-
  Option 2: Global assumptions at ALL worlds

  If we interpret C1-C3 as holding at every world (not just at s), then Lewis's
  theorem becomes trivially true, but also vacuous and useless for the intended
  purpose of analyzing conventions.

  The "proof" is straightforward but reveals the theorem says nothing interesting
  in this interpretation.
-/

/--
  Lewis's theorem (trivial version): If the assumptions hold globally, CRB follows trivially.

  Assumptions:
  - C1: Rg φ w holds at every world w (everyone always believes φ everywhere)
  - C2: Ind i (Rg φ) (Rg (Rg φ)) w holds at every world w (not used in proof!)
  - C3: Ind i (Rg φ) (Rg ψ) w holds at every world w

  Conclusion: CRB ψ s (ψ is common reason to believe at s)

  The proof is trivial: C3 at any world w gives us Rg ψ w (everyone believes ψ at w).
  Since this holds everywhere, ψ holds at all accessible worlds, hence CRB ψ s.

  Note: C2 is completely unused! This suggests the global interpretation misses
  the intended logical structure of Lewis's argument.
-/
lemma lewis_s_2
  (C1 : ∀ w, Rg φ w)  -- Everyone believes φ at every world
  (C3 : ∀ w, Ind i (Rg φ) (Rg ψ) w) :  -- At every world, Rg φ indicates Rg ψ
    CRB ψ s := by
  -- From C3: at any world w, since Rg φ w holds (by C1), we get Rg ψ w
  have hRgψ_all : ∀ w, Rg ψ w := fun w => (C3 w).2 (C1 w)
  -- Now show CRB ψ s: ψ holds at all worlds reachable from s
  intro v hv
  induction hv with
  | base h_edge =>
      -- Base case: v is one step from some world x
      rename_i x y
      rcases h_edge with ⟨j, hj⟩
      -- Since Rg ψ x holds, and j relates x to y, we have ψ y
      exact (hRgψ_all x) j y hj
  | step _ _ ih =>
      -- Inductive case: just use the induction hypothesis
      exact ih

end LewisTheoremOption2

-- ============================================================================
-- Summary and Conclusions
-- ============================================================================

/-
  Summary of findings:

  1. **Sillari's axioms B1, B2, B4, B5, B6, B10, B11** are all provable from the
     semantic definitions of R and Ind. These are sound.

  2. **Axiom B3 FAILS**: This is Lewis's crucial axiom A1, and it does not follow
     from Sillari's semantic definitions. We proved this with an explicit
     counterexample (two-world frame). This is a serious problem since Lewis's
     original argument depends on this axiom.

  3. **Axiom C4 (Cubitt & Sugden) FAILS**: Another indication that Sillari's
     formalization doesn't correctly capture Lewis's theory.

  4. **Lewis's main theorem** has two possible interpretations, both problematic:
     - **Local interpretation** (assumptions only at world s): The theorem is FALSE.
       We provided counterexamples with 1 agent (3 worlds) and 2 agents (3 worlds).
     - **Global interpretation** (assumptions at all worlds): The theorem is TRUE
       but TRIVIAL. The proof is vacuous and doesn't capture the intended epistemic
       reasoning about conventions. Moreover, assumption C2 is completely unused,
       suggesting this interpretation misses the logical structure.

  5. **Conclusion**: Sillari's modal logic formalization has fundamental issues and
     does not successfully capture Lewis's account of common knowledge and conventions.
     The failure of B3/A1 is particularly problematic, and the ambiguity in
     interpreting Lewis's theorem suggests the formalization needs significant revision.
-/
