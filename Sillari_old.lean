/-
Copyright (c) 2023 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import Mathlib.Tactic

/-- A multi-agent Kripke frame: for each agent `i : Agent`, an accessibility relation on worlds. -/
structure MultiAgentFrame (Agent : Type) where
  /-- The type of possible worlds -/
  World : Type
  /-- Accessibility relation for each agent -/
  rel : Agent → World → World → Prop

variable {Agent : Type} {frame : MultiAgentFrame Agent}

def modal_imp (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => φ w → ψ w
infixr:90 " ⟶ₘ " => modal_imp

/-- Modal negation -/
def modal_neg (φ : frame.World → Prop) : frame.World → Prop :=
  fun w => ¬φ w
notation "¬ₘ" => modal_neg

/-- Modal conjunction -/
def modal_conj (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => φ w ∧ ψ w
infixr:70 " ∧ₘ " => modal_conj

/-- Modal disjunction -/
def modal_disj (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => φ w ∨ ψ w
infixr:65 " ∨ₘ " => modal_disj

/-- Validity (truth at all worlds) -/
def valid (φ : frame.World → Prop) : Prop := ∀ w, φ w
notation "⊢ " φ => valid φ


variable {f : MultiAgentFrame Agent}
variable {s t u v w : frame.World}
variable {A φ ψ γ : frame.World → Prop}
variable (i j i1 i2 : Agent)

/- Sillari's theory has to represent the two central concepts of Lewis' theory
   of common knowledge. The first one, reason to believe, is captured by the
   operator R that is defined in the file modal_logic_multi_agent.
   The second one, indication, is defined as follows. -/

def R (i : Agent) (φ : frame.World → Prop) : frame.World → Prop :=
    fun w => ∀v, frame.rel i w v → φ v

/- We define 'all agents have reason to believe φ' -/
def Rg (φ : frame.World → Prop) : frame.World → Prop :=
    fun w => ∀i, R i φ w

-- A world `w1` is *connected* to `w2` if some agent i relates them
def connected (w1 w2 : frame.World) : Prop :=
  ∃ i : Agent, frame.rel i w1 w2

-- Transitive closure of `connected`
inductive trcl (r : frame.World → frame.World → Prop) : frame.World → frame.World → Prop
| base {x y} : r x y → trcl r x y
| step {x y z} : r x y → trcl r y z → trcl r x z

lemma trcl.head {r : frame.World → frame.World → Prop} {x y z : frame.World}
    (h : r x y) (p : trcl r y z) : trcl r x z :=
  trcl.step h p

/-- CRB ψ s: ψ holds at every world reachable from s via the closure of `connected`. -/
def CRB (ψ : frame.World → Prop) (s : frame.World) : Prop :=
  ∀ w, trcl (connected : frame.World → frame.World → Prop) s w → ψ w

/-- If you can reach a world where ψ fails, then CRB ψ s is false. -/
lemma CRB.counterexample {ψ : frame.World → Prop} {s w : frame.World}
    (hsw : trcl (connected : frame.World → frame.World → Prop) s w) (hnot : ¬ ψ w) :
    ¬ CRB ψ s := by
  intro hCR
  exact hnot (hCR w hsw)

/-- A convenient “∃-form” for ¬CRB, useful with `simp`/`push_neg`. -/
lemma not_CRB_iff_exists {ψ : frame.World → Prop} {s : frame.World} :
    (¬ CRB ψ s) ↔ ∃ w, trcl (connected : frame.World → frame.World → Prop) s w ∧ ¬ ψ w := by
  classical
  unfold CRB
  constructor
  · intro h
    -- classical De Morgan on ∀/→
    -- ¬(∀ w, A w → ψ w) ⇒ ∃ w, A w ∧ ¬ ψ w
    by_contra h'
    have : ∀ w, trcl (connected : frame.World → frame.World → Prop) s w → ψ w := by
      intro w hw
      by_contra hψ
      exact h' ⟨w, hw, hψ⟩
    exact h this
  · rintro ⟨w, hw, hψ⟩ hCR
    exact hψ (hCR w hw)

/- Indication is defined in terms of Reason-to-believe and implication -/
def Ind (i : Agent) (φ : frame.World → Prop) (ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => R i φ w ∧ (φ w → ψ w)

/- this property expresses that a frame has at least three worlds -/
def three_worlds : frame.World → frame.World → frame.World → Prop :=
  fun w1 w2 w3 => w2 ≠ w1 ∧ w3 ≠ w2 ∧ w3 ≠ w1

/- this property expresses that a frame has at least two worlds -/
def two_worlds : frame.World → frame.World→ Prop :=
  fun w1 w2 => w1 ≠ w2

/- this property expresses that there are exactly two individuals -/
def two_agents : Agent → Agent → Prop :=
  fun i1 i2 => i1 ≠ i2 ∧ ∀i, i = i1 ∨ i = i2

/- this property expresses that there is exactly one individual -/
def one_agent : Agent → Prop := fun i1 => ∀i, i = i1

/- Sillari mixes a proof-theoretic account with eleven axioms B1 - B8 and
    B10 - B11 and a semantic account with his modal definitions of R and Ind.
    We prove that all but three of the axioms can be derived as lemmas from the
    definitions of R and Ind.
    Axiom B3 contradicts the definitions: we provide a counterexample.
    Axioms B7 and B8 will not be discussed because they play no role in Sillari's
    argument. -/

lemma B1 : ∀w, R i φ w → R i (φ ⟶ₘ ψ) w → R i ψ w := by
intros v h1 h2 u h3
rw [R] at *
have h4 : φ u := h1 u h3
have h5 : (φ ⟶ₘ ψ) u := h2 u h3
exact h5 h4


lemma B2 : ∀w, R i φ w → (φ ⟶ₘ ψ) w → Ind i φ ψ w := by
intro w h1 h2
--rw [Ind]
constructor
{ assumption  }
{ intro h3
  --rw [modal_imp] at h2
  exact h2 h3 }

/- Lemma B3 states: ∀w, R r i φ w → Ind r i φ ψ w → R r i ψ w.
    This is not true, as we will show by a counterexample, a model with two worlds.
    that is problematic for Sillari because he needs this axiom in his proof of
    Lewis' theorem.
    B3 is the same as Lewis' A1 -/

lemma B3_fails
(h1 : two_worlds s t)
(h2a : ¬ frame.rel i s s) (h2b : frame.rel i s t) :
    ¬ (∀w (φ ψ : frame.World → Prop), R i φ w → Ind i φ ψ w → R i ψ w) := by
let ψ := fun w => w ≠ t
let φ := fun w => w ≠ s
push_neg
have h4 : R i φ s := by rw [R]; aesop
have h5 : Ind i φ ψ s := by rw [Ind]; aesop
have h6 : ¬ R i ψ s := by
  -- If R i ψ s held, then ψ t would hold, i.e. t ≠ t, contradiction.
  intro hR
  exact (hR t h2b) rfl

refine ⟨s, φ, ψ, ?_, ?_, ?_⟩
· exact h4
· exact h5
· exact h6

lemma B4 : ∀w, Ind i φ γ w → Ind i γ ψ w → Ind i φ ψ w := by
intro w h1 h2
--rw [Ind] at *
constructor
{ exact h1.1 }
{ have h4 : φ w → γ w := h1.2
  have h5 : γ w → ψ w := h2.2
  intro hw
  exact h5 (h4 hw)  }


lemma B5 : (⊢  φ) → (⊢  (φ ⟶ₘ ψ)) → (⊢  ψ) := by
intro h1 h2
--rw [m_valid] at *
intro w
exact h2 w (h1 w)


lemma B6 : (⊢  φ) → (⊢  R i φ) := by
intro h1 u
rw [R]
intro v _
exact h1 v

/- Sillari also states axioms B7 (positive introspection) and B8 (negative
    introspection), but he does not use these axioms, and they do not follow from
    the semantics.
    Axiom B7 : ⊢ (R r i φ →ₘ R r i (R r i φ))
    Axiom B8 : ⊢ (R r i φ →ₘ ¬ₘ (R r i (¬ₘ φ))
    These axioms would imply that the relations of the frame are transitive and
    serial. -/

lemma B10 : ⊢ CRB φ ⟶ₘ Rg (φ ∧ₘ CRB φ) := by
  intro s hCR
  -- need: ∀ i t, frame.rel i s t → (φ ∧ₘ CRB φ) t
  intro i t hst
  constructor
  · -- φ t
    exact hCR t (trcl.base ⟨i, hst⟩)
  · -- CRB φ t
    intro w htw
    exact hCR w (trcl.step ⟨i, hst⟩ htw)


lemma B11 : (⊢  φ ⟶ₘ Rg (ψ ∧ₘ φ)) → ⊢  (φ ⟶ₘ CRB ψ) := by
  -- Unpack validity of φ ⟶ Rg (ψ ∧ φ)
  intro hvalid
  -- Show validity of φ ⟶ CRB ψ: fix an arbitrary world s with φ s
  intro s hφs
  -- Propagate (ψ ∧ φ) along any reachable path from the start world
  have propagate :
      ∀ {x y}, φ x →
        trcl (connected : frame.World → frame.World → Prop) x y →
        (ψ y ∧ φ y) := by
    intro x y hφx hxy
    induction hxy with
    | base hconn =>
        -- Single step: use Rg (ψ ∧ φ) at x
        rename_i x y
        rcases hconn with ⟨j, hj⟩
        have hRg : Rg (ψ ∧ₘ φ) x := (hvalid x) hφx
        exact hRg j y hj
    | step hconn hrest ih =>
        -- Name endpoints to keep types aligned
        rename_i x y z
        rcases hconn with ⟨j, hj⟩
        have hRg : Rg (ψ ∧ₘ φ) x := (hvalid x) hφx
        have hy : (ψ ∧ₘ φ) y := hRg j y hj
        -- Continue on the tail of the path using φ y
        exact ih hy.2

  -- Conclude CRB ψ at s by projecting the ψ-component
  intro w hsw
  exact (propagate hφs hsw).1

/- Cubitt and Sugden's axiom C4 fails. This proves that Sillari's formalisation does not match
    the account of common knowledge that Lewis gave. -/

lemma C4_fails (h2a : ¬ frame.rel i s s) (h2b : frame.rel i s t) :
    ¬ ∀w (φ ψ : frame.World → Prop), (Ind i φ ψ w → R i (Ind j φ ψ) w) := by
let φ := fun _ : frame.World => True
let ψ := fun w : frame.World => w = s
push_neg
have h3 : Ind i φ ψ s := by
  --rw[Ind]
  constructor
  { --rw [R]
    intro w _
    aesop }
  { aesop }
have h3a : ¬ R i (Ind j φ ψ) s := by
  rw [R]
  push_neg
  use t
  constructor
  { exact h2b }
  { intro hn
    --rw [Ind] at hn
    have hphi : φ t := by aesop
    have hp : ψ t := hn.2 hphi
    have h3b : ¬ ψ t := by aesop
    aesop
  }
use s, φ, ψ

/- Now we discuss Sillari's proof of Lewis' theorem. It is not clear how to
   interpret his proof. Therefore, two options are presented. The first option makes
   it impossible to find a proof. The second option gives a valid proof, but
   the proof is trivial and thus useless. -/

/- option 1 : C1 - C3 are only assumed at the world for which the theorem has to
    hold. First, we provide a counterexample with one agent and a frame with three
    worlds. In this counterexample, the frame is nor transitive nor serial. -/

/-- Main lemma: choose φ := (· ≠ s) and ψ := (· = u) to witness failure. -/
lemma Lewis_fails_1i
    (h3w : three_worlds s u v) -- pass the proof as a hypothesis
    (hrel :
    frame.rel =
      (fun (_ : Agent) (w1 w2 : frame.World) =>
        (w1 = s ∧ w2 = u) ∨ (w1 = u ∧ w2 = v)))
     : ∃ (φ : frame.World → Prop),
      R i1 φ s ∧
      Ind i1 (R i1 φ) (R i1 (R i1 φ)) s ∧
      Ind i1 (R i1 φ) (R i1 (fun w => w = u)) s ∧
      ¬ CRB (fun w => w = u) s := by
    -- Unpack distinctness of the three worlds
  obtain ⟨hsu, hvu, hvs⟩ : u ≠ s ∧ v ≠ u ∧ v ≠ s := by
    simpa [three_worlds] using h3w    -- Choose φ and ψ
  let φ : frame.World → Prop := fun w => w ≠ s
  let ψ : frame.World → Prop := fun w => w = u

  -- One-step edges from the concrete frame
  have rel_s_u : frame.rel i1 s u := by
    have : (s = s ∧ u = u) ∨ (s = u ∧ u = v) := Or.inl ⟨rfl, rfl⟩
    simp [hrel]
  have rel_u_v : frame.rel i1 u v := by
    have : (u = s ∧ v = u) ∨ (u = u ∧ v = v) := Or.inr ⟨rfl, rfl⟩
    simp [hrel]

  -- Any successor of s is u
  have succ_s_eq_u :
      ∀ w, frame.rel i1 s w → w = u := by
    intro w hw
    have hw' :
        (s = s ∧ w = u) ∨ (s = u ∧ w = v) := by
      simpa [hrel] using hw
    cases hw' with
    | inl h => exact h.2
    | inr h => exact (hsu.symm h.1).elim

  -- Any successor of u is v
  have succ_u_eq_v :
      ∀ x, frame.rel i1 u x → x = v := by
    intro x hx
    have hx' :
        (u = s ∧ x = u) ∨ (u = u ∧ x = v) := by
      simpa [hrel] using hx
    cases hx' with
    | inl h => exact (hsu h.1).elim
    | inr h => exact h.2

  -- (1) R i1 φ s
  have hRphi_s : R i1 φ s := by
    intro w hw
    have : w = u := succ_s_eq_u w hw
    -- φ u is u ≠ s
    simpa [φ, this] using hsu

  -- (2) R i1 (R i1 φ) s
  have hR_Rphi_s : R i1 (R i1 φ) s := by
    -- need: ∀ w, frame.rel i1 s w → R i1 φ w
    intro w hw
    -- need: ∀ x, frame.rel i1 w x → φ x
    intro x hx
    -- w = u and x = v; φ v is v ≠ s
    have hw_u : w = u := succ_s_eq_u w hw
    have hx_v : x = v := by
      subst hw_u
      exact succ_u_eq_v x hx
    simpa [φ, hx_v] using hvs

  -- (3) Ind i1 (R i1 φ) (R i1 (R i1 φ)) s
  have hInd1 : Ind i1 (R i1 φ) (R i1 (R i1 φ)) s := by
    -- Ind expects: ⟨ R i1 (R i1 φ) s , (R i1 φ s → R i1 (R i1 φ) s) ⟩
    exact ⟨hR_Rphi_s, fun _ => hR_Rphi_s⟩

  -- (4) Ind i1 (R i1 φ) (R i1 ψ) s
  -- First, show R i1 ψ s
  have hRpsi_s : R i1 ψ s := by
    intro w hw
    have : w = u := succ_s_eq_u w hw
    simp [ψ, this]

  have hInd2 : Ind i1 (R i1 φ) (R i1 ψ) s := by
    -- Ind expects: ⟨ R i1 (R i1 φ) s , (R i1 φ s → R i1 ψ s) ⟩
    exact ⟨hR_Rphi_s, fun _ => hRpsi_s⟩

  -- (5) ¬ CRB (fun w => w = u) s, proved directly (no CRB anywhere)
  have hNotCR : ¬ CRB (fun w => w = u) s := by
    intro hCR
    -- 2-step path s → u → v
    have hsv : trcl connected s v :=
      trcl.head ⟨i1, rel_s_u⟩ (trcl.base ⟨i1, rel_u_v⟩)
    -- CRB forces (w = u) at v, contradiction with hvu : v ≠ u
    have : v = u := hCR v hsv
    exact hvu this

  -- Package the witnesses
  exact ⟨φ, hRphi_s, hInd1, hInd2, hNotCR⟩

/- In case we accept axioms B7 and B8, we have to provide a counterexample with a
    frame that is transitive and serial. That is possible: -/
lemma Lewis_fails_2i
(h1 : three_worlds s u v)
(h2 : two_agents i1 i2)
(h3 : frame.rel = fun i w1 w2 => (i = i1 ∧ w1 = s ∧ w2 = u) ∨ (i = i1 ∧ w1 = u ∧ w2 = u)
∨ (w1 = v ∧ w2 = v) ∨ (i = i2 ∧ w1 = s ∧ w2 = s) ∨ (i = i2 ∧ w1 = u ∧ w2 = v))
: ¬ ∀ i φ ψ, Rg φ s → Ind i (Rg φ) (Rg (Rg φ)) s → Ind i (Rg φ) (Rg ψ) s → CRB ψ s := by
rw [two_agents] at h2
rw [three_worlds] at h1
let φ : frame.World → Prop := fun _ => True
let ψ : frame.World → Prop := fun w => w ≠ v
push_neg
use i1, φ, ψ
have h41 : Rg φ s := by
    --rw [Rg]
    intro i w
    have h4a : i = i1 ∨ i = i2 := h2.right i
    cases h4a with
    | inl i1 => aesop
    | inr i2 => aesop
have h42a : Rg (Rg φ) s := by
  rw [Rg]
  intro i x
  rw [Rg]
  intro _ w hw
  aesop
have h42 : Ind i1 (Rg φ) (Rg (Rg φ)) s := by
    rw [Ind]
    constructor
    { exact h42a i1  }
    { intro _; exact h42a}
have h43 : Ind i1 (Rg φ) (Rg ψ) s := by
  --rw [Ind]
  constructor
  { exact h42a i1 }
  { intro hphi
    rw [Rg]
    intro i
    rw [R]
    intro w
    aesop    }
have h44 : ¬ CRB ψ s := by
  rw [CRB]
  push_neg
  use v
  simp
  have h5a : connected s u := by use i1; aesop
  have h5b : connected u v := by use i2; aesop
  exact trcl.head h5a (trcl.base h5b)
aesop

/- option 2 : C1 - C3 are assumed to hold at each world
    Now, the proof is rather trivial
    C2 is even not used -/
lemma lewis_s_2
(C1 : ∀ w, Rg φ w)
(C3 : ∀ w, Ind i (Rg φ) (Rg ψ) w) :
  CRB ψ s := by
  have hRgψ_all : ∀ w, Rg ψ w := fun w => (C3 w).2 (C1 w)
  intro v hv
  induction hv with
  | base h_edge =>
      -- The endpoints of this base case are fresh; name them explicitly:
      rename_i x y
      rcases h_edge with ⟨j, hj⟩
      -- hRgψ_all : ∀ w, Rg ψ w  where Rg ψ w ≡ ∀ j v, frame.rel j w v → ψ v
      exact (hRgψ_all x) j y hj
  | step _ _ ih =>
      exact ih
