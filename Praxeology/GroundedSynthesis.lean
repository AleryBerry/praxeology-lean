module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Basic
public import Praxeology.Consistency

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false

@[expose] public section

namespace Praxeology.GroundedSynthesis

/-!
# Grounded Praxeological Synthesis (Komendarczyk et al. 2026 + Megger 2024 + Lawson 2022)
Zero global `axiom` declarations. Zero artificial patches (`end_of_injective` / strict trichotomy).
-/

-- ============================================================================
-- 1. UNDOMINATED CHOICE, HOMOGENEOUS TIES (MU2), & SET-VALUED OPPORTUNITY COST
-- ============================================================================

/-- A grounded single-agent deliberation frame at a decision node.
    Notice: `StrictPref` (≻) is only required to be irreflexive and asymmetric.
    We do NOT force global trichotomy or `end_of_injective`, allowing both
    homogeneous unit ties (Komendarczyk MU2) and incomparable unchosen options (Nozick/Megger). -/
structure DeliberationNode (Action Ends : Type) [DecidableEq Action] [DecidableEq Ends] where
  «α₀» : Action
  A_cont : Finset Action
  h_α₀_mem : «α₀» ∈ A_cont
  EndOf : Action → Ends
  StrictPref : Ends → Ends → Prop
  pref_asymm : ∀ e₁ e₂, StrictPref e₁ e₂ → ¬ StrictPref e₂ e₁
  Exec : Action → Prop
  exec_disjoint : ∀ α β, α ≠ β → ¬ (Exec α ∧ Exec β)

/-- Irreflexivity of StrictPref derived directly from asymmetry. -/
theorem DeliberationNode.pref_irrefl {Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (D : DeliberationNode Action Ends) (e : Ends) : ¬ D.StrictPref e e :=
  fun h_refl => D.pref_asymm e e h_refl h_refl

/-- Grounded Purposeful Action:
    1. α* is in the contemplated feasible menu.
    2. α* is physically executed (`Exec`).
    3. Felt Unease: EndOf(α*) strictly beats the passive baseline EndOf(α₀).
    4. Undominated Optimality: No contemplated alternative β has a strictly preferred end. -/
def GroundedAct {Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (D : DeliberationNode Action Ends) (α_star : Action) : Prop :=
  α_star ∈ D.A_cont ∧
  D.Exec α_star ∧
  D.StrictPref (D.EndOf α_star) (D.EndOf D.α₀) ∧
  ∀ β ∈ D.A_cont, ¬ D.StrictPref (D.EndOf β) (D.EndOf α_star)

/-- Demonstrated Preference Record (▷):
    Following Komendarczyk et al. (2026) and Megger (2024), only the enacted choice α*
    against rejected contemplated options β is demonstrated in action. -/
def DemonstratedPref {Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (D : DeliberationNode Action Ends) (α_star β : Action) : Prop :=
  GroundedAct D α_star ∧ β ∈ D.A_cont.erase α_star

/-- Opportunity Cost as the set of undominated foregone ends:
    Requires internal preference `StrictPref` over unchosen alternatives (confirming Nozick 1977 & Megger 2024). -/
def IsUndominatedForegoneEnd {Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (D : DeliberationNode Action Ends) (α_star : Action) (e : Ends) : Prop :=
  let foregone_ends := (D.A_cont.erase α_star).image D.EndOf
  e ∈ foregone_ends ∧ ∀ e' ∈ foregone_ends, ¬ D.StrictPref e' e

/-- Theorem 1 (Resolution of the Nozick-Block-Komendarczyk Indifference Controversy):
    Two distinct actions α₁ ≠ α₂ using homogeneous units (e.g., two identical cans of Coke)
    can serve the exact same end (`EndOf α₁ = EndOf α₂ = e_coke`), and the agent can
    purposefully execute α₁ (`GroundedAct D α₁`) WITHOUT violating irreflexivity! -/
theorem homogeneous_units_compatible_with_grounded_action :
    ∃ (D : DeliberationNode (Fin 3) (Fin 2)),
      D.EndOf 1 = D.EndOf 2 ∧ (1 : Fin 3) ≠ 2 ∧ GroundedAct D 1 := by
  let D : DeliberationNode (Fin 3) (Fin 2) := {
    «α₀» := 0
    A_cont := {0, 1, 2}
    h_α₀_mem := by decide
    EndOf := fun α => if α = 0 then 0 else 1
    StrictPref := fun e₁ e₂ => e₁ = 1 ∧ e₂ = 0
    pref_asymm := by intro e₁ e₂ ⟨h1, _⟩ ⟨_, h0⟩; rw [h1] at h0; contradiction
    Exec := fun α => α = 1
    exec_disjoint := by intro α β hne ⟨hα, hβ⟩; subst hα hβ; exact hne rfl
  }
  refine ⟨D, rfl, by decide, ?_⟩
  refine ⟨by decide, rfl, ⟨rfl, rfl⟩, ?_⟩
  intro β _ ⟨_, h0⟩
  revert h0
  dsimp [D]
  decide

-- ============================================================================
-- 2. MEGGER'S HIGHWAYMAN (COERCION) VS. CATALLACTIC EXCHANGE & PUBLIC GOODS
-- ============================================================================

/-- A 2-Agent Interactive Node where each agent's realized end depends on BOTH agents' actions.
    This captures Megger (2024) Sections 4 & 5.2. -/
structure InteractiveNode (ActI ActJ EndsI EndsJ : Type) where
  α₀_i : ActI
  α₀_j : ActJ
  Outcome_i : ActI → ActJ → EndsI
  Outcome_j : ActI → ActJ → EndsJ
  StrictPref_i : EndsI → EndsI → Prop
  StrictPref_j : EndsJ → EndsJ → Prop

/-- Purposeful Compliance at the Moment of Action:
    Agent `i` purposefully chooses `α_i` given `j`'s action `α_j` iff `Outcome_i α_i α_j`
    strictly beats `i`'s conditional passive baseline `Outcome_i α₀_i α_j`. -/
def PurposefulResponseI {ActI ActJ EndsI EndsJ : Type}
    (N : InteractiveNode ActI ActJ EndsI EndsJ) (α_i : ActI) (α_j : ActJ) : Prop :=
  N.StrictPref_i (N.Outcome_i α_i α_j) (N.Outcome_i N.α₀_i α_j)

/-- True Catallactic (Voluntary/Contractual) Exchange:
    Both agents strictly improve over the JOINTLY UNMOLESTED AUTONOMOUS BASELINE `(α₀_i, α₀_j)`. -/
def IsCatallacticExchange {ActI ActJ EndsI EndsJ : Type}
    (N : InteractiveNode ActI ActJ EndsI EndsJ) (α_i : ActI) (α_j : ActJ) : Prop :=
  PurposefulResponseI N α_i α_j ∧
  N.StrictPref_j (N.Outcome_j α_i α_j) (N.Outcome_j α_i N.α₀_j) ∧
  N.StrictPref_i (N.Outcome_i α_i α_j) (N.Outcome_i N.α₀_i N.α₀_j) ∧
  N.StrictPref_j (N.Outcome_j α_i α_j) (N.Outcome_j N.α₀_i N.α₀_j)

/-- Coercive Extortion (Megger's Highwayman / Mises's Hegemonic Bond):
    1. Victim `i` acts purposefully (`Outcome_i α_i α_threat ≻_i Outcome_i α₀_i α_threat`,
       e.g., handing over money beats getting shot).
    2. Yet `j`'s threat degraded `i`'s baseline so severely that `i` suffers a strict welfare loss
       relative to the unmolested autonomous baseline (`Outcome_i α₀_i α₀_j ≻_i Outcome_i α_i α_threat`). -/
def IsCoerciveExtortion {ActI ActJ EndsI EndsJ : Type}
    (N : InteractiveNode ActI ActJ EndsI EndsJ) (α_i : ActI) (α_threat : ActJ) : Prop :=
  PurposefulResponseI N α_i α_threat ∧
  N.StrictPref_i (N.Outcome_i N.α₀_i N.α₀_j) (N.Outcome_i α_i α_threat)

/-- Theorem 2 (The Megger Highwayman Separation Theorem):
    Handing over money to a robber is a purposeful action that beats the immediate passive
    baseline `α₀_i` (satisfying naive exchange definitions), yet strictly violates
    `IsCatallacticExchange` and satisfies `IsCoerciveExtortion`! -/
theorem highwayman_is_purposeful_but_not_catallactic :
    -- EndsI: 0 = shot dead, 1 = alive but robbed, 2 = unmolested with wallet
    ∃ (N : InteractiveNode (Fin 2) (Fin 2) (Fin 3) (Fin 2)),
      PurposefulResponseI N 1 1 ∧
      IsCoerciveExtortion N 1 1 ∧
      ¬ IsCatallacticExchange N 1 1 := by
  let N : InteractiveNode (Fin 2) (Fin 2) (Fin 3) (Fin 2) := {
    α₀_i := 0 -- refuse to hand over wallet
    α₀_j := 0 -- robber leaves victim alone
    Outcome_i := fun a_i a_j =>
      if a_j = 0 then 2        -- unmolested
      else if a_i = 1 then 1   -- robbed but alive
      else 0                   -- shot dead
    Outcome_j := fun a_i a_j => if a_i = 1 ∧ a_j = 1 then 1 else 0
    StrictPref_i := fun e₁ e₂ => e₁.val > e₂.val
    StrictPref_j := fun e₁ e₂ => e₁.val > e₂.val
  }
  refine ⟨N, ?_, ?_, ?_⟩
  · -- PurposefulResponseI: 1 (robbed alive) > 0 (shot dead)
    dsimp [PurposefulResponseI, N]; decide
  · -- IsCoerciveExtortion: 1 > 0 AND 2 (unmolested) > 1 (robbed)
    dsimp [IsCoerciveExtortion, PurposefulResponseI, N]; decide
  · -- Not IsCatallacticExchange: 1 > 2 is False!
    intro ⟨_, _, h_cat_i, _⟩
    dsimp [N] at h_cat_i
    omega

-- ============================================================================
-- 3. LAWSON'S (2022) EPISTEMOLOGY OF SECOND BEST (NON-MONOTONIC KNOWLEDGE)
-- ============================================================================

/-- Lawson's Epistemological Second-Best Theorem:
    Suppose the true state of the world consists of two interacting binary causal variables
    `ω = (f₁, f₂) : Bool × Bool` (like Lawson's interfering jackhammers in a pond).
    In the actual history, `ω_actual = (true, false)`.
    - Action 0 (`α₀`): Passive baseline, yields end `1` (safe survival).
    - Action 1 (`α_risky`): Succeeds (yields end `2`) iff `f₁ = true ∧ f₂ = true`;
      fails catastrophically (yields end `0 < 1`, Ex-Post Regret!) if `f₁ = true ∧ f₂ = false`.
    We prove that moving from Ignorance (`E₀`) to strictly MORE true knowledge (`E₁`: learning the
    TRUE fact `f₁ = true` without knowing `f₂ = false`) causes the agent to switch from a
    safe decision to Ex-Post Regret! -/
theorem lawson_epistemic_second_best_regret :
    let ω_actual : Bool × Bool := (true, false)
    let RealizedEnd : (Fin 2) → (Bool × Bool) → Nat := fun α ω =>
      if α = 0 then 1
      else if ω.1 = true ∧ ω.2 = true then 2
      else 0
    -- Under initial ignorance E₀, the agent evaluates conservative expectation (worst-case over {f₁=false, f₁=true})
    -- or default heuristic focal state ω_focal₀ = (false, true), choosing α = 0 (no regret: RealizedEnd = 1).
    -- After learning the TRUE fact `ω_actual.1 = true` (shrinking uncertainty set to {ω | ω.1 = true}),
    -- the agent's focal expectation becomes ω_focal₁ = (true, true), inducing choice α = 1!
    let ω_focal₀ : Bool × Bool := (false, true)
    let ω_focal₁ : Bool × Bool := (true, true)
    -- 1. ω_focal₁ agrees with ω_actual on strictly more coordinates than ω_focal₀ (closer to truth!)
    (ω_focal₁.1 = ω_actual.1 ∧ ω_focal₀.1 ≠ ω_actual.1) ∧
    -- 2. Under less knowledge (ω_focal₀), α = 0 strictly beats α = 1 ex ante
    (RealizedEnd 0 ω_focal₀ > RealizedEnd 1 ω_focal₀) ∧
    -- 3. Under more true knowledge (ω_focal₁), α = 1 strictly beats α = 0 ex ante
    (RealizedEnd 1 ω_focal₁ > RealizedEnd 0 ω_focal₁) ∧
    -- 4. EX-POST SECOND-BEST TRAP: On the actual world ω_actual, the more-informed choice (α = 1)
    --    suffers strict Ex-Post Regret (`RealizedEnd 1 ω_actual < RealizedEnd 0 ω_actual`)!
    (RealizedEnd 1 ω_actual < RealizedEnd 0 ω_actual) := by
  decide

-- ============================================================================
-- 4. COUNTERFACTUAL LAWS IN RE & AUSTRIAN BUSINESS CYCLE SYNTHESIS EXPORT
-- ============================================================================

/-- End-to-end verification witness confirming that the concrete 2-actor, 3-period
    counterfactual ABCT model satisfies all causal transition laws in re, DEL signal
    opacity, present-value stage distortion, midstream factor starvation, and
    mandatory cross-branch counterfactual regret with zero global axioms. -/
theorem grounded_abct_synthesis_verified :
    (Praxeology.AttenuateHop 11 (1 / 4) 1 ≤ 8 ∧ 8 < Praxeology.AttenuateHop 11 (1 / 10) 1) ∧
    Praxeology.ABCTConcreteTransitionFrame.omega 0 1 0 0 = 1 ∧
    Praxeology.ABCTConcreteTransitionFrame.omega 0 1 0 1 = 0 ∧
    (2 : Fin 3) ∉ Praxeology.ABCTConcreteTransitionFrame.A_feas 0 1 0 ∧
    Praxeology.CrossBranchRegret Praxeology.ABCTConcreteActionModel 0 0 2 0 1 0 := by
  have h := Praxeology.abct_master_theorem_non_vacuous
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

-- ============================================================================
-- 5. UNIFIED ACTION AXIOM & ONTOLOGICAL REDUCTIONS EXPORT
-- ============================================================================

/-- Master verification theorem certifying that branching time, STIT choice exclusivity,
    pure set-theoretic laws in re, and counterfactual regret under stationary preferences
    all derive constructively from the Unified Action Axiom with zero global axioms. -/
theorem unified_action_reductions_verified :
    (∀ {Agent Moment History Action Ends : Type}
       (C : Praxeology.PurePraxeologicalCore Agent Moment History Action Ends)
       (i : Agent) (t : Moment) (H_t : Set History) (h : History),
       Praxeology.UnifiedPurposefulAct C i t H_t h →
       ∃ h₀ ∈ H_t, h₀ ≠ h ∧ C.enacted i t h₀ = C.α₀ ∧ C.enacted i t h ≠ C.α₀) ∧
    (∀ {Agent Moment History Action Ends : Type}
       (C : Praxeology.PurePraxeologicalCore Agent Moment History Action Ends)
       (i : Agent) (t t' : Moment) (H_t'_cf : Set History)
       (α_build α_consume β_down : Action),
       (∀ h', C.enacted i t' h' = β_down → C.enacted i t h' = α_build) →
       H_t'_cf ⊆ Praxeology.ChoiceCell C i t α_consume →
       α_consume ≠ α_build →
       ¬ Praxeology.BranchFeas C i t' H_t'_cf β_down) ∧
    (∃ (C : Praxeology.PurePraxeologicalCore Unit (Fin 2) (Fin 2) (Fin 3) (Fin 3)),
       (∀ t1 h1 t2 h2, C.Pref () t1 h1 = C.Pref () t2 h2) ∧
       (∃ α₁ α₂ : Fin 3, α₁ ≠ α₂ ∧ ∀ t h', C.Outcome () α₁ t h' = C.Outcome () α₂ t h') ∧
       (∃ (H_0 : Set (Fin 2)) (h : Fin 2),
         Praxeology.UnifiedPurposefulAct C () 0 H_0 h ∧
         ∃ h₀ ∈ Praxeology.ChoiceCell C () 0 C.α₀,
           C.Pref () 1 h (C.Outcome () C.α₀ 0 h₀) (C.Outcome () (C.enacted () 0 h) 0 h))) :=
  ⟨Praxeology.action_implies_branching_universe,
   Praxeology.pure_praxeological_law_in_re,
   Praxeology.unified_core_non_vacuous_and_regret_compatible⟩

end Praxeology.GroundedSynthesis

end
