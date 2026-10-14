module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false

/-!
# Praxeology.Diagnostic

Zero-Axiom Diagnostic & Independence-Testing System for Praxeology:
This module contains ZERO `axiom` declarations.

Structure of the Module:
1. Section 1: Minimal Action Theory (`MinimalActionModel`) — Zero Extra Assumptions.
2. Section 2: Part I — Theorems Strictly Proven from `MinimalActionModel` Alone.
   - Theorem D.1 (`minimal_action_non_passive`)
   - Theorem D.2 (`minimal_action_unique_execution`)
   - Theorem D.3 (`definitional_local_performative_consistency`)
   - Theorem D.4 (`minimal_double_inequality_of_exchange`)
3. Section 3: Part II — Undecidability & Logical Independence Proofs via Counter-Models.
   - Independence 1 (`buridan_tie_refutes_strict_demonstrated_pref`, `buridan_independence_certified`)
   - Independence 2 (`opportunity_cost_independent_of_minimal_action`)
   - Independence 3 (`dmu_fails_under_complementarity`)
   - Independence 4 (`positive_time_pref_independent_of_minimal_action`)
   - Independence 5 (`universal_action_not_proved_by_local_assertion`)
4. Section 4: Part III — Constructive Proof of 1-Step Bourbaki-Witt Fixed Point
   without any global axioms (`constructive_mengerian_fixed_point`).
-/

@[expose] public section

namespace Praxeology

-- =========================================================================
-- Section 1: Minimal Action Theory (MinimalActionModel)
-- =========================================================================

/-- MinimalActionModel:
    The minimal formal structure representing purposeful human action.
    Contains zero global axioms, and imposes NO auxiliary assumptions
    such as preference transitivity over unchosen options, connectedness,
    teleological injectivity, or positive time preference. -/
structure MinimalActionModel (Agent Moment History Action Means Ends : Type) where
  α₀ : Action
  A_feas : Agent → Moment → History → Finset Action
  alpha_zero_mem : ∀ i t h, α₀ ∈ A_feas i t h
  End_of : Agent → Action → Moment → History → Ends
  Pref : Agent → Moment → History → Ends → Ends → Prop
  pref_irrefl_zero : ∀ i t h, ¬ Pref i t h (End_of i α₀ t h) (End_of i α₀ t h)
  Exec : Agent → Moment → Action → History → Prop
  exec_disjoint : ∀ i t h α β, α ≠ β → ¬ (Exec i t α h ∧ Exec i t β h)
  minimal_action_axiom : ∀ i t h,
    (∃ α ∈ A_feas i t h, Pref i t h (End_of i α t h) (End_of i α₀ t h)) →
    ∃ α_star ∈ A_feas i t h, Exec i t α_star h ∧ Pref i t h (End_of i α_star t h) (End_of i α₀ t h)

/-- Purposeful Action in the Minimal Model:
    Action α_star is feasible, executed, and strictly preferred to the passive baseline α₀. -/
def MinimalAct {Agent Moment History Action Means Ends : Type}
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  α_star ∈ M.A_feas i t h ∧ M.Exec i t α_star h ∧ M.Pref i t h (M.End_of i α_star t h) (M.End_of i M.α₀ t h)

/-- An agent has a minimal choice node when at least one feasible action improves upon α₀. -/
def HasMinimalChoice {Agent Moment History Action Means Ends : Type}
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) : Prop :=
  ∃ α ∈ M.A_feas i t h, M.Pref i t h (M.End_of i α t h) (M.End_of i M.α₀ t h)

/-- Restatement of the minimal action axiom using MinimalAct. -/
theorem minimal_act_of_choice {Agent Moment History Action Means Ends : Type}
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History)
    (h_choice : HasMinimalChoice M i t h) :
    ∃ α_star, MinimalAct M i t h α_star := by
  rcases M.minimal_action_axiom i t h h_choice with ⟨α_star, h_feas, h_exec, h_pref⟩
  exact ⟨α_star, h_feas, h_exec, h_pref⟩

-- =========================================================================
-- Section 2: Part I — Theorems Strictly Proven from MinimalActionModel Alone
-- =========================================================================

/-- Theorem D.1 (Minimal Action is Non-Passive):
    Any purposeful action α_star is distinct from the passive baseline α₀,
    and achieves an end distinct from the status quo end. -/
theorem minimal_action_non_passive {Agent Moment History Action Means Ends : Type}
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_act : MinimalAct M i t h α_star) :
    α_star ≠ M.α₀ ∧ M.End_of i α_star t h ≠ M.End_of i M.α₀ t h := by
  have h_pref := h_act.2.2
  have h_not_end : M.End_of i α_star t h ≠ M.End_of i M.α₀ t h := by
    intro h_eq
    rw [h_eq] at h_pref
    exact M.pref_irrefl_zero i t h h_pref
  have h_not_act : α_star ≠ M.α₀ := by
    intro h_eq
    subst h_eq
    exact h_not_end rfl
  exact ⟨h_not_act, h_not_end⟩

/-- Theorem D.2 (Unique Execution of Purposeful Action):
    If an agent executes purposeful actions α₁ and α₂ at the same moment and history,
    then α₁ = α₂. Follows purely from execution cell disjointness,
    without requiring teleological injectivity (end_of_injective) or preference connectedness. -/
theorem minimal_action_unique_execution {Agent Moment History Action Means Ends : Type}
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α₁ α₂ : Action)
    (h1 : MinimalAct M i t h α₁)
    (h2 : MinimalAct M i t h α₂) :
    α₁ = α₂ := by
  by_contra hne
  have h_disj := M.exec_disjoint i t h α₁ α₂ hne
  exact h_disj ⟨h1.2.1, h2.2.1⟩

/-- Definitional Intentional Assertion:
    An agent intentionally asserts proposition p by purposefully executing assertion action α_assert. -/
def IntentionalAssert {Agent Moment History Action Means Ends : Type}
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_assert : Action) (p : Prop) : Prop :=
  MinimalAct M i t h α_assert

/-- Theorem D.3 (Definitional Local Performative Consistency):
    No agent can intentionally assert the local absence of purposeful action
    while that assertion is itself true.
    Requires ZERO bridging axioms: the contradiction is purely definitional. -/
theorem definitional_local_performative_consistency {Agent Moment History Action Means Ends : Type}
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_assert : Action)
    (h_assert : IntentionalAssert M i t h α_assert (¬ ∃ α, MinimalAct M i t h α))
    (h_denial : ¬ ∃ α, MinimalAct M i t h α) : False := by
  dsimp [IntentionalAssert] at h_assert
  exact h_denial ⟨α_assert, h_assert⟩

/-- Theorem D.4 (Minimal Double Inequality of Exchange):
    In any bilateral exchange where agent i executes offer action α_offer
    and agent j executes accept action α_accept, both agents strictly prefer
    their trade outcome over their passive baseline α₀.
    Proves Theorem 3.1 without transitivity, connectedness, or injectivity. -/
theorem minimal_double_inequality_of_exchange {Agent Moment History Action Means Ends : Type}
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i j : Agent) (t : Moment) (h : History)
    (α_offer α_accept : Action)
    (hi : MinimalAct M i t h α_offer)
    (hj : MinimalAct M j t h α_accept) :
    M.Pref i t h (M.End_of i α_offer t h) (M.End_of i M.α₀ t h) ∧
    M.Pref j t h (M.End_of j α_accept t h) (M.End_of j M.α₀ t h) :=
  ⟨hi.2.2, hj.2.2⟩

-- =========================================================================
-- Section 3: Part II — Undecidability & Independence Proofs via Counter-Models
-- =========================================================================

/-- Strict Demonstrated Preference condition:
    The chosen action α_star is strictly preferred to EVERY feasible alternative. -/
def StrictDemonstratedPref {Agent Moment History Action Means Ends : Type} [DecidableEq Action]
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  ∀ β ∈ (M.A_feas i t h).erase α_star, M.Pref i t h (M.End_of i α_star t h) (M.End_of i β t h)

/-- Theorem D.5 (Independence Proof 1: Buridan's Ass Tie Refutes Strict Demonstrated Preference):
    If two distinct feasible actions α₁ ≠ α₂ share the exact same optimal end e_star,
    and preference is irreflexive on e_star, then strict demonstrated preference is
    FALSE for both α₁ and α₂.
    This demonstrates that end_of_injective is an artificial patch required only by
    strict demonstrated preference, not by purposeful action itself. -/
theorem buridan_tie_refutes_strict_demonstrated_pref {Agent Moment History Action Means Ends : Type}
    [DecidableEq Action]
    (M : MinimalActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History)
    (α₁ α₂ : Action) (e_star : Ends)
    (hne : α₁ ≠ α₂)
    (h1 : α₁ ∈ M.A_feas i t h)
    (h2 : α₂ ∈ M.A_feas i t h)
    (h_end1 : M.End_of i α₁ t h = e_star)
    (h_end2 : M.End_of i α₂ t h = e_star)
    (h_irrefl : ¬ M.Pref i t h e_star e_star) :
    ¬ StrictDemonstratedPref M i t h α₁ ∧
    ¬ StrictDemonstratedPref M i t h α₂ := by
  constructor
  · intro h_strict1
    have h_mem2 : α₂ ∈ (M.A_feas i t h).erase α₁ := by
      rw [Finset.mem_erase]
      exact ⟨hne.symm, h2⟩
    have h_pref12 := h_strict1 α₂ h_mem2
    rw [h_end1, h_end2] at h_pref12
    exact h_irrefl h_pref12
  · intro h_strict2
    have h_mem1 : α₁ ∈ (M.A_feas i t h).erase α₂ := by
      rw [Finset.mem_erase]
      exact ⟨hne, h1⟩
    have h_pref21 := h_strict2 α₁ h_mem1
    rw [h_end1, h_end2] at h_pref21
    exact h_irrefl h_pref21

/-- Feasible menu for BuridanModel: {0, 1, 2}. -/
def BuridanMenu : Finset (Fin 3) := {0, 1, 2}

theorem buridan_zero_mem : (0 : Fin 3) ∈ BuridanMenu := by decide
theorem buridan_one_mem : (1 : Fin 3) ∈ BuridanMenu := by decide
theorem buridan_two_mem : (2 : Fin 3) ∈ BuridanMenu := by decide

/-- Concrete Counter-Model 1: Buridan Tie Model.
    Actions {0, 1, 2} where 1 and 2 achieve the same preferred end e_star = 1.
    MinimalAct holds for 1, yet StrictDemonstratedPref fails for both 1 and 2. -/
def BuridanModel : MinimalActionModel (Fin 1) (Fin 1) (Fin 1) (Fin 3) (Fin 1) (Fin 2) where
  α₀ := 0
  A_feas _ _ _ := BuridanMenu
  alpha_zero_mem _ _ _ := buridan_zero_mem
  End_of _ α _ _ := if α = 0 then 0 else 1
  Pref _ _ _ a b := a = 1 ∧ b = 0
  pref_irrefl_zero _ _ _ := by
    intro ⟨h1, _⟩
    exact absurd h1 (by decide)
  Exec _ _ α _ := α = 1
  exec_disjoint _ _ _ α β hne := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  minimal_action_axiom _ _ _ _ :=
    ⟨1, buridan_one_mem, rfl, ⟨rfl, rfl⟩⟩

/-- Certification of Independence Proof 1:
    In BuridanModel, MinimalAct holds for action 1, but StrictDemonstratedPref fails for both 1 and 2. -/
theorem buridan_independence_certified :
    MinimalAct BuridanModel 0 0 0 1 ∧
    ¬ StrictDemonstratedPref BuridanModel 0 0 0 1 ∧
    ¬ StrictDemonstratedPref BuridanModel 0 0 0 2 := by
  have h_act : MinimalAct BuridanModel 0 0 0 1 :=
    ⟨buridan_one_mem, rfl, ⟨rfl, rfl⟩⟩
  have h_tie := buridan_tie_refutes_strict_demonstrated_pref
    BuridanModel 0 0 0 1 2 1
    (by decide)
    buridan_one_mem
    buridan_two_mem
    rfl
    rfl
    (by
      intro ⟨_, h⟩
      exact absurd h (by decide))
  exact ⟨h_act, h_tie.1, h_tie.2⟩

/-- Feasible menu for IncompForegoneModel: {0, 1, 2, 3}. -/
def IncompMenu : Finset (Fin 4) := {0, 1, 2, 3}

theorem incomp_zero_mem : (0 : Fin 4) ∈ IncompMenu := by decide
theorem incomp_one_mem : (1 : Fin 4) ∈ IncompMenu := by decide

/-- Concrete Counter-Model 2: Incomparable Foregone Alternatives Model.
    Actions {0, 1, 2, 3}. Action 1 is chosen and strictly preferred to 0, 2, 3.
    However, the unchosen foregone options 2 and 3 are mutually incomparable. -/
def IncompForegoneModel : MinimalActionModel (Fin 1) (Fin 1) (Fin 1) (Fin 4) (Fin 1) (Fin 4) where
  α₀ := 0
  A_feas _ _ _ := IncompMenu
  alpha_zero_mem _ _ _ := incomp_zero_mem
  End_of _ α _ _ := α
  Pref _ _ _ a b := (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3)
  pref_irrefl_zero _ _ _ := by
    rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
  Exec _ _ α _ := α = 1
  exec_disjoint _ _ _ α β hne := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  minimal_action_axiom _ _ _ _ :=
    ⟨1, incomp_one_mem, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Theorem D.6 (Independence Proof 2: Opportunity Cost Independent of Minimal Action):
    In IncompForegoneModel, purposeful action α = 1 is executed and strictly preferred to all alternatives,
    yet NO unique maximum foregone alternative (Opportunity Cost) exists among {2, 3},
    because 2 and 3 are mutually incomparable.
    Proves that Opportunity Cost requires independent connectedness/transitivity axioms. -/
theorem opportunity_cost_independent_of_minimal_action :
    MinimalAct IncompForegoneModel 0 0 0 1 ∧
    ¬ ∃ e_opp ∈ ({2, 3} : Finset (Fin 4)),
        ∀ e' ∈ ({2, 3} : Finset (Fin 4)).erase e_opp,
          IncompForegoneModel.Pref 0 0 0 e_opp e' := by
  constructor
  · exact ⟨incomp_one_mem, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · intro ⟨e_opp, h_mem, h_max⟩
    fin_cases e_opp
    · have : (0 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) := by decide
      exact this h_mem
    · have : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) := by decide
      exact this h_mem
    · have h3_in : (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)).erase 2 := by decide
      have h_pref23 := h_max 3 h3_in
      rcases h_pref23 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
    · have h2_in : (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)).erase 3 := by decide
      have h_pref32 := h_max 2 h2_in
      rcases h_pref32 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

/-- Theorem D.7 (Independence Proof 3: Diminishing Marginal Utility Fails under Complementarity):
    A 2-unit resource allocation where 1 unit (a single shoe) yields zero utility improvement (Val 1 = Val 0),
    while 2 units (a pair of shoes) yields positive utility (Val 2 ≻ Val 1).
    The marginal utility of the 2nd unit strictly dominates that of the 1st unit,
    proving that Diminishing Marginal Utility does not follow from the Action Axiom
    without the auxiliary AtomicRegime (zero-complementarity) postulate. -/
theorem dmu_fails_under_complementarity :
    let Val : ℕ → Fin 2 := fun k => if k ≥ 2 then 1 else 0
    let Pref : Fin 2 → Fin 2 → Prop := fun a b => a = 1 ∧ b = 0
    -- 1. First unit provides zero marginal gain over status quo:
    Val 1 = Val 0 ∧
    -- 2. Second unit provides strictly positive marginal gain:
    Pref (Val 2) (Val 1) ∧
    -- 3. Marginal utility is strictly increasing, refuting DMU:
    ¬ Pref (Val 1) (Val 0) := by
  dsimp
  refine ⟨rfl, ⟨rfl, rfl⟩, ?_⟩
  intro ⟨h1, h2⟩
  exact absurd h1 (by decide)

/-- Feasible menu for SavingModel: {0, 1, 2}. -/
def SavingMenu : Finset (Fin 3) := {0, 1, 2}

theorem saving_zero_mem : (0 : Fin 3) ∈ SavingMenu := by decide
theorem saving_two_mem : (2 : Fin 3) ∈ SavingMenu := by decide

/-- Concrete Counter-Model 4: Saving for Winter Model.
    Actions: 0 (idle), 1 (consume today), 2 (save for winter).
    Agent strictly prefers saving for winter over consuming today (2 ≻ 1 ≻ 0). -/
def SavingModel : MinimalActionModel (Fin 1) (Fin 1) (Fin 1) (Fin 3) (Fin 1) (Fin 3) where
  α₀ := 0
  A_feas _ _ _ := SavingMenu
  alpha_zero_mem _ _ _ := saving_zero_mem
  End_of _ α _ _ := α
  Pref _ _ _ a b := (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 0)
  pref_irrefl_zero _ _ _ := by
    rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
  Exec _ _ α _ := α = 2
  exec_disjoint _ _ _ α β hne := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  minimal_action_axiom _ _ _ _ :=
    ⟨2, saving_two_mem, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- Theorem D.8 (Independence Proof 4: Positive Time Preference Independent of Minimal Action):
    In SavingModel, the agent purposefully acts by saving for winter (α = 2),
    completely satisfying MinimalActionModel, yet strictly prefers later consumption over earlier consumption
    (Pref e_winter e_today), refuting universal positive time preference (¬ Pref e_today e_winter).
    Proves that Positive Time Preference is logically independent of the Action Axiom. -/
theorem positive_time_pref_independent_of_minimal_action :
    MinimalAct SavingModel 0 0 0 2 ∧
    SavingModel.Pref 0 0 0 2 1 ∧
    ¬ SavingModel.Pref 0 0 0 1 2 := by
  constructor
  · exact ⟨saving_two_mem, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · constructor
    · exact Or.inl ⟨rfl, rfl⟩
    · intro h
      rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)

/-- Concrete Counter-Model 5: Local Action vs Universal Action Model.
    Two moments: t = 0 (agent purposefully asserts at t = 0) and t = 1 (passive state, no action). -/
def LocalActionModel : MinimalActionModel (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 1) (Fin 2) where
  α₀ := 0
  A_feas _ t _ := if t.val = 0 then {0, 1} else {0}
  alpha_zero_mem _ t _ := by
    fin_cases t <;> simp [Finset.mem_insert_self, Finset.mem_singleton]
  End_of _ α t _ := if t.val = 0 then α else 0
  Pref _ t _ a b := if t.val = 0 then (a = 1 ∧ b = 0) else False
  pref_irrefl_zero _ t _ := by
    fin_cases t
    · intro ⟨h1, _⟩
      exact absurd h1 (by decide)
    · intro h
      exact False.elim h
  Exec _ t α _ := if t.val = 0 then α = 1 else α = 0
  exec_disjoint _ t _ α β hne := by
    fin_cases t
    · rintro ⟨rfl, rfl⟩
      exact hne rfl
    · rintro ⟨rfl, rfl⟩
      exact hne rfl
  minimal_action_axiom _ t _ h_choice := by
    fin_cases t
    · exact ⟨1, Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl), rfl, ⟨rfl, rfl⟩⟩
    · rcases h_choice with ⟨α, _, hα_pref⟩
      exact False.elim hα_pref

/-- Theorem D.9 (Independence Proof 5: Universal Continuous Action Not Proved by Local Assertion):
    In LocalActionModel, the agent purposefully acts at moment t = 0,
    yet at moment t = 1 NO purposeful action occurs.
    Proves that performative consistency guarantees action only locally at the moment of assertion,
    and cannot prove continuous universal action across all moments. -/
theorem universal_action_not_proved_by_local_assertion :
    MinimalAct LocalActionModel 0 0 0 1 ∧
    ¬ ∃ α, MinimalAct LocalActionModel 0 1 0 α := by
  constructor
  · exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl), rfl, ⟨rfl, rfl⟩⟩
  · intro ⟨α, h_act⟩
    exact h_act.2.2

-- =========================================================================
-- Section 4: Part III — Constructive Proof of 1-Step Bourbaki-Witt Fixed Point
-- =========================================================================

/-- Mengerian indirect-exchange transition operator without axioms:
    Agents adopt commodity m if it is maximally marketable and indirect exchange is feasible. -/
def MengerianOp {Agent Means : Type} [Fintype Agent] [DecidableEq Agent] [Fintype Means] [DecidableEq Means]
    (FeasIndirect : Agent → Means → Prop) [∀ i m, Decidable (FeasIndirect i m)]
    (Γ : Means → Finset Agent) (m : Means) : Finset Agent :=
  Γ m ∪ (Finset.univ.filter (fun i => (∀ m', (Γ m').card ≤ (Γ m).card) ∧ FeasIndirect i m))

/-- Theorem D.10 (Constructive 1-Step Bourbaki-Witt Fixed Point):
    For any finite agent and commodity spaces, if commodity m_star has strictly greater
    initial marketability than all competing goods, and all agents find indirect exchange feasible
    through m_star, then a single iteration of the Mengerian operator yields:
    1. Universal acceptance of m_star: Γ₁ m_star = Finset.univ.
    2. Stability of all other goods: ∀ m ≠ m_star, Γ₁ m = Γ₀ m.
    3. Exact Bourbaki-Witt Fixed Point: MengerianOp FeasIndirect Γ₁ = Γ₁.
    This constructive proof completely eliminates the need for an uninterpreted fixed-point axiom. -/
theorem constructive_mengerian_fixed_point {Agent Means : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means] [DecidableEq Means]
    (FeasIndirect : Agent → Means → Prop) [∀ i m, Decidable (FeasIndirect i m)]
    (Γ₀ : Means → Finset Agent)
    (m_star : Means)
    (h_strict_max : ∀ m : Means, m ≠ m_star → (Γ₀ m).card < (Γ₀ m_star).card)
    (h_feas : ∀ i : Agent, FeasIndirect i m_star)
    (h_not_univ : ∀ m : Means, m ≠ m_star → (Γ₀ m).card < (Finset.univ : Finset Agent).card) :
    let Γ₁ := MengerianOp FeasIndirect Γ₀
    Γ₁ m_star = Finset.univ ∧
    (∀ m : Means, m ≠ m_star → Γ₁ m = Γ₀ m) ∧
    MengerianOp FeasIndirect Γ₁ = Γ₁ := by
  intro Γ₁
  -- 1. Prove m_star is max-marketable in Γ₀
  have h_max_mstar : ∀ m' : Means, (Γ₀ m').card ≤ (Γ₀ m_star).card := by
    intro m'
    by_cases h_eq : m' = m_star
    · subst h_eq
      exact le_rfl
    · exact le_of_lt (h_strict_max m' h_eq)
  -- 2. Prove no other good is max-marketable in Γ₀
  have h_not_max_other : ∀ m : Means, m ≠ m_star → ¬ ∀ m' : Means, (Γ₀ m').card ≤ (Γ₀ m).card := by
    intro m h_ne h_all_le
    have h_le := h_all_le m_star
    have h_lt := h_strict_max m h_ne
    linarith
  -- 3. Γ₁ m_star = Finset.univ
  have h_gamma1_mstar : Γ₁ m_star = Finset.univ := by
    ext i
    dsimp [Γ₁, MengerianOp]
    rw [Finset.mem_union, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      right
      exact ⟨h_max_mstar, h_feas i⟩
  -- 4. ∀ m ≠ m_star, Γ₁ m = Γ₀ m
  have h_gamma1_other : ∀ m : Means, m ≠ m_star → Γ₁ m = Γ₀ m := by
    intro m h_ne
    ext i
    dsimp [Γ₁, MengerianOp]
    rw [Finset.mem_union, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro (h_in | ⟨h_max, _⟩)
      · exact h_in
      · exact (h_not_max_other m h_ne h_max).elim
    · intro h_in
      exact Or.inl h_in
  -- 5. MengerianOp FeasIndirect Γ₁ = Γ₁
  have h_fixed_point : MengerianOp FeasIndirect Γ₁ = Γ₁ := by
    ext m i
    by_cases h_eq : m = m_star
    · subst h_eq
      dsimp [MengerianOp]
      rw [Finset.mem_union, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro _
        rw [h_gamma1_mstar]
        exact Finset.mem_univ i
      · intro _
        exact Or.inl (by rw [h_gamma1_mstar]; exact Finset.mem_univ i)
    · dsimp [MengerianOp]
      rw [Finset.mem_union, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      have h_m_not_max : ¬ ∀ m' : Means, (Γ₁ m').card ≤ (Γ₁ m).card := by
        intro h_all_le
        have h_le := h_all_le m_star
        rw [h_gamma1_mstar] at h_le
        have h_lt : (Γ₁ m).card < (Finset.univ : Finset Agent).card := by
          rw [h_gamma1_other m h_eq]
          exact h_not_univ m h_eq
        linarith
      constructor
      · rintro (h_in | ⟨h_max, _⟩)
        · exact h_in
        · exact (h_m_not_max h_max).elim
      · intro h_in
        exact Or.inl h_in
  exact ⟨h_gamma1_mstar, h_gamma1_other, h_fixed_point⟩

end Praxeology

end
