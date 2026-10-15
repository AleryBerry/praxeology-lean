module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-!
# Praxeology.Frame

Formalization of the ontological primitives and frame conditions for praxeology
and catallactics, following `spec/01_ontology_and_frames.md`.

## Contents
1. Multi-Sorted Signature: `Agent`, `Moment`, `Action`, `Means`, `Ends`.
2. Kripke-Tree Temporal Frame: strict precedence, backward linearity, forward branching, discrete successors.
3. History Bundles and Agency Partitions: STIT choice partitions and independence of agency.
4. Model-Theoretic Semantics: `Exec`, dynamic counterfactual box modality `DynamicBox`, and deliberative STIT `dstit`.
5. Bounded Doxastic State: epistemic information states, minimal plausibility, and DEL updates.
-/

@[expose] public section

namespace Praxeology

-- =========================================================================
-- 1. Multi-Sorted Signature (Σ_prx)
-- =========================================================================

/-- Agent sort: finite, non-empty set of discrete acting entities. -/
axiom Agent : Type
axiom instNonemptyAgent : Nonempty Agent
axiom instFintypeAgent : Fintype Agent
axiom instDecidableEqAgent : DecidableEq Agent
attribute [instance] instNonemptyAgent instFintypeAgent instDecidableEqAgent

/-- Moment sort: discrete points in time equipped with a strict order (<). -/
axiom Moment : Type
axiom instDecidableEqMoment : DecidableEq Moment
attribute [instance] instDecidableEqMoment

/-- Action sort: finite set of elementary intentional choices. -/
axiom Action : Type
axiom instNonemptyAction : Nonempty Action
axiom instFintypeAction : Fintype Action
axiom instDecidableEqAction : DecidableEq Action
attribute [instance] instNonemptyAction instFintypeAction instDecidableEqAction

/-- Distinguished passive/inertial baseline action α₀. -/
axiom alpha_zero : Action
notation "α₀" => alpha_zero

/-- Means sort: discrete physical goods/resources measured in units of ℕ₀. -/
axiom Means : Type
axiom instDecidableEqMeans : DecidableEq Means
attribute [instance] instDecidableEqMeans

/-- Ends sort: discrete teleological goals/states of affairs. -/
axiom Ends : Type
axiom instDecidableEqEnds : DecidableEq Ends
attribute [instance] instDecidableEqEnds

-- =========================================================================
-- 2. Kripke-Tree Temporal Frame (CTL* Branching Time)
-- =========================================================================

/-- Temporal precedence relation (<) on Moment. -/
axiom Precedence : Moment → Moment → Prop

instance : LT Moment where
  lt := Precedence

/-- Precedence is irreflexive. -/
axiom moment_lt_irrefl (t : Moment) : ¬(t < t)

/-- Precedence is transitive. -/
axiom moment_lt_trans {t1 t2 t3 : Moment} : t1 < t2 → t2 < t3 → t1 < t3

/-- Precedence is asymmetric (derived from irreflexivity and transitivity). -/
theorem moment_lt_asymm {t1 t2 : Moment} (h1 : t1 < t2) (h2 : t2 < t1) : False :=
  moment_lt_irrefl t1 (moment_lt_trans h1 h2)

/-- Backward Linearity (Historical Determinism / Fixed Past):
    The past of any moment is strictly linear. -/
axiom backward_linearity (t t1 t2 : Moment) :
  t1 < t → t2 < t → (t1 < t2 ∨ t1 = t2 ∨ t2 < t1)

/-- Forward Branching (Open Future):
    Every moment has at least two distinct future branches. -/
axiom forward_branching (t : Moment) :
  ∃ t1 t2 : Moment, t < t1 ∧ t < t2 ∧ t1 ≠ t2

-- =========================================================================
-- 3. History and History Bundles
-- =========================================================================

/-- A set of moments is a linear chain if all pairs of elements are comparable under (<). -/
def IsLinearChain (s : Set Moment) : Prop :=
  ∀ ⦃t1 t2⦄, t1 ∈ s → t2 ∈ s → (t1 < t2 ∨ t1 = t2 ∨ t2 < t1)

/-- A history is a maximal linear chain in (Moment, <). -/
def IsMaximalLinearChain (s : Set Moment) : Prop :=
  IsLinearChain s ∧ ∀ s', IsLinearChain s' → s ⊆ s' → s = s'

/-- History sort: maximal linear chain of moments. -/
structure History where
  val : Set Moment
  property : IsMaximalLinearChain val

instance : Membership Moment History where
  mem h t := t ∈ h.val

/-- Extensionality for histories: two histories with the same moments are equal. -/
@[ext]
theorem History.ext (h1 h2 : History) (h : h1.val = h2.val) : h1 = h2 := by
  cases h1; cases h2; cases h; rfl

/-- Every moment belongs to at least one maximal history. -/
axiom moment_in_history (t : Moment) : ∃ h : History, t ∈ h

/-- The history bundle passing through moment t: H(t) := { h : History | t ∈ h }. -/
def HistoryBundle (t : Moment) : Type :=
  { h : History // t ∈ h }

-- =========================================================================
-- 4. Agency and Choice Partitions (STIT / PDL)
-- =========================================================================

/-- Feasible menu of actions for agent i at ⟨t, h⟩. -/
axiom A_feas (i : Agent) (t : Moment) (h : History) : Finset Action

/-- Feasible menu is historically settled at t: it is invariant across all histories in H(t). -/
axiom A_feas_bundle_invariant (i : Agent) (t : Moment) (h1 h2 : History)
    (h1_t : t ∈ h1) (h2_t : t ∈ h2) :
    A_feas i t h1 = A_feas i t h2

/-- The passive/inertial baseline action α₀ is always feasible. -/
axiom alpha_zero_feasible (i : Agent) (t : Moment) (h : History) :
  α₀ ∈ A_feas i t h

/-- Feasible menu is always non-empty. -/
theorem A_feas_nonempty (i : Agent) (t : Moment) (h : History) :
    (A_feas i t h).Nonempty :=
  ⟨α₀, alpha_zero_feasible i t h⟩

/-- Choice partition cell π_i(t, α) for agent i and action α at moment t. -/
axiom ChoicePartition (i : Agent) (t : Moment) (α : Action) : Set History

/-- Every history in the choice partition cell passes through moment t: π_i(t, α) ⊆ H(t). -/
axiom choice_partition_subset_bundle (i : Agent) (t : Moment) (α : Action) :
  ∀ h ∈ ChoicePartition i t α, t ∈ h

/-- Partition covers the history bundle H(t):
    every history in H(t) realizes some feasible action. -/
axiom choice_partition_cover (i : Agent) (t : Moment) (h : History) (ht : t ∈ h) :
  ∃ α ∈ A_feas i t h, h ∈ ChoicePartition i t α

/-- Partition cells are mutually disjoint for distinct feasible actions. -/
axiom choice_partition_disjoint (i : Agent) (t : Moment) (h : History)
    {α β : Action} (hα : α ∈ A_feas i t h) (hβ : β ∈ A_feas i t h) (hne : α ≠ β) :
    Disjoint (ChoicePartition i t α) (ChoicePartition i t β)

/-- Partition cells are non-empty for all feasible actions. -/
axiom choice_partition_nonempty (i : Agent) (t : Moment) (h : History)
    {α : Action} (hα : α ∈ A_feas i t h) :
    ∃ h' : History, h' ∈ ChoicePartition i t α

-- =========================================================================
-- 5. Model-Theoretic Truth Conditions (Exec, DynamicBox, dstit)
-- =========================================================================

/-- Execution Predicate:
    M, ⟨t, h⟩ ⊨ Exec(α) iff h ∈ π_i(t, α). -/
def Exec (i : Agent) (t : Moment) (α : Action) : History → Prop :=
  fun h => h ∈ ChoicePartition i t α

/-- Dynamic Counterfactual Modality [α] ψ at moment t:
    ψ holds on all histories in the choice partition cell of α.
    Non-vacuous counterfactual jumping even if the actual history h ∉ π_i(t, α). -/
def DynamicBox (i : Agent) (t : Moment) (α : Action) (ψ : History → Prop) : Prop :=
  ∀ h' : History, h' ∈ ChoicePartition i t α → ψ h'

/-- Choice Cell Π_i(t, h):
    The unique cell of the agency partition containing history h. -/
def STITChoiceCell (i : Agent) (t : Moment) (h : History) : Set History :=
  { h' : History | ∃ α ∈ A_feas i t h, h ∈ ChoicePartition i t α ∧ h' ∈ ChoicePartition i t α }

/-- Deliberative STIT (dstit):
    M, ⟨t, h⟩ ⊨ [ :i dstit: ] ψ iff
    1. Positive condition: ψ holds on all histories in agent i's choice cell at ⟨t, h⟩.
    2. Negative (deliberative) condition: ψ fails on at least one counterfactual history in H(t). -/
def dstit (i : Agent) (t : Moment) (ψ : History → Prop) (h : History) : Prop :=
  (∀ h' ∈ STITChoiceCell i t h, ψ h') ∧
  (∃ h'' : History, t ∈ h'' ∧ ¬ ψ h'')

/-- If h is in the choice partition cell of α, then every history in STITChoiceCell i t h
    is also in ChoicePartition i t α. -/
theorem choiceCell_subset_partition (i : Agent) (t : Moment) (h : History)
    {α : Action} (hα : α ∈ A_feas i t h) (hh : h ∈ ChoicePartition i t α) :
    STITChoiceCell i t h ⊆ ChoicePartition i t α := by
  intro h' hh'
  rcases hh' with ⟨β, hβ, hh_β, hh'_β⟩
  by_cases h_eq : β = α
  · subst h_eq; exact hh'_β
  · have h_disj := choice_partition_disjoint i t h hβ hα h_eq
    exact False.elim (Set.disjoint_left.mp h_disj hh_β hh)

/-- Deliberative STIT execution implies that the actual history realizes the action. -/
theorem dstit_exec_mem (i : Agent) (t : Moment) (h : History) (α : Action)
    (_h_feas : α ∈ A_feas i t h) (ht : t ∈ h) (h_dstit : dstit i t (Exec i t α) h) :
    Exec i t α h := by
  obtain ⟨β, hβ, hhβ⟩ := choice_partition_cover i t h ht
  have h_in_cell : h ∈ STITChoiceCell i t h := ⟨β, hβ, hhβ, hhβ⟩
  have h_pos := h_dstit.1 h h_in_cell
  exact h_pos

-- =========================================================================
-- 6. Mortal Biological Horizon
-- =========================================================================

/-- Biological/operational lifespan horizon of agent i on history h. -/
axiom T_max : Agent → History → Moment

/-- The lifespan boundary moment belongs to history h. -/
axiom T_max_mem (i : Agent) (h : History) : T_max i h ∈ h

/-- Post-Horizon Singleton Menu:
    Beyond lifespan T_max(i, h), the feasible action menu collapses to the singleton
    passive/inertial baseline {α₀}, maintaining non-emptiness without active agency. -/
axiom post_horizon_singleton (i : Agent) (t : Moment) (h : History) :
  T_max i h < t → A_feas i t h = {α₀}

-- =========================================================================
-- 7. Doxastic Epistemic Logic (DEL)
-- =========================================================================

/-- Minimal plausibility worlds for agent i at moment t. -/
axiom MinPlausible (i : Agent) (t : Moment) : Set History

/-- Minimal plausibility worlds passing through moment t. -/
axiom min_plausible_subset_bundle (i : Agent) (t : Moment) :
  ∀ h ∈ MinPlausible i t, t ∈ h

/-- Minimal plausibility set is non-empty. -/
axiom min_plausible_nonempty (i : Agent) (t : Moment) :
  (MinPlausible i t).Nonempty

/-- Subjective Belief B_i ψ at moment t:
    ψ holds on all minimally plausible worlds of agent i at moment t. -/
def Belief (i : Agent) (t : Moment) (ψ : History → Prop) : Prop :=
  ∀ h' ∈ MinPlausible i t, ψ h'

/-- Dynamic Epistemic Event Update:
    Restricts minimal plausibility worlds to those satisfying event ε. -/
def DELUpdate (i : Agent) (t : Moment) (ε : History → Prop) : Set History :=
  { h' ∈ MinPlausible i t | ε h' }

/-- Belief after dynamic epistemic event update [!ε] ψ. -/
def BeliefAfterUpdate (i : Agent) (t : Moment) (ε : History → Prop) (ψ : History → Prop) : Prop :=
  ∀ h' ∈ DELUpdate i t ε, ψ h'

-- =========================================================================
-- Section 8: Causal State-Transition Frame (Laws in Re & Path-Dependence)
-- =========================================================================

/-- Causal state-transition frame formalizing physical laws in re and
    intertemporal capital accumulation/depletion. -/
structure CausalTransitionFrame (Agent Moment History Action Means : Type)
    [DecidableEq Action] where
  «α₀» : Action
  prec : Moment → Moment → Prop
  A_feas : Agent → Moment → History → Finset Action
  alpha_zero_mem : ∀ i t h, «α₀» ∈ A_feas i t h
  Exec : Agent → Moment → Action → History → Prop
  omega : Agent → Moment → History → Means → ℕ
  use_means : Action → Means → ℕ
  yield_means : Action → Means → ℕ
  phys_feas : ∀ i t h α, α ∈ A_feas i t h → ∀ m, use_means α m ≤ omega i t h m
  law_in_re_transition : ∀ i t t' h α m,
    Exec i t α h → prec t t' →
    omega i t' h m + use_means α m = omega i t h m + yield_means α m

/-- Actions requiring more physical means than available in endowment are infeasible. -/
theorem infeasible_of_insufficient_endowment
    {Agent Moment History Action Means : Type} [DecidableEq Action]
    (F : CausalTransitionFrame Agent Moment History Action Means)
    (i : Agent) (t : Moment) (h : History) (β : Action) (m : Means)
    (h_insufficient : F.omega i t h m < F.use_means β m) :
    β ∉ F.A_feas i t h := by
  intro h_mem
  have h_le := F.phys_feas i t h β h_mem m
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_insufficient h_le)

/-- Hülsmann's Path-Dependent Counterfactual Availability Theorem:
    Upstream choice to build capital vs. consume inertial state causally determines
    downstream feasibility of capital-using production methods across branching histories. -/
theorem hulsmann_path_dependent_availability
    {Agent Moment History Action Means : Type} [DecidableEq Action]
    (F : CausalTransitionFrame Agent Moment History Action Means)
    (i : Agent) (t t1' t2' : Moment) (h1 h2 : History)
    (α_build α_consume β_downstream : Action) (m_cap : Means)
    (h_prec1 : F.prec t t1') (h_prec2 : F.prec t t2')
    (h_init1 : F.omega i t h1 m_cap = 0)
    (h_init2 : F.omega i t h2 m_cap = 0)
    (h_exec1 : F.Exec i t α_build h1)
    (h_exec2 : F.Exec i t α_consume h2)
    (h_use_build : F.use_means α_build m_cap = 0)
    (h_yield_build : F.yield_means α_build m_cap = 1)
    (h_use_cons : F.use_means α_consume m_cap = 0)
    (h_yield_cons : F.yield_means α_consume m_cap = 0)
    (h_req_down : F.use_means β_downstream m_cap = 1) :
    F.omega i t1' h1 m_cap = 1 ∧
    F.omega i t2' h2 m_cap = 0 ∧
    β_downstream ∉ F.A_feas i t2' h2 := by
  have h_tr1 := F.law_in_re_transition i t t1' h1 α_build m_cap h_exec1 h_prec1
  rw [h_use_build, h_init1, h_yield_build, Nat.add_zero, Nat.zero_add] at h_tr1
  have h_tr2 := F.law_in_re_transition i t t2' h2 α_consume m_cap h_exec2 h_prec2
  rw [h_use_cons, h_init2, h_yield_cons, Nat.add_zero, Nat.zero_add] at h_tr2
  refine ⟨h_tr1, h_tr2, ?_⟩
  apply infeasible_of_insufficient_endowment F i t2' h2 β_downstream m_cap
  rw [h_tr2, h_req_down]
  exact Nat.zero_lt_one

end Praxeology

end
