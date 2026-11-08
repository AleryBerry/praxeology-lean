/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame.Core


/-!
# Praxeological Frame: Foundational Ontological Structures

Foundational ontology of praxeology: time, causality, agents, ends, means, and action frames.
-/

open scoped BigOperators

@[expose] public section

namespace Praxeology

-- Section 9: Finite ActionFrame Model


structure TreeAndAcceptanceWitness where
  MomentM : Type
  AgentM  : Type
  MeansM  : Type
  [instFintypeAgent : Fintype AgentM]
  prec : MomentM → MomentM → Prop
  prec_irrefl : ∀ m, ¬ prec m m
  prec_trans : ∀ a b c, prec a b → prec b c → prec a c
  prec_backward_linear : ∀ t1 t2 t3, prec t1 t3 → prec t2 t3 → prec t1 t2 ∨ t1 = t2 ∨ prec t2 t1
  root : MomentM
  branch1 : MomentM
  branch2 : MomentM
  h_branch1 : prec root branch1
  h_branch2 : prec root branch2
  h_incomp1 : ¬ prec branch1 branch2
  h_incomp2 : ¬ prec branch2 branch1
  h_distinct_branches : branch1 ≠ branch2
  gamma0 : MeansM → Finset AgentM
  money_good : MeansM
  h_max_marketable : ∀ m : MeansM, m ≠ money_good → (gamma0 m).card < (gamma0 money_good).card
  h_money_universal : gamma0 money_good = Finset.univ

def model_gamma0 : Fin 3 → Finset (Fin 2)
  | 0 => Finset.univ
  | 1 => {0}
  | 2 => {1}

def temporal_prec (a b : Fin 3) : Prop :=
  a = 0 ∧ (b = 1 ∨ b = 2)

instance : DecidableRel temporal_prec := by
  intro a b
  dsimp [temporal_prec]
  infer_instance

def BranchingMarketabilityModel : TreeAndAcceptanceWitness where
  MomentM := Fin 3
  AgentM  := Fin 2
  MeansM  := Fin 3
  prec := temporal_prec
  prec_irrefl := by
    intro m hm
    dsimp [temporal_prec] at hm
    rcases hm with ⟨hm0, hm12⟩
    subst hm0
    rcases hm12 with h1 | h2
    · have h_ne1 : (0 : Fin 3) ≠ 1 := by decide
      exact (h_ne1 h1).elim
    · have h_ne2 : (0 : Fin 3) ≠ 2 := by decide
      exact (h_ne2 h2).elim
  prec_trans := by
    intro a b c hab hbc
    dsimp [temporal_prec] at hab hbc
    have hb1 : b = 0 := hbc.1
    have hb2 : b = 1 ∨ b = 2 := hab.2
    subst hb1
    rcases hb2 with h1 | h2
    · have h_ne1 : (0 : Fin 3) ≠ 1 := by decide
      exact (h_ne1 h1).elim
    · have h_ne2 : (0 : Fin 3) ≠ 2 := by decide
      exact (h_ne2 h2).elim
  prec_backward_linear := by
    intro t1 t2 t3 h1 h2
    dsimp [temporal_prec] at h1 h2
    have ht1 : t1 = 0 := h1.1
    have ht2 : t2 = 0 := h2.1
    right; left
    rw [ht1, ht2]
  root := 0
  branch1 := 1
  branch2 := 2
  h_branch1 := by dsimp [temporal_prec]; decide
  h_branch2 := by dsimp [temporal_prec]; decide
  h_incomp1 := by dsimp [temporal_prec]; decide
  h_incomp2 := by dsimp [temporal_prec]; decide
  h_distinct_branches := by decide
  gamma0 := model_gamma0
  money_good := 0
  h_max_marketable := by
    intro m hm
    fin_cases m
    · exact (hm rfl).elim
    · decide
    · decide
  h_money_universal := by
    rfl


theorem branching_marketability_model_consistent : Nonempty TreeAndAcceptanceWitness :=
  ⟨BranchingMarketabilityModel⟩

/-- Three distinct successors represent the idle, consume, and defer histories. -/
def finite_action_prec (a b : Fin 4) : Prop := a = 0 ∧ b ≠ 0

instance : DecidableRel finite_action_prec := by
  intro a b
  dsimp [finite_action_prec]
  infer_instance

/-- Root 0 and one action-specific leaf on each of the three histories. -/
def branch_incidence (t : Fin 4) (h : Fin 3) : Prop :=
  t = 0 ∨ t.val = h.val + 1

instance : DecidableRel branch_incidence := by
  intro t h
  dsimp [branch_incidence]
  infer_instance

/-- Action labels used by the finite model. -/
inductive ModelAction where
  | idle : ModelAction
  | consume : ModelAction
  | defer : ModelAction
  | offer : Fin 2 → Fin 2 → ℕ → Fin 3 → ℕ → Fin 3 → ModelAction
  | accept : Fin 2 → Fin 2 → ℕ → Fin 3 → ℕ → Fin 3 → ModelAction
  deriving DecidableEq, Inhabited

/-- End labels used by the finite model. -/
inductive ModelEnd where
  | baseline : ModelEnd
  | bundle : (Fin 3 → ℕ) → ModelEnd
  | quantity : Fin 3 → ℕ → ModelEnd
  | timed : ModelEnd → Fin 4 → ModelEnd
  deriving DecidableEq, Inhabited

/-- Rank assigned to each end. -/
def end_rank : ModelEnd → ℕ
  | ModelEnd.baseline => 0
  | ModelEnd.bundle b => 10 * (b 0 + b 1 + b 2)
  | ModelEnd.quantity m q => 100 * q + m.val
  | ModelEnd.timed e τ => end_rank e + (if τ = 0 then 2 else 0)

/-- Physical requirement schedule for `FiniteBranchingModel`. -/
def finite_model_requirement : ModelEnd → Fin 3 → ℕ
  | ModelEnd.baseline => fun _ => 0
  | ModelEnd.bundle b => b
  | ModelEnd.quantity m q => fun m' => if m' = m then q else 0
  | ModelEnd.timed e _ => finite_model_requirement e

theorem teleological_bundle_dominates_sum_lt (b1 b2 : Fin 3 → ℕ)
    (h_dom : TeleologicalBundleDominates finite_model_requirement b1 b2) :
    b2 0 + b2 1 + b2 2 < b1 0 + b1 1 + b1 2 := by
  have h_le : ∀ m, b2 m ≤ b1 m := by
    have h_att2 : JointlyAttains finite_model_requirement b2 {ModelEnd.bundle b2} := by
      intro m
      simp [finite_model_requirement]
    have h_att1 := h_dom.1 {ModelEnd.bundle b2} h_att2
    intro m
    have hm : b2 m ≤ b1 m := by
      have h := h_att1 m
      simpa [finite_model_requirement] using h
    exact hm
  have h_ne : b1 ≠ b2 := by
    rintro rfl
    exact teleological_bundle_dominates_irrefl finite_model_requirement b1 h_dom
  have h_lt : ∃ m : Fin 3, b2 m < b1 m := by
    by_contra h_not
    have h_eq : b1 = b2 := by
      ext m
      have h1 := h_le m
      have h2 : ¬ (b2 m < b1 m) := fun hlt => h_not ⟨m, hlt⟩
      omega
    exact h_ne h_eq
  rcases h_lt with ⟨m, hm⟩
  fin_cases m
  · have h0 : b2 0 < b1 0 := hm
    have h1 := h_le 1
    have h2 := h_le 2
    omega
  · have h1 : b2 1 < b1 1 := hm
    have h0 := h_le 0
    have h2 := h_le 2
    omega
  · have h2 : b2 2 < b1 2 := hm
    have h0 := h_le 0
    have h1 := h_le 1
    omega

theorem teleological_bundle_dominates_end_rank_lt (b1 b2 : Fin 3 → ℕ)
    (h_dom : TeleologicalBundleDominates finite_model_requirement b1 b2) :
    end_rank (ModelEnd.bundle b2) < end_rank (ModelEnd.bundle b1) := by
  dsimp [end_rank]
  have h_sum := teleological_bundle_dominates_sum_lt b1 b2 h_dom
  omega

theorem physical_bundle_dominates_sum_lt (b1 b2 : Fin 3 → ℕ)
    (h_dom : PhysicalBundleDominates b1 b2) :
    b2 0 + b2 1 + b2 2 < b1 0 + b1 1 + b1 2 := by
  rcases h_dom with ⟨hle, ⟨m, hlt⟩⟩
  revert hlt
  fin_cases m
  · intro hlt
    change b2 0 < b1 0 at hlt
    have h1 := hle 1
    have h2 := hle 2
    omega
  · intro hlt
    change b2 1 < b1 1 at hlt
    have h0 := hle 0
    have h2 := hle 2
    omega
  · intro hlt
    change b2 2 < b1 2 at hlt
    have h0 := hle 0
    have h1 := hle 1
    omega

theorem physical_bundle_dominates_end_rank_lt (b1 b2 : Fin 3 → ℕ)
    (h_dom : PhysicalBundleDominates b1 b2) :
    end_rank (ModelEnd.bundle b2) < end_rank (ModelEnd.bundle b1) := by
  dsimp [end_rank]
  have h_sum := physical_bundle_dominates_sum_lt b1 b2 h_dom
  omega

/-- Each finite-model history is exactly the root and its own action-specific leaf. -/
theorem finite_model_histories_maximal_linear (h : Fin 3) :
    IsMaximalLinearChain finite_action_prec { t : Fin 4 | branch_incidence t h } := by
  constructor
  · intro t1 t2 ht1 ht2
    fin_cases h <;> fin_cases t1 <;> fin_cases t2 <;>
      simp_all [branch_incidence, finite_action_prec]
  · intro s' hs' hsub x hx
    by_cases hxroot : x = 0
    · simp [branch_incidence, hxroot]
    have hleaf : (Fin.succ h : Fin 4) ∈ s' := hsub (by simp [branch_incidence])
    rcases hs' hx hleaf with hlt | heq | hgt
    · exact (hxroot hlt.1).elim
    · right
      rw [heq]
      rfl
    · exact (Fin.succ_ne_zero h hgt.1).elim

/-- Action-conditioned history selection operator for `FiniteBranchingModel`. -/
def finite_model_sigma (i : Fin 2) (t : Fin 4) (α : ModelAction) (h' : Fin 3) : Fin 3 :=
  if i = 0 ∧ t = 0 then
    match α with
    | ModelAction.idle => 0
    | ModelAction.consume => 1
    | ModelAction.defer => 2
    | _ => h'
  else h'


def finite_model_maturation (i : Fin 2) (α : ModelAction) (t : Fin 4) (h : Fin 3) : Fin 4 :=
  if i = 0 ∧ t = 0 then
    match α with
    | ModelAction.idle => 0
    | _ => Fin.succ h
  else t

/-- The finite model satisfies the `ActionFrame` fields. -/
@[reducible] instance FiniteBranchingModel : ActionFrame where
  Agent := Fin 2
  Moment := Fin 4
  History := Fin 3
  Action := ModelAction
  Means := Fin 3
  Ends := ModelEnd
  alpha_zero := ModelAction.idle
  Precedence := finite_action_prec
  moment_lt_irrefl := by
    intro t h
    exact h.2 h.1
  moment_lt_trans := by
    intro _ b _ hab hbc
    exact (hab.2 hbc.1).elim
  backward_linearity := by
    intro _ _ _ h1 h2
    exact Or.inr (Or.inl (h1.1.trans h2.1.symm))
  mem_hist := branch_incidence
  moment_in_history := by
    intro t
    fin_cases t
    · exact ⟨0, by dsimp [branch_incidence]; decide⟩
    · exact ⟨0, by dsimp [branch_incidence]; decide⟩
    · exact ⟨1, by dsimp [branch_incidence]; decide⟩
    · exact ⟨2, by dsimp [branch_incidence]; decide⟩
  histories_maximal_linear := finite_model_histories_maximal_linear
  histories_extensional := by
    intro h1 h2 hsame
    apply Fin.ext
    have hleaf : branch_incidence (Fin.succ h1) h2 :=
      (hsame (Fin.succ h1)).mp (by simp [branch_incidence])
    simp [branch_incidence] at hleaf
    omega
  divergent_futures_witness := by
    intro t h1 h2 ht1 ht2 hne
    fin_cases t
    · refine ⟨Fin.succ h1, Fin.succ h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [branch_incidence]
      · simp [branch_incidence]
      · simp [finite_action_prec]
      · simp [finite_action_prec]
      · simp [finite_action_prec]
      · intro heq
        apply hne
        exact Fin.ext (by simpa using congrArg Fin.val heq)
      · simp [finite_action_prec]
    · simp [branch_incidence] at ht1 ht2
      have heq : h1 = h2 := Fin.ext (by omega)
      exact (hne heq).elim
    · simp [branch_incidence] at ht1 ht2
      have heq : h1 = h2 := Fin.ext (by omega)
      exact (hne heq).elim
    · simp [branch_incidence] at ht1 ht2
      have heq : h1 = h2 := Fin.ext (by omega)
      exact (hne heq).elim
  A_cont := fun i t _ => if i = 0 ∧ t = 0 then
    {ModelAction.idle, ModelAction.consume, ModelAction.defer} else {ModelAction.idle}
  A_cont_bundle_invariant := by
    intro _ _ _ _ _ _
    rfl
  alpha_zero_cont := by
    intro i t h
    fin_cases i <;> fin_cases t <;> decide
  omega := fun _ _ _ _ => 2
  omega_bundle_invariant := by
    intro _ _ _ _ _ _ _
    rfl
  use_means := fun α m =>
    match α with
    | ModelAction.offer _ _ qA mA _ _ => if m = mA then qA else 0
    | ModelAction.accept _ _ _ _ qB mB => if m = mB then qB else 0
    | _ => 0
  yield_means := fun α m =>
    match α with
    | ModelAction.offer _ _ _ _ qB mB => if m = mB then qB else 0
    | ModelAction.accept _ _ qA mA _ _ => if m = mA then qA else 0
    | _ => 0
  use_means_alpha_zero := by
    intro m; rfl
  yield_means_alpha_zero := by
    intro m; rfl
  A_feas := fun i t _ => if i = 0 ∧ t = 0 then
    {ModelAction.idle, ModelAction.consume, ModelAction.defer} else {ModelAction.idle}
  A_feas_coupling := by
    intro i t _ α
    constructor
    · intro hα
      refine ⟨hα, fun _ => ?_⟩
      fin_cases i <;> fin_cases t <;> {
        dsimp at hα
        simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with rfl | rfl | rfl <;> exact Nat.zero_le 2
      }
    · intro h
      exact h.1
  enacted := fun i t h =>
    if i = 0 ∧ t = 0 then
      if h = 0 then ModelAction.idle
      else if h = 1 then ModelAction.consume
      else ModelAction.defer
    else
      ModelAction.idle
  enacted_in_A_feas := by
    intro i t h _ht
    fin_cases i <;> fin_cases t <;> fin_cases h <;> decide
  no_choice_between_undivided := by
    intro i t u h1 h2 _ _ htu hu1 hu2
    have hne : u ≠ 0 := htu.2
    have hv1 : u.val = h1.val + 1 := (hu1.resolve_left hne)
    have hv2 : u.val = h2.val + 1 := (hu2.resolve_left hne)
    have hh : h1 = h2 := Fin.ext (by omega)
    subst hh
    rfl
  sigma := finite_model_sigma
  sigma_realization := by
    intro i t h h' α _ht hα ht'
    fin_cases i <;> fin_cases t <;> fin_cases h' <;> {
      dsimp [finite_model_sigma, ActionFrame.A_feas] at hα ⊢
      first
      | simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with rfl | rfl | rfl
        · exact ⟨by dsimp [branch_incidence]; decide, rfl⟩
        · exact ⟨by dsimp [branch_incidence]; decide, rfl⟩
        · exact ⟨by dsimp [branch_incidence]; decide, rfl⟩
      | simp only [Finset.mem_singleton] at hα
        subst hα
        exact ⟨ht', rfl⟩
    }
  sigma_centering := by
    intro i t h' α _ht' h_enact
    subst h_enact
    fin_cases i <;> fin_cases t <;> fin_cases h' <;> rfl
  sigma_co_agency := by
    intro i j t h h' α h_ne _ht _hα _ht'
    fin_cases i <;> fin_cases j <;> try { exact (h_ne rfl).elim }
    all_goals {
      cases t; fin_cases h' <;> rfl
    }
  expected_maturation_mem_future := by
    intro i α t h ht _h_enact
    dsimp [finite_model_maturation]
    split_ifs with h_root
    · obtain ⟨rfl, rfl⟩ := h_root
      cases α with
      | idle => exact ⟨Or.inl rfl, Or.inl rfl⟩
      | consume => exact ⟨Or.inr rfl, Or.inr ⟨rfl, Fin.succ_ne_zero h⟩⟩
      | defer => exact ⟨Or.inr rfl, Or.inr ⟨rfl, Fin.succ_ne_zero h⟩⟩
      | offer _ _ _ _ _ _ => exact ⟨Or.inr rfl, Or.inr ⟨rfl, Fin.succ_ne_zero h⟩⟩
      | accept _ _ _ _ _ _ => exact ⟨Or.inr rfl, Or.inr ⟨rfl, Fin.succ_ne_zero h⟩⟩
    · exact ⟨ht, Or.inl rfl⟩
  law_in_re_transition := by
    intro i t t' h α m _h_not_tr h_enact _h_next
    fin_cases i <;> fin_cases t <;> fin_cases h <;> {
      dsimp [ActionFrame.enacted] at h_enact
      subst h_enact
      rfl
    }
  MinPlausible := fun _ t => { h : Fin 3 | branch_incidence t h }
  tau := fun _ t _ => t
  min_plausible_node_incidence := by
    intro _ _ h' hh'
    exact hh'
  tau_centering := by
    intro _ _ _ _
    rfl
  min_plausible_nonempty := by
    intro i t
    fin_cases t
    · exact ⟨0, by dsimp [branch_incidence]; decide⟩
    · exact ⟨0, by dsimp [branch_incidence]; decide⟩
    · exact ⟨1, by dsimp [branch_incidence]; decide⟩
    · exact ⟨2, by dsimp [branch_incidence]; decide⟩
  requirement := finite_model_requirement
  ValuedEnd := fun _ _ _ _ => True
  valued_end_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
  OutcomeOf := fun _ α t _ _ =>
    if t = 0 then
      match α with
      | ModelAction.idle => ModelEnd.timed (ModelEnd.quantity 0 0) 0
      | ModelAction.consume => ModelEnd.timed (ModelEnd.quantity 1 1) 0
      | _ => ModelEnd.timed (ModelEnd.quantity 1 1) 1
    else
      ModelEnd.timed (ModelEnd.quantity 0 0) t
  ExpectedMaturation := finite_model_maturation
  End_of := fun _ α t _ =>
    if t = 0 then
      match α with
      | ModelAction.idle => ModelEnd.timed (ModelEnd.quantity 0 0) 0
      | ModelAction.consume => ModelEnd.timed (ModelEnd.quantity 1 1) 0
      | _ => ModelEnd.timed (ModelEnd.quantity 1 1) 1
    else
      ModelEnd.timed (ModelEnd.quantity 0 0) t
  End_of_bundle_invariant := by
    intro _ _ _ _ _ _ _
    rfl
  Preference := fun _ _ _ e1 e2 => end_rank e2 < end_rank e1
  Preference_bundle_invariant := by
    intro _ _ _ _ _ _
    rfl
  pref_asymm := by
    intro i t h e1 e2 h12 h21
    exact Nat.lt_asymm h12 h21
  doxastic_sure_thing_bridge := by
    intro i α β t h _ _ ⟨h', _, h_pref⟩
    exact h_pref
  doxastic_plausible_support := by
    intro i α β t h _ h_pref
    have ⟨h_pl, hh_pl⟩ : ∃ h_pl, branch_incidence t h_pl := by
      fin_cases t
      · exact ⟨0, by dsimp [branch_incidence]; decide⟩
      · exact ⟨0, by dsimp [branch_incidence]; decide⟩
      · exact ⟨1, by dsimp [branch_incidence]; decide⟩
      · exact ⟨2, by dsimp [branch_incidence]; decide⟩
    exact ⟨h_pl, hh_pl, h_pref⟩
  BundleEnd := ModelEnd.bundle
  teleological_bundle_dominance_induces_preference := by
    intro i t h b1 b2 h_dom
    have h_global : TeleologicalBundleDominates finite_model_requirement b1 b2 :=
      (subjective_teleological_dominates_iff_teleological_of_universal
        finite_model_requirement (fun _ : ModelEnd => True) (fun _ => trivial) b1 b2).mp h_dom
    exact teleological_bundle_dominates_end_rank_lt b1 b2 h_global

instance : IntertemporalEnds FiniteBranchingModel where
  TimedEnd := ModelEnd.timed
  QuantityEnd := ModelEnd.quantity
  timed_end_inj := by intro _ _ _ _ h; exact ModelEnd.timed.inj h
  quantity_end_inj := by intro _ _ _ _ h; exact ModelEnd.quantity.inj h


/-- `FiniteBranchingModel` is an instance of `ActionFrame`. -/
theorem action_frame_consistent : Nonempty ActionFrame :=
  ⟨FiniteBranchingModel⟩

/-- A moment can be absent from a history. -/
theorem finite_model_branching_nontrivial :
    ∃ (t : Fin 4) (h : Fin 3), ¬ branch_incidence t h :=
  ⟨1, 2, by dsimp [branch_incidence]; decide⟩


-- Section 10: Bilateral Trade Model


/-- Five moments: one root and four leaves. -/
inductive BilateralMoment where
  | root : BilateralMoment
  | leaf0 : BilateralMoment
  | leaf1 : BilateralMoment
  | leaf2 : BilateralMoment
  | leaf3 : BilateralMoment
  deriving DecidableEq, Inhabited

/-- The root precedes each leaf. -/
def bilateral_prec : BilateralMoment → BilateralMoment → Prop
  | .root, .leaf0 => True
  | .root, .leaf1 => True
  | .root, .leaf2 => True
  | .root, .leaf3 => True
  | _, _ => False

instance : DecidableRel bilateral_prec := fun t1 t2 =>
  match t1, t2 with
  | .root, .leaf0 => isTrue trivial
  | .root, .leaf1 => isTrue trivial
  | .root, .leaf2 => isTrue trivial
  | .root, .leaf3 => isTrue trivial
  | .root, .root => isFalse (by intro h; cases h)
  | .leaf0, _ => isFalse (by intro h; cases h)
  | .leaf1, _ => isFalse (by intro h; cases h)
  | .leaf2, _ => isFalse (by intro h; cases h)
  | .leaf3, _ => isFalse (by intro h; cases h)

/-- Each history contains the root and one leaf. -/
def bilateral_mem_hist : BilateralMoment → Fin 4 → Prop
  | .root, _ => True
  | .leaf0, h => h = 0
  | .leaf1, h => h = 1
  | .leaf2, h => h = 2
  | .leaf3, h => h = 3

def bilateral_leaf (h : Fin 4) : BilateralMoment :=
  match h with
  | 0 => .leaf0
  | 1 => .leaf1
  | 2 => .leaf2
  | 3 => .leaf3

instance : DecidableRel bilateral_mem_hist := fun t h =>
  match t with
  | .root => isTrue trivial
  | .leaf0 => if h0 : h = 0 then isTrue h0 else isFalse h0
  | .leaf1 => if h1 : h = 1 then isTrue h1 else isFalse h1
  | .leaf2 => if h2 : h = 2 then isTrue h2 else isFalse h2
  | .leaf3 => if h3 : h = 3 then isTrue h3 else isFalse h3

/-- Each history is a maximal linear chain. -/
theorem bilateral_histories_maximal_linear (h : Fin 4) :
    IsMaximalLinearChain bilateral_prec { t : BilateralMoment | bilateral_mem_hist t h } := by
  constructor
  · intro t1 t2 ht1 ht2
    fin_cases h <;> cases t1 <;> cases t2 <;> {
      try { revert ht1; decide }
      try { revert ht2; decide }
    }
  · intro s' hs' hsub x hx
    cases x
    · trivial
    · fin_cases h
      · rfl
      · exfalso
        have h1 : BilateralMoment.leaf1 ∈ s' := hsub (by decide)
        have hc := hs' hx h1
        rcases hc with h | h | h <;> revert h <;> decide
      · exfalso
        have h2 : BilateralMoment.leaf2 ∈ s' := hsub (by decide)
        have hc := hs' hx h2
        rcases hc with h | h | h <;> revert h <;> decide
      · exfalso
        have h3 : BilateralMoment.leaf3 ∈ s' := hsub (by decide)
        have hc := hs' hx h3
        rcases hc with h | h | h <;> revert h <;> decide
    · fin_cases h
      · exfalso
        have h0 : BilateralMoment.leaf0 ∈ s' := hsub (by decide)
        have hc := hs' hx h0
        rcases hc with h | h | h <;> revert h <;> decide
      · rfl
      · exfalso
        have h2 : BilateralMoment.leaf2 ∈ s' := hsub (by decide)
        have hc := hs' hx h2
        rcases hc with h | h | h <;> revert h <;> decide
      · exfalso
        have h3 : BilateralMoment.leaf3 ∈ s' := hsub (by decide)
        have hc := hs' hx h3
        rcases hc with h | h | h <;> revert h <;> decide
    · fin_cases h
      · exfalso
        have h0 : BilateralMoment.leaf0 ∈ s' := hsub (by decide)
        have hc := hs' hx h0
        rcases hc with h | h | h <;> revert h <;> decide
      · exfalso
        have h1 : BilateralMoment.leaf1 ∈ s' := hsub (by decide)
        have hc := hs' hx h1
        rcases hc with h | h | h <;> revert h <;> decide
      · rfl
      · exfalso
        have h3 : BilateralMoment.leaf3 ∈ s' := hsub (by decide)
        have hc := hs' hx h3
        rcases hc with h | h | h <;> revert h <;> decide
    · fin_cases h
      · exfalso
        have h0 : BilateralMoment.leaf0 ∈ s' := hsub (by decide)
        have hc := hs' hx h0
        rcases hc with h | h | h <;> revert h <;> decide
      · exfalso
        have h1 : BilateralMoment.leaf1 ∈ s' := hsub (by decide)
        have hc := hs' hx h1
        rcases hc with h | h | h <;> revert h <;> decide
      · exfalso
        have h2 : BilateralMoment.leaf2 ∈ s' := hsub (by decide)
        have hc := hs' hx h2
        rcases hc with h | h | h <;> revert h <;> decide
      · rfl

/-- Distinct histories through the root have different leaves. -/
theorem bilateral_divergent_futures_witness (t : BilateralMoment) (h1 h2 : Fin 4)
    (ht1 : bilateral_mem_hist t h1) (ht2 : bilateral_mem_hist t h2) (hne : h1 ≠ h2) :
    ∃ u v : BilateralMoment,
      bilateral_mem_hist u h1 ∧ bilateral_mem_hist v h2 ∧
      bilateral_prec t u ∧ bilateral_prec t v ∧
      ¬ bilateral_prec u v ∧ u ≠ v ∧ ¬ bilateral_prec v u := by
  cases t with
  | root =>
      refine ⟨bilateral_leaf h1, bilateral_leaf h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        fin_cases h1 <;> fin_cases h2 <;>
          simp_all [bilateral_leaf, bilateral_mem_hist, bilateral_prec]
  | leaf0 =>
      change h1 = 0 at ht1
      change h2 = 0 at ht2
      subst h1
      subst h2
      exact (hne rfl).elim
  | leaf1 =>
      change h1 = 1 at ht1
      change h2 = 1 at ht2
      subst h1
      subst h2
      exact (hne rfl).elim
  | leaf2 =>
      change h1 = 2 at ht1
      change h2 = 2 at ht2
      subst h1
      subst h2
      exact (hne rfl).elim
  | leaf3 =>
      change h1 = 3 at ht1
      change h2 = 3 at ht2
      subst h1
      subst h2
      exact (hne rfl).elim

/-- Physical endowment for the bilateral trade model. -/
def bilateral_omega (i : Fin 2) (t : BilateralMoment) (_h : Fin 4) (m : Fin 3) : ℕ :=
  match t with
  | .root =>
    if i = 0 then (if m = 0 then 2 else 0)
    else (if m = 1 then 2 else 0)
  | .leaf0 =>
    if i = 0 then (if m = 0 then 2 else 0)
    else (if m = 1 then 2 else 0)
  | .leaf1 =>
    if i = 0 then (if m = 0 then 2 else 0)
    else (if m = 1 then 2 else 0)
  | .leaf2 =>
    if i = 0 then (if m = 0 then 2 else 0)
    else (if m = 1 then 2 else 0)
  | .leaf3 =>
    if i = 0 then (if m = 0 ∨ m = 1 then 1 else 0)
    else (if m = 0 ∨ m = 1 then 1 else 0)


def bilateral_enacted (i : Fin 2) (t : BilateralMoment) (h : Fin 4) : ModelAction :=
  match t with
  | .root =>
    if i = 0 then
      if h = 1 ∨ h = 3 then ModelAction.offer 0 1 1 0 1 1
      else ModelAction.idle
    else
      if h = 2 ∨ h = 3 then ModelAction.accept 1 0 1 0 1 1
      else ModelAction.idle
  | _ => ModelAction.idle

/-- The one-step transitions from the root. -/
theorem bilateral_next_moment_cases {t t' : BilateralMoment} {h : Fin 4}
    (h_next : IsNextMoment bilateral_prec bilateral_mem_hist t t' h) :
    (t = .root ∧ t' = .leaf0 ∧ h = 0) ∨
    (t = .root ∧ t' = .leaf1 ∧ h = 1) ∨
    (t = .root ∧ t' = .leaf2 ∧ h = 2) ∨
    (t = .root ∧ t' = .leaf3 ∧ h = 3) := by
  have hprec := h_next.2.2.1
  have hmem := h_next.2.1
  cases t <;> cases t' <;> fin_cases h <;> {
    try { revert hprec; decide }
    try { revert hmem; decide }
  }

/-- End labels used by the bilateral model. -/
inductive BilateralEnd where
  | baseline : BilateralEnd
  | bundle : (Fin 3 → ℕ) → BilateralEnd
  | quantity : Fin 3 → ℕ → BilateralEnd
  | timed : BilateralEnd → BilateralMoment → BilateralEnd
  deriving DecidableEq, Inhabited

/-- Rank assigned to each bilateral end. -/
def bilateral_end_rank : BilateralEnd → ℕ
  | BilateralEnd.baseline => 0
  | BilateralEnd.bundle b => 10 * (b 0 + b 1 + b 2)
  | BilateralEnd.quantity m q => 100 * q + m.val
  | BilateralEnd.timed e τ => bilateral_end_rank e + (if τ = BilateralMoment.root then 2 else 0)

/-- Physical requirement schedule for `BilateralTradeActionFrame`. -/
def bilateral_requirement : BilateralEnd → Fin 3 → ℕ
  | BilateralEnd.baseline => fun _ => 0
  | BilateralEnd.bundle b => b
  | BilateralEnd.quantity m q => fun m' => if m' = m then q else 0
  | BilateralEnd.timed e _ => bilateral_requirement e

theorem bilateral_teleological_bundle_dominates_sum_lt (b1 b2 : Fin 3 → ℕ)
    (h_dom : TeleologicalBundleDominates bilateral_requirement b1 b2) :
    b2 0 + b2 1 + b2 2 < b1 0 + b1 1 + b1 2 := by
  have h_le : ∀ m, b2 m ≤ b1 m := by
    have h_att2 : JointlyAttains bilateral_requirement b2 {BilateralEnd.bundle b2} := by
      intro m
      simp [bilateral_requirement]
    have h_att1 := h_dom.1 {BilateralEnd.bundle b2} h_att2
    intro m
    have hm : b2 m ≤ b1 m := by
      have h := h_att1 m
      simpa [bilateral_requirement] using h
    exact hm
  have h_ne : b1 ≠ b2 := by
    rintro rfl
    exact teleological_bundle_dominates_irrefl bilateral_requirement b1 h_dom
  have h_lt : ∃ m : Fin 3, b2 m < b1 m := by
    by_contra h_not
    have h_eq : b1 = b2 := by
      ext m
      have h1 := h_le m
      have h2 : ¬ (b2 m < b1 m) := fun hlt => h_not ⟨m, hlt⟩
      omega
    exact h_ne h_eq
  rcases h_lt with ⟨m, hm⟩
  fin_cases m
  · have h0 : b2 0 < b1 0 := hm
    have h1 := h_le 1
    have h2 := h_le 2
    omega
  · have h1 : b2 1 < b1 1 := hm
    have h0 := h_le 0
    have h2 := h_le 2
    omega
  · have h2 : b2 2 < b1 2 := hm
    have h0 := h_le 0
    have h1 := h_le 1
    omega

theorem bilateral_teleological_bundle_dominates_end_rank_lt (b1 b2 : Fin 3 → ℕ)
    (h_dom : TeleologicalBundleDominates bilateral_requirement b1 b2) :
    bilateral_end_rank (BilateralEnd.bundle b2) < bilateral_end_rank (BilateralEnd.bundle b1) := by
  dsimp [bilateral_end_rank]
  have h_sum := bilateral_teleological_bundle_dominates_sum_lt b1 b2 h_dom
  omega

theorem bilateral_physical_bundle_dominates_end_rank_lt (b1 b2 : Fin 3 → ℕ)
    (h_dom : PhysicalBundleDominates b1 b2) :
    bilateral_end_rank (BilateralEnd.bundle b2) < bilateral_end_rank (BilateralEnd.bundle b1) := by
  dsimp [bilateral_end_rank]
  have h_sum := physical_bundle_dominates_sum_lt b1 b2 h_dom
  omega

/-- Selects the history where `α` is enacted at `t`. -/
def bilateral_sigma (i : Fin 2) (t : BilateralMoment) (α : ModelAction) (h' : Fin 4) : Fin 4 :=
  match t with
  | .root =>
    if i = 0 then
      if α = ModelAction.offer 0 1 1 0 1 1 then
        if h' = 2 ∨ h' = 3 then 3 else 1
      else
        if h' = 2 ∨ h' = 3 then 2 else 0
    else
      if α = ModelAction.accept 1 0 1 0 1 1 then
        if h' = 1 ∨ h' = 3 then 3 else 2
      else
        if h' = 1 ∨ h' = 3 then 1 else 0
  | _ => h'

/-- History selected for each moment. -/
def bilateral_subjective_witness (t : BilateralMoment) : Fin 4 :=
  match t with
  | .root => 3
  | .leaf0 => 0
  | .leaf1 => 1
  | .leaf2 => 2
  | .leaf3 => 3

/-- Terminal moment for each history. -/
def bilateral_terminal_moment (h : Fin 4) : BilateralMoment :=
  match h.val with
  | 0 => .leaf0
  | 1 => .leaf1
  | 2 => .leaf2
  | _ => .leaf3

/-- Root actions mature at the selected history's terminal moment. -/
def bilateral_subjective_maturation (_i : Fin 2) (_α : ModelAction)
    (t : BilateralMoment) (h : Fin 4) : BilateralMoment :=
  match t with
  | .root => bilateral_terminal_moment h
  | _ => t

/-- Subjective elementary ends use the inherited physical recipe schedule. -/
def bilateral_subjective_requirement (e : BilateralEnd) (m : Fin 3) : ℕ :=
  bilateral_requirement e m

/-- Each agent values the quantity end for the other agent's initial good. -/
def bilateral_subjective_valued_end (i : Fin 2) (_t : BilateralMoment)
    (_h : Fin 4) (e : BilateralEnd) : Prop :=
  if i = 0 then e = .quantity 1 1 else e = .quantity 0 1

/-- Bundle preference is defined by dominance over valued ends. -/
def bilateral_subjective_preference (i : Fin 2) (_t : BilateralMoment) (_h : Fin 4)
    (e1 e2 : BilateralEnd) : Prop :=
  match e1, e2 with
  | .bundle b1, .bundle b2 =>
      SubjectiveTeleologicalDominates bilateral_subjective_requirement
        (bilateral_subjective_valued_end i .root 0) b1 b2
  | _, _ => False

/-- Bundle end from the resulting endowment. -/
def bilateral_subjective_outcome (i : Fin 2) (_α : ModelAction) (_t τ : BilateralMoment)
    (h : Fin 4) : BilateralEnd :=
  .bundle (bilateral_omega i τ h)

/-- Outcome on the selected plausible history. -/
def bilateral_subjective_end (i : Fin 2) (α : ModelAction) (t : BilateralMoment)
    (_h : Fin 4) : BilateralEnd :=
  let h' := bilateral_subjective_witness t
  let hα := bilateral_sigma i t α h'
  bilateral_subjective_outcome i α t (bilateral_subjective_maturation i α t hα) hα

/-- Matched trade dominates each agent's initial bundle. -/
theorem bilateral_subjective_trade_dominance (i : Fin 2) :
    SubjectiveTeleologicalDominates bilateral_subjective_requirement
      (bilateral_subjective_valued_end i .root 3)
      (bilateral_omega i .leaf3 3) (bilateral_omega i .root 3) := by
  classical
  fin_cases i
  · apply subjective_teleological_dominates_of_unique_valued_end
      bilateral_subjective_requirement
      (bilateral_subjective_valued_end 0 .root 3)
      (.quantity 1 1)
      (bilateral_omega 0 .leaf3 3)
      (bilateral_omega 0 .root 3)
    · intro e he
      simpa [bilateral_subjective_valued_end] using he
    · simp [bilateral_subjective_valued_end]
    · intro m
      fin_cases m <;>
        simp [bilateral_subjective_requirement, bilateral_requirement, bilateral_omega]
    · intro hatt
      have hbad := hatt 1
      simp [bilateral_subjective_requirement, bilateral_requirement, bilateral_omega] at hbad
  · apply subjective_teleological_dominates_of_unique_valued_end
      bilateral_subjective_requirement
      (bilateral_subjective_valued_end 1 .root 3)
      (.quantity 0 1)
      (bilateral_omega 1 .leaf3 3)
      (bilateral_omega 1 .root 3)
    · intro e he
      simpa [bilateral_subjective_valued_end] using he
    · simp [bilateral_subjective_valued_end]
    · intro m
      fin_cases m <;>
        simp [bilateral_subjective_requirement, bilateral_requirement, bilateral_omega]
    · intro hatt
      have hbad := hatt 0
      simp [bilateral_subjective_requirement, bilateral_requirement, bilateral_omega] at hbad

/-- `BilateralTradeActionFrame` includes matched trade and unilateral offer examples. -/
@[reducible] instance (priority := 100) BilateralTradeActionFrame : ActionFrame where
  Agent := Fin 2
  Moment := BilateralMoment
  History := Fin 4
  Action := ModelAction
  Means := Fin 3
  Ends := BilateralEnd
  alpha_zero := ModelAction.idle
  Precedence := bilateral_prec
  moment_lt_irrefl := by
    intro t ht
    cases t <;> revert ht <;> decide
  moment_lt_trans := by
    intro t1 t2 t3 h12 h23
    cases t1 <;> cases t2 <;> cases t3 <;> revert h12 h23 <;> decide
  backward_linearity := by
    intro t1 t2 t3 h13 h23
    cases t1 <;> cases t2 <;> cases t3 <;> revert h13 h23 <;> decide
  mem_hist := bilateral_mem_hist
  moment_in_history := by
    intro t
    cases t
    · exact ⟨0, trivial⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  histories_maximal_linear := bilateral_histories_maximal_linear
  histories_extensional := by
    intro h1 h2 hsame
    have h0 := hsame BilateralMoment.leaf0
    have h1' := hsame BilateralMoment.leaf1
    have h2' := hsame BilateralMoment.leaf2
    have h3 := hsame BilateralMoment.leaf3
    fin_cases h1 <;> fin_cases h2 <;> simp_all [bilateral_mem_hist]
  divergent_futures_witness := by
    intro t h1 h2 ht1 ht2 hne
    exact bilateral_divergent_futures_witness t h1 h2 ht1 ht2 hne
  A_cont := fun i t _ =>
    match t with
    | .root =>
      if i = 0 then {ModelAction.idle, ModelAction.offer 0 1 1 0 1 1}
      else {ModelAction.idle, ModelAction.accept 1 0 1 0 1 1}
    | _ => {ModelAction.idle}
  A_cont_bundle_invariant := by
    intro _ t _ _ _ _
    cases t <;> rfl
  alpha_zero_cont := by
    intro i t _
    fin_cases i <;> cases t <;> decide
  omega := bilateral_omega
  omega_bundle_invariant := by
    intro _ t _ h1 h2 hh1 hh2
    cases t
    · rfl
    · dsimp [bilateral_mem_hist] at hh1 hh2; subst hh1; subst hh2; rfl
    · dsimp [bilateral_mem_hist] at hh1 hh2; subst hh1; subst hh2; rfl
    · dsimp [bilateral_mem_hist] at hh1 hh2; subst hh1; subst hh2; rfl
    · dsimp [bilateral_mem_hist] at hh1 hh2; subst hh1; subst hh2; rfl
  use_means := fun α m =>
    match α with
    | ModelAction.offer _ _ qA mA _ _ => if m = mA then qA else 0
    | ModelAction.accept _ _ _ _ qB mB => if m = mB then qB else 0
    | _ => 0
  yield_means := fun α m =>
    match α with
    | ModelAction.offer _ _ _ _ qB mB => if m = mB then qB else 0
    | ModelAction.accept _ _ qA mA _ _ => if m = mA then qA else 0
    | _ => 0
  use_means_alpha_zero := by intro _; rfl
  yield_means_alpha_zero := by intro _; rfl
  A_feas := fun i t _ =>
    match t with
    | .root =>
      if i = 0 then {ModelAction.idle, ModelAction.offer 0 1 1 0 1 1}
      else {ModelAction.idle, ModelAction.accept 1 0 1 0 1 1}
    | _ => {ModelAction.idle}
  A_feas_coupling := by
    intro i t h α
    constructor
    · intro hα
      refine ⟨hα, fun m => ?_⟩
      fin_cases i <;> cases t
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with rfl | rfl <;> fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_singleton] at hα; subst hα
        fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_singleton] at hα; subst hα
        fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_singleton] at hα; subst hα
        fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_singleton] at hα; subst hα
        fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with rfl | rfl <;> fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_singleton] at hα; subst hα
        fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_singleton] at hα; subst hα
        fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_singleton] at hα; subst hα
        fin_cases m <;> decide
      · dsimp [bilateral_omega]
        dsimp at hα; simp only [Finset.mem_singleton] at hα; subst hα
        fin_cases m <;> decide
    · intro h; exact h.1
  enacted := bilateral_enacted
  enacted_in_A_feas := by
    intro i t h _
    fin_cases i <;> cases t <;> fin_cases h <;> decide
  no_choice_between_undivided := by
    intro i t u h1 h2 _ _ htu hu1 hu2
    cases t <;> cases u <;> try { cases htu }
    all_goals fin_cases h1 <;> fin_cases h2 <;> simp_all [bilateral_mem_hist]
  sigma := bilateral_sigma
  sigma_realization := by
    intro i t h h' α _ht hα ht'
    fin_cases i <;> cases t <;> fin_cases h' <;> {
      dsimp [bilateral_sigma, ActionFrame.A_feas] at hα ⊢
      first
      | simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with rfl | rfl
        · exact ⟨trivial, rfl⟩
        · exact ⟨trivial, rfl⟩
      | simp only [Finset.mem_singleton] at hα
        subst hα
        exact ⟨ht', rfl⟩
    }
  sigma_centering := by
    intro i t h' α _ht' h_enact
    subst h_enact
    fin_cases i <;> cases t <;> fin_cases h' <;> rfl
  sigma_co_agency := by
    intro i j t h h' α h_ne _ht hα _ht'
    fin_cases i <;> fin_cases j <;> try { exact (h_ne rfl).elim }
    all_goals {
      cases t
      · dsimp [ActionFrame.A_feas] at hα
        rcases Finset.mem_insert.mp hα with rfl | hα'
        · fin_cases h' <;> rfl
        · rw [Finset.mem_singleton] at hα'
          subst hα'
          fin_cases h' <;> rfl
      · dsimp [ActionFrame.A_feas] at hα; rw [Finset.mem_singleton] at hα
        subst hα; fin_cases h' <;> rfl
      · dsimp [ActionFrame.A_feas] at hα; rw [Finset.mem_singleton] at hα
        subst hα; fin_cases h' <;> rfl
      · dsimp [ActionFrame.A_feas] at hα; rw [Finset.mem_singleton] at hα
        subst hα; fin_cases h' <;> rfl
      · dsimp [ActionFrame.A_feas] at hα; rw [Finset.mem_singleton] at hα
        subst hα; fin_cases h' <;> rfl
    }
  expected_maturation_mem_future := by
    intro i α t h ht _h_enact
    refine ⟨ht, Or.inl rfl⟩
  IsTradeAction := fun α =>
    (∃ i j qA mA qB mB, α = ModelAction.offer i j qA mA qB mB) ∨
    (∃ j i qA mA qB mB, α = ModelAction.accept j i qA mA qB mB)
  alpha_zero_not_trade := by
    intro h
    rcases h with ⟨i, j, qA, mA, qB, mB, h_eq⟩ | ⟨j, i, qA, mA, qB, mB, h_eq⟩
    · cases h_eq
    · cases h_eq
  law_in_re_transition := by
    intro i t t' h α m h_not_tr h_enact h_next
    rcases bilateral_next_moment_cases h_next with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · fin_cases i <;> {
        dsimp [bilateral_enacted] at h_enact
        subst h_enact
        fin_cases m <;> decide
      }
    · fin_cases i
      · dsimp [bilateral_enacted] at h_enact
        subst h_enact
        exfalso
        apply h_not_tr
        exact Or.inl ⟨0, 1, 1, 0, 1, 1, rfl⟩
      · dsimp [bilateral_enacted] at h_enact
        subst h_enact
        fin_cases m <;> decide
    · fin_cases i
      · dsimp [bilateral_enacted] at h_enact
        subst h_enact
        fin_cases m <;> decide
      · dsimp [bilateral_enacted] at h_enact
        subst h_enact
        exfalso
        apply h_not_tr
        exact Or.inr ⟨1, 0, 1, 0, 1, 1, rfl⟩
    · fin_cases i
      · dsimp [bilateral_enacted] at h_enact
        subst h_enact
        exfalso
        apply h_not_tr
        exact Or.inl ⟨0, 1, 1, 0, 1, 1, rfl⟩
      · dsimp [bilateral_enacted] at h_enact
        subst h_enact
        exfalso
        apply h_not_tr
        exact Or.inr ⟨1, 0, 1, 0, 1, 1, rfl⟩
  MinPlausible := fun _ t => { h : Fin 4 | bilateral_mem_hist t h }
  tau := fun _ t _ => t
  min_plausible_node_incidence := by intro _ _ h hh; exact hh
  tau_centering := by intro _ _ _ _; rfl
  min_plausible_nonempty := by
    intro _ t
    cases t
    · exact ⟨0, trivial⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  requirement := bilateral_requirement
  ValuedEnd := fun _ _ _ _ => True
  valued_end_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
  OutcomeOf := fun _ _ _ _ _ => BilateralEnd.baseline
  ExpectedMaturation := fun _ _ t _ => t
  End_of := fun _ _ _ _ => BilateralEnd.baseline
  End_of_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
  Preference := fun _ _ _ e1 e2 => bilateral_end_rank e2 < bilateral_end_rank e1
  Preference_bundle_invariant := by intro _ _ _ _ _ _; rfl
  pref_asymm := by intro _ _ _ _ _ h1 h2; exact Nat.lt_asymm h1 h2
  doxastic_sure_thing_bridge := by
    intro i α β t h _ _ ⟨h', _, h_pref⟩
    exact h_pref
  doxastic_plausible_support := by
    intro i α β t h _ h_pref
    have ⟨h_pl, hh_pl⟩ : ∃ h_pl, bilateral_mem_hist t h_pl := by
      cases t
      · exact ⟨0, trivial⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    exact ⟨h_pl, hh_pl, h_pref⟩
  BundleEnd := BilateralEnd.bundle
  teleological_bundle_dominance_induces_preference := by
    intro _ _ _ b1 b2 h_dom
    have h_global : TeleologicalBundleDominates bilateral_requirement b1 b2 :=
      (subjective_teleological_dominates_iff_teleological_of_universal
        bilateral_requirement (fun _ : BilateralEnd => True) (fun _ => trivial) b1 b2).mp h_dom
    exact bilateral_teleological_bundle_dominates_end_rank_lt b1 b2 h_global

instance : BilateralExchangeFrame BilateralTradeActionFrame where
  Offer := ModelAction.offer
  Accept := ModelAction.accept
  use_means_offer := by intro _ _ _ _ _ _ _; rfl
  yield_means_offer := by intro _ _ _ _ _ _ _; rfl
  use_means_accept := by intro _ _ _ _ _ _ _; rfl
  yield_means_accept := by intro _ _ _ _ _ _ _; rfl
  offer_inj := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact ModelAction.offer.inj h
  accept_inj := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact ModelAction.accept.inj h
  offer_ne_accept := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
  alpha_zero_ne_offer := by intro _ _ _ _ _ _ h; cases h
  alpha_zero_ne_accept := by intro _ _ _ _ _ _ h; cases h
  unilateral_offer_noop := by
    intro i j qA mA qB mB t t' h m h_enact h_not_acc h_next
    rcases bilateral_next_moment_cases h_next with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · fin_cases i <;> { dsimp [bilateral_enacted] at h_enact; cases h_enact }
    · fin_cases i
      · dsimp [bilateral_enacted] at h_enact
        cases h_enact
        fin_cases m <;> decide
      · dsimp [bilateral_enacted] at h_enact; cases h_enact
    · fin_cases i <;> { dsimp [bilateral_enacted] at h_enact; cases h_enact }
    · fin_cases i
      · dsimp [bilateral_enacted] at h_enact
        cases h_enact
        exfalso
        apply h_not_acc
        decide
      · dsimp [bilateral_enacted] at h_enact; cases h_enact
  unilateral_accept_noop := by
    intro j i qA mA qB mB t t' h m h_enact h_not_off h_next
    rcases bilateral_next_moment_cases h_next with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · fin_cases j <;> { dsimp [bilateral_enacted] at h_enact; cases h_enact }
    · fin_cases j <;> { dsimp [bilateral_enacted] at h_enact; cases h_enact }
    · fin_cases j
      · dsimp [bilateral_enacted] at h_enact; cases h_enact
      · dsimp [bilateral_enacted] at h_enact
        cases h_enact
        fin_cases m <;> decide
    · fin_cases j
      · dsimp [bilateral_enacted] at h_enact; cases h_enact
      · dsimp [bilateral_enacted] at h_enact
        cases h_enact
        exfalso
        apply h_not_off
        decide
  bilateral_transfer_law := by
    intro i j qA mA qB mB t t' h m h_ne h_enact_i h_enact_j h_next
    rcases bilateral_next_moment_cases h_next with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · fin_cases i <;> { dsimp [bilateral_enacted] at h_enact_i; cases h_enact_i }
    · fin_cases j <;> { dsimp [bilateral_enacted] at h_enact_j; cases h_enact_j }
    · fin_cases i <;> { dsimp [bilateral_enacted] at h_enact_i; cases h_enact_i }
    · fin_cases i <;> fin_cases j
      · exact (h_ne rfl).elim
      · dsimp [bilateral_enacted] at h_enact_i h_enact_j
        cases h_enact_i
        cases h_enact_j
        fin_cases m <;> decide
      · dsimp [bilateral_enacted] at h_enact_i; cases h_enact_i
      · exact (h_ne rfl).elim
  is_trade_action_def := by intro α; rfl

instance : IntertemporalEnds BilateralTradeActionFrame where
  TimedEnd := BilateralEnd.timed
  QuantityEnd := BilateralEnd.quantity
  timed_end_inj := by intro _ _ _ _ h; exact BilateralEnd.timed.inj h
  quantity_end_inj := by intro _ _ _ _ h; exact BilateralEnd.quantity.inj h

/-- ActionFrame for the bilateral trade model. -/
@[reducible] def SubjectiveBilateralTradeActionFrame : ActionFrame :=
  { BilateralTradeActionFrame with
    Agent := Fin 2
    Moment := BilateralMoment
    History := Fin 4
    Action := ModelAction
    Means := Fin 3
    Ends := BilateralEnd
    requirement := bilateral_subjective_requirement
    ValuedEnd := bilateral_subjective_valued_end
    valued_end_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
    MinPlausible := fun _ t => {bilateral_subjective_witness t}
    min_plausible_node_incidence := by
      intro _ t h' hh
      have heq : h' = bilateral_subjective_witness t := Set.mem_singleton_iff.mp hh
      subst h'
      change bilateral_mem_hist t (bilateral_subjective_witness t)
      cases t <;> simp [bilateral_subjective_witness, bilateral_mem_hist]
    min_plausible_nonempty := by
      intro _ t
      exact ⟨bilateral_subjective_witness t, Set.mem_singleton _⟩
    tau := fun _ t _ => t
    sigma := bilateral_sigma
    OutcomeOf := bilateral_subjective_outcome
    ExpectedMaturation := bilateral_subjective_maturation
    expected_maturation_mem_future := by
      intro i α t h ht _
      change bilateral_mem_hist (bilateral_subjective_maturation i α t h) h ∧
        (t = bilateral_subjective_maturation i α t h ∨
          bilateral_prec t (bilateral_subjective_maturation i α t h))
      change bilateral_mem_hist t h at ht
      cases t <;> fin_cases h <;>
        simp_all [bilateral_subjective_maturation, bilateral_terminal_moment,
          bilateral_mem_hist, bilateral_prec]
    End_of := bilateral_subjective_end
    End_of_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
    Preference := bilateral_subjective_preference
    Preference_bundle_invariant := by intro _ _ _ _ _ _; rfl
    pref_asymm := by
      intro i _ _ e1 e2 h12 h21
      cases e1 <;> cases e2 <;>
        simp_all only [bilateral_subjective_preference]
      · rcases h12 with ⟨_, ⟨S, hvalued, h_att, h_not⟩⟩
        exact h_not (h21.1 S hvalued h_att)
    doxastic_sure_thing_bridge := by
      intro i α β t h _h_app _h_weak h_strict
      rcases h_strict with ⟨h', hh', hpref⟩
      have heq : h' = bilateral_subjective_witness t := by
        simpa [bilateral_subjective_witness] using hh'
      subst h'
      simpa [bilateral_subjective_end, bilateral_subjective_witness,
        bilateral_subjective_maturation, bilateral_subjective_outcome] using hpref
    doxastic_plausible_support := by
      intro i α β t h _h_app hpref
      refine ⟨bilateral_subjective_witness t, ?_, ?_⟩
      · simp [bilateral_subjective_witness]
      · simpa [bilateral_subjective_end, bilateral_subjective_witness,
          bilateral_subjective_maturation, bilateral_subjective_outcome] using hpref
    teleological_bundle_dominance_induces_preference := by
      intro i t h b1 b2 hdom
      exact hdom }

instance : BilateralExchangeFrame SubjectiveBilateralTradeActionFrame where
  Offer := ModelAction.offer
  Accept := ModelAction.accept
  use_means_offer := by intro _ _ _ _ _ _ _; rfl
  yield_means_offer := by intro _ _ _ _ _ _ _; rfl
  use_means_accept := by intro _ _ _ _ _ _ _; rfl
  yield_means_accept := by intro _ _ _ _ _ _ _; rfl
  offer_inj := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact ModelAction.offer.inj h
  accept_inj := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact ModelAction.accept.inj h
  offer_ne_accept := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
  alpha_zero_ne_offer := by intro _ _ _ _ _ _ h; cases h
  alpha_zero_ne_accept := by intro _ _ _ _ _ _ h; cases h
  unilateral_offer_noop := by
    intro i j qA mA qB mB t t' h m h_enact h_not_acc h_next
    rcases bilateral_next_moment_cases h_next with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · fin_cases i <;> { dsimp [bilateral_enacted] at h_enact; cases h_enact }
    · fin_cases i
      · dsimp [bilateral_enacted] at h_enact
        cases h_enact
        fin_cases m <;> decide
      · dsimp [bilateral_enacted] at h_enact; cases h_enact
    · fin_cases i <;> { dsimp [bilateral_enacted] at h_enact; cases h_enact }
    · fin_cases i
      · dsimp [bilateral_enacted] at h_enact
        cases h_enact
        exfalso
        apply h_not_acc
        decide
      · dsimp [bilateral_enacted] at h_enact; cases h_enact
  unilateral_accept_noop := by
    intro j i qA mA qB mB t t' h m h_enact h_not_off h_next
    rcases bilateral_next_moment_cases h_next with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · fin_cases j <;> { dsimp [bilateral_enacted] at h_enact; cases h_enact }
    · fin_cases j <;> { dsimp [bilateral_enacted] at h_enact; cases h_enact }
    · fin_cases j
      · dsimp [bilateral_enacted] at h_enact; cases h_enact
      · dsimp [bilateral_enacted] at h_enact
        cases h_enact
        fin_cases m <;> decide
    · fin_cases j
      · dsimp [bilateral_enacted] at h_enact; cases h_enact
      · dsimp [bilateral_enacted] at h_enact
        cases h_enact
        exfalso
        apply h_not_off
        decide
  bilateral_transfer_law := by
    intro i j qA mA qB mB t t' h m h_ne h_enact_i h_enact_j h_next
    rcases bilateral_next_moment_cases h_next with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · fin_cases i <;> { dsimp [bilateral_enacted] at h_enact_i; cases h_enact_i }
    · fin_cases j <;> { dsimp [bilateral_enacted] at h_enact_j; cases h_enact_j }
    · fin_cases i <;> { dsimp [bilateral_enacted] at h_enact_i; cases h_enact_i }
    · fin_cases i <;> fin_cases j
      · exact (h_ne rfl).elim
      · dsimp [bilateral_enacted] at h_enact_i h_enact_j
        cases h_enact_i
        cases h_enact_j
        fin_cases m <;> decide
      · dsimp [bilateral_enacted] at h_enact_i; cases h_enact_i
      · exact (h_ne rfl).elim
  is_trade_action_def := by intro α; rfl

instance : IntertemporalEnds SubjectiveBilateralTradeActionFrame where
  TimedEnd := BilateralEnd.timed
  QuantityEnd := BilateralEnd.quantity
  timed_end_inj := by intro _ _ _ _ h; exact BilateralEnd.timed.inj h
  quantity_end_inj := by intro _ _ _ _ h; exact BilateralEnd.quantity.inj h

/-- The agents' actions can be selected independently at the root. -/
theorem bilateral_trade_model_stit_independent :
    STITAgentIndependence BilateralTradeActionFrame BilateralMoment.root := by
  intro s hs
  have hs0 := hs (0 : Fin 2) (0 : Fin 4) trivial
  have hs1 := hs (1 : Fin 2) (0 : Fin 4) trivial
  dsimp [ActionFrame.A_feas] at hs0 hs1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs0 hs1
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1
  · refine ⟨(0 : Fin 4), trivial, ?_⟩
    intro i
    fin_cases i
    · exact hs0.symm
    · exact hs1.symm
  · refine ⟨(2 : Fin 4), trivial, ?_⟩
    intro i
    fin_cases i
    · exact hs0.symm
    · exact hs1.symm
  · refine ⟨(1 : Fin 4), trivial, ?_⟩
    intro i
    fin_cases i
    · exact hs0.symm
    · exact hs1.symm
  · refine ⟨(3 : Fin 4), trivial, ?_⟩
    intro i
    fin_cases i
    · exact hs0.symm
    · exact hs1.symm

/-- Matched actions transfer one unit of each good on history 3. -/
theorem bilateral_trade_model_executes_matched_swap :
    bilateral_enacted 0 .root 3 = ModelAction.offer 0 1 1 0 1 1 ∧
    bilateral_enacted 1 .root 3 = ModelAction.accept 1 0 1 0 1 1 ∧
    bilateral_omega 0 .leaf3 3 0 = 1 ∧
    bilateral_omega 0 .leaf3 3 1 = 1 ∧
    bilateral_omega 1 .leaf3 3 0 = 1 ∧
    bilateral_omega 1 .leaf3 3 1 = 1 := by
  decide


theorem bilateral_trade_model_unilateral_offer_noop :
    bilateral_enacted 0 .root 1 = ModelAction.offer 0 1 1 0 1 1 ∧
    bilateral_enacted 1 .root 1 = ModelAction.idle ∧
    (∀ m : Fin 3, bilateral_omega 0 .leaf1 1 m = bilateral_omega 0 .root 1 m) := by
  refine ⟨rfl, rfl, ?_⟩
  intro m
  fin_cases m <;> decide


end Praxeology

end
