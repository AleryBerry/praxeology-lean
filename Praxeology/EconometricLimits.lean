/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Marginal

/-!
# Econometric Limits: Non-Identifiability and Regime Uncertainty

This module formalizes the epistemic and econometric limits of empirical observation
in praxeology, specifically demonstrating the non-identifiability of structural
preference parameters and causal models from observed action trajectories alone.
-/

@[expose] public section

namespace Praxeology

/-- An econometric candidate interpretation of an ActionFrame W, specifying
an outcome function and preference relation on the carrier types of W. -/
structure EconometricInterpretation (W : ActionFrame) where
  End_of : W.Agent → W.Action → W.Moment → W.History → W.Ends
  Preference : W.Agent → W.Moment → W.History → W.Ends → W.Ends → Prop
  pref_asymm : ∀ i t h e₁ e₂, Preference i t h e₁ e₂ → ¬ Preference i t h e₂ e₁

/-- The canonical interpretation directly given by the ActionFrame itself. -/
def ActionFrame.canonicalInterpretation (W : ActionFrame) : EconometricInterpretation W where
  End_of := W.End_of
  Preference := W.Preference
  pref_asymm := W.pref_asymm

/-- Purposeful action under an econometric interpretation of an ActionFrame. -/
def PurposefulUnder (W : ActionFrame) (interp : EconometricInterpretation W)
    (i : W.Agent) (t : W.Moment) (h : W.History) (α : W.Action) : Prop :=
  α ∈ W.A_feas i t h ∧
  (W.mem_hist t h ∧ W.enacted i t h = α) ∧
  (α = W.alpha_zero ∨
    interp.Preference i t h (interp.End_of i α t h) (interp.End_of i W.alpha_zero t h)) ∧
  ∀ β ∈ W.A_feas i t h, ¬ interp.Preference i t h (interp.End_of i β t h) (interp.End_of i α t h)

/-- Purposeful action under the canonical interpretation matches PurposefulAct. -/
theorem purposefulUnder_canonical_iff (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (α : W.Action) :
    PurposefulUnder W W.canonicalInterpretation i t h α ↔ @PurposefulAct W i t h α := by
  dsimp [PurposefulUnder, PurposefulAct, PurposefulActUnder,
    ActionFrame.canonicalInterpretation, Exec, ChoicePartition]
  rfl

/-- An empirically observable record consists of the enacted action and the realized end. -/
structure HistoricalObservation (W : ActionFrame) where
  enacted_act : W.Action
  realized_end : W.Ends
  deriving DecidableEq

/-- The enacted action and resulting outcome at `⟨t, h⟩` under interpretation `interp`. -/
def observe (W : ActionFrame) (interp : EconometricInterpretation W)
    (i : W.Agent) (t : W.Moment) (h : W.History) : HistoricalObservation W :=
  ⟨W.enacted i t h, interp.End_of i (W.enacted i t h) t h⟩

/-- Two interpretations are observationally equivalent at `⟨t, h⟩` if records match. -/
def ObsEquiv (W : ActionFrame) (interp₁ interp₂ : EconometricInterpretation W)
    (i : W.Agent) (t : W.Moment) (h : W.History) : Prop :=
  observe W interp₁ i t h = observe W interp₂ i t h

/-- A function from historical observations to parameter values. -/
def EconometricEstimator (W : ActionFrame) (Θ : Type) : Type :=
  HistoricalObservation W → Θ

/-- An estimator identifies a parameter function `f` over model class `M` at `⟨t, h⟩`. -/
def Identifies (W : ActionFrame)
    (M : Set (EconometricInterpretation W))
    (f : EconometricInterpretation W → Θ)
    (est : EconometricEstimator W Θ)
    (i : W.Agent) (t : W.Moment) (h : W.History) : Prop :=
  ∀ interp ∈ M, est (observe W interp i t h) = f interp

/-- Master non-identifiability theorem: an empirical estimator cannot distinguish models that
share an observable record but diverge in structural parameters. -/
theorem non_identifiability_of_divergent_models
    {W : ActionFrame} {Θ : Type}
    (M : Set (EconometricInterpretation W))
    (f : EconometricInterpretation W → Θ)
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (interp₁ interp₂ : EconometricInterpretation W)
    (h₁ : interp₁ ∈ M) (h₂ : interp₂ ∈ M)
    (h_obs : ObsEquiv W interp₁ interp₂ i t h)
    (h_diff : f interp₁ ≠ f interp₂) :
    ¬ ∃ est : EconometricEstimator W Θ, Identifies W M f est i t h := by
  rintro ⟨est, h_id⟩
  have h_id1 := h_id interp₁ h₁
  have h_id2 := h_id interp₂ h₂
  dsimp [ObsEquiv] at h_obs
  rw [h_obs] at h_id1
  exact h_diff (h_id1.symm.trans h_id2)

/-- Causal counterfactual parameters cannot be identified from realized historical trajectories. -/
theorem causal_econometric_non_identifiability
    (W : ActionFrame)
    (interp₁ : EconometricInterpretation W)
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (h_act : PurposefulUnder W interp₁ i t h (W.enacted i t h))
    (h₀ : W.History) (h_ne : h₀ ≠ h)
    (e_alt : W.Ends)
    (h_diff_end : e_alt ≠ interp₁.End_of i W.alpha_zero t h₀) :
    ∃ interp₂ : EconometricInterpretation W,
      PurposefulUnder W interp₂ i t h (W.enacted i t h) ∧
      ObsEquiv W interp₁ interp₂ i t h ∧
      interp₁.End_of i W.alpha_zero t h₀ ≠ interp₂.End_of i W.alpha_zero t h₀ := by
  classical
  let End_of₂ : W.Agent → W.Action → W.Moment → W.History → W.Ends :=
    fun a act m hist =>
      if a = i ∧ act = W.alpha_zero ∧ m = t ∧ hist = h₀ then e_alt
      else interp₁.End_of a act m hist
  let interp₂ : EconometricInterpretation W := {
    End_of := End_of₂
    Preference := interp₁.Preference
    pref_asymm := interp₁.pref_asymm
  }
  have h_same_at_h : ∀ a act m, End_of₂ a act m h = interp₁.End_of a act m h := by
    intro a act m
    dsimp [End_of₂]
    have h_not_h₀ : ¬ (a = i ∧ act = W.alpha_zero ∧ m = t ∧ h = h₀) := by
      intro ⟨_, _, _, h_eq⟩
      exact h_ne h_eq.symm
    rw [ite_eq_right h_not_h₀]
  have h_act₂ : PurposefulUnder W interp₂ i t h (W.enacted i t h) := by
    rcases h_act with ⟨h_feas, h_exec, h_pref_idle, h_undom⟩
    refine ⟨h_feas, h_exec, ?_, ?_⟩
    · cases h_pref_idle with
      | inl h_idle => exact Or.inl h_idle
      | inr h_pref =>
        right
        dsimp [interp₂]
        rw [h_same_at_h i (W.enacted i t h) t, h_same_at_h i W.alpha_zero t]
        exact h_pref
    · intro β hβ
      dsimp [interp₂]
      rw [h_same_at_h i β t, h_same_at_h i (W.enacted i t h) t]
      exact h_undom β hβ
  have h_obs : ObsEquiv W interp₁ interp₂ i t h := by
    dsimp [ObsEquiv, observe, interp₂]
    rw [h_same_at_h i (W.enacted i t h) t]
  have h_diff : interp₁.End_of i W.alpha_zero t h₀ ≠ interp₂.End_of i W.alpha_zero t h₀ := by
    dsimp [interp₂, End_of₂]
    have h_cond : (i = i ∧ W.alpha_zero = W.alpha_zero ∧ t = t ∧ h₀ = h₀) := ⟨rfl, rfl, rfl, rfl⟩
    rw [ite_eq_left h_cond]
    exact h_diff_end.symm
  exact ⟨interp₂, h_act₂, h_obs, h_diff⟩

/-- Lucas Critique: changing outcomes for unchosen actions alters purposeful optimality. -/
theorem lucas_critique_policy_invariance_failure
    (W : ActionFrame)
    (interp : EconometricInterpretation W)
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (α_star β : W.Action)
    (h_distinct : α_star ≠ β)
    (_h_enacted : W.enacted i t h = α_star)
    (hβ_in : β ∈ W.A_feas i t h)
    (e_great : W.Ends)
    (h_dominate : interp.Preference i t h e_great (interp.End_of i α_star t h)) :
    let End_of_new : W.Agent → W.Action → W.Moment → W.History → W.Ends :=
      fun a act m hist =>
        if a = i ∧ act = β ∧ m = t ∧ hist = h then e_great
        else interp.End_of a act m hist
    let interp_new : EconometricInterpretation W := {
      interp with End_of := End_of_new
    }
    ¬ PurposefulUnder W interp_new i t h α_star := by
  classical
  intro End_of_new interp_new h_act_new
  have h_undom := h_act_new.2.2.2 β hβ_in
  dsimp [interp_new, End_of_new] at h_undom
  have h_cond_β : (i = i ∧ β = β ∧ t = t ∧ h = h) := ⟨rfl, rfl, rfl, rfl⟩
  rw [ite_eq_left h_cond_β] at h_undom
  have h_cond_en : ¬ (i = i ∧ α_star = β ∧ t = t ∧ h = h) := by
    intro ⟨_, h_eq, _, _⟩
    exact h_distinct h_eq
  rw [ite_eq_right h_cond_en] at h_undom
  exact h_undom h_dominate

/-- Instrumental Variable exclusion restrictions are unverifiable from observed choices alone. -/
theorem iv_exclusion_restriction_unverifiable
    [W : ActionFrame] {Inst : Type}
    (α_star α_alt : W.Action) (h_diff_act : α_star ≠ α_alt)
    (z₁ z₂ : Inst) (hz_diff : z₁ ≠ z₂)
    (e_obs : W.Ends) (e₁ e₂ : W.Ends) (h_diff_e : e₁ ≠ e₂) :
    ∃ (IV_valid IV_invalid : Inst → W.Action → W.Ends),
      (∀ z, IV_valid z α_star = e_obs) ∧
      (∀ z, IV_invalid z α_star = e_obs) ∧
      (∀ a, IV_valid z₁ a = IV_valid z₂ a) ∧
      (IV_invalid z₁ α_alt ≠ IV_invalid z₂ α_alt) := by
  classical
  let IV_valid : Inst → Action → Ends :=
    fun _ a => if a = α_star then e_obs else e₁
  let IV_invalid : Inst → Action → Ends :=
    fun z a =>
      if a = α_star then e_obs
      else if z = z₁ then e₁ else e₂
  have h_obs_valid : ∀ z, IV_valid z α_star = e_obs := by
    intro z
    dsimp [IV_valid]
    rw [ite_eq_left rfl]
  have h_obs_invalid : ∀ z, IV_invalid z α_star = e_obs := by
    intro z
    dsimp [IV_invalid]
    rw [ite_eq_left rfl]
  have h_excl_valid : ∀ a, IV_valid z₁ a = IV_valid z₂ a := by
    intro a
    dsimp [IV_valid]
  have h_viol_invalid : IV_invalid z₁ α_alt ≠ IV_invalid z₂ α_alt := by
    dsimp [IV_invalid]
    have h_ne_star : α_alt ≠ α_star := h_diff_act.symm
    rw [ite_eq_right h_ne_star, ite_eq_right h_ne_star]
    rw [ite_eq_left rfl]
    have hz_ne : ¬ (z₂ = z₁) := fun h => hz_diff h.symm
    rw [ite_eq_right hz_ne]
    exact h_diff_e
  exact ⟨IV_valid, IV_invalid, h_obs_valid, h_obs_invalid, h_excl_valid, h_viol_invalid⟩

/-- Duhem-Quine underdetermination: alternative structural theories predict identical
observations on realized paths while diverging on unselected counterfactuals. -/
theorem duhem_quine_underdetermination
    (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (α_star α_cf : W.Action) (h_diff_act : α_star ≠ α_cf)
    (e_obs : W.Ends) (e_cf₁ e_cf₂ : W.Ends) (h_diff_cf : e_cf₁ ≠ e_cf₂) :
    ∃ (interp₁ interp₂ : EconometricInterpretation W),
      (interp₁.End_of i α_star t h = e_obs ∧ interp₂.End_of i α_star t h = e_obs) ∧
      (interp₁.End_of i α_cf t h ≠ interp₂.End_of i α_cf t h) := by
  classical
  let End_of₁ : W.Agent → W.Action → W.Moment → W.History → W.Ends :=
    fun a act m hist =>
      if a = i ∧ act = α_star ∧ m = t ∧ hist = h then e_obs
      else e_cf₁
  let End_of₂ : W.Agent → W.Action → W.Moment → W.History → W.Ends :=
    fun a act m hist =>
      if a = i ∧ act = α_star ∧ m = t ∧ hist = h then e_obs
      else e_cf₂
  let interp₁ : EconometricInterpretation W := {
    End_of := End_of₁
    Preference := W.Preference
    pref_asymm := W.pref_asymm
  }
  let interp₂ : EconometricInterpretation W := {
    End_of := End_of₂
    Preference := W.Preference
    pref_asymm := W.pref_asymm
  }
  have h1 : interp₁.End_of i α_star t h = e_obs := by
    dsimp [interp₁, End_of₁]
    have h_cond : (i = i ∧ α_star = α_star ∧ t = t ∧ h = h) := ⟨rfl, rfl, rfl, rfl⟩
    rw [ite_eq_left h_cond]
  have h2 : interp₂.End_of i α_star t h = e_obs := by
    dsimp [interp₂, End_of₂]
    have h_cond : (i = i ∧ α_star = α_star ∧ t = t ∧ h = h) := ⟨rfl, rfl, rfl, rfl⟩
    rw [ite_eq_left h_cond]
  have h_cf : interp₁.End_of i α_cf t h ≠ interp₂.End_of i α_cf t h := by
    dsimp [interp₁, interp₂, End_of₁, End_of₂]
    have h_ne : ¬ (i = i ∧ α_cf = α_star ∧ t = t ∧ h = h) := by
      intro ⟨_, h_eq, _⟩
      exact h_diff_act h_eq.symm
    rw [ite_eq_right h_ne, ite_eq_right h_ne]
    exact h_diff_cf
  exact ⟨interp₁, interp₂, ⟨h1, h2⟩, h_cf⟩

/-- Duhem-Quine underdetermination with purposeful rationalization: alternative structural
theories predict identical observations on realized paths while diverging on counterfactual
histories, with both rationalizing the enacted purposeful choice. -/
theorem duhem_quine_underdetermination_purposeful
    (W : ActionFrame)
    (interp₁ : EconometricInterpretation W)
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (h_act : PurposefulUnder W interp₁ i t h (W.enacted i t h))
    (h₀ : W.History) (h_ne : h₀ ≠ h)
    (α_cf : W.Action) (e_alt : W.Ends)
    (h_diff_end : e_alt ≠ interp₁.End_of i α_cf t h₀) :
    ∃ interp₂ : EconometricInterpretation W,
      PurposefulUnder W interp₂ i t h (W.enacted i t h) ∧
      interp₁.End_of i (W.enacted i t h) t h = interp₂.End_of i (W.enacted i t h) t h ∧
      interp₁.End_of i α_cf t h₀ ≠ interp₂.End_of i α_cf t h₀ := by
  classical
  let End_of₂ : W.Agent → W.Action → W.Moment → W.History → W.Ends :=
    fun a act m hist =>
      if a = i ∧ act = α_cf ∧ m = t ∧ hist = h₀ then e_alt
      else interp₁.End_of a act m hist
  let interp₂ : EconometricInterpretation W := {
    End_of := End_of₂
    Preference := interp₁.Preference
    pref_asymm := interp₁.pref_asymm
  }
  have h_same_at_h : ∀ a act m, End_of₂ a act m h = interp₁.End_of a act m h := by
    intro a act m
    dsimp [End_of₂]
    have h_not_h₀ : ¬ (a = i ∧ act = α_cf ∧ m = t ∧ h = h₀) := by
      intro ⟨_, _, _, h_eq⟩
      exact h_ne h_eq.symm
    rw [ite_eq_right h_not_h₀]
  have h_act₂ : PurposefulUnder W interp₂ i t h (W.enacted i t h) := by
    rcases h_act with ⟨h_feas, h_exec, h_pref_idle, h_undom⟩
    refine ⟨h_feas, h_exec, ?_, ?_⟩
    · cases h_pref_idle with
      | inl h_idle => exact Or.inl h_idle
      | inr h_pref =>
        right
        dsimp [interp₂]
        rw [h_same_at_h i (W.enacted i t h) t, h_same_at_h i W.alpha_zero t]
        exact h_pref
    · intro β hβ
      dsimp [interp₂]
      rw [h_same_at_h i β t, h_same_at_h i (W.enacted i t h) t]
      exact h_undom β hβ
  have h_same_enacted :
      interp₁.End_of i (W.enacted i t h) t h = interp₂.End_of i (W.enacted i t h) t h := by
    dsimp [interp₂]
    rw [h_same_at_h i (W.enacted i t h) t]
  have h_diff : interp₁.End_of i α_cf t h₀ ≠ interp₂.End_of i α_cf t h₀ := by
    dsimp [interp₂, End_of₂]
    have h_cond : (i = i ∧ α_cf = α_cf ∧ t = t ∧ h₀ = h₀) := ⟨rfl, rfl, rfl, rfl⟩
    rw [ite_eq_left h_cond]
    exact h_diff_end.symm
  exact ⟨interp₂, h_act₂, h_same_enacted, h_diff⟩

/-- Discrete macroeconomic regimes of capital structure. -/
inductive CapitalRegime where
  | Absorption : CapitalRegime
  | Liquidation : CapitalRegime
  deriving DecidableEq

/-- Austrian Business Cycle Theory: macro-aggregate observations do not identify whether capital
goods are experiencing sustainable absorption or unsustainable liquidation. -/
theorem abct_macro_aggregate_regime_non_identifiability
    {W : ActionFrame}
    (M : Set (EconometricInterpretation W))
    (regimeOf : EconometricInterpretation W → CapitalRegime)
    (i : W.Agent) (t0 : W.Moment) (h : W.History)
    (interp_absorb interp_liquidate : EconometricInterpretation W)
    (h_absorb : interp_absorb ∈ M)
    (h_liquidate : interp_liquidate ∈ M)
    (h_obs : ObsEquiv W interp_absorb interp_liquidate i t0 h)
    (h_diff_regime : regimeOf interp_absorb ≠ regimeOf interp_liquidate) :
    ¬ ∃ est : EconometricEstimator W CapitalRegime,
      Identifies W M regimeOf est i t0 h :=
  non_identifiability_of_divergent_models M regimeOf i t0 h
    interp_absorb interp_liquidate h_absorb h_liquidate h_obs h_diff_regime

/-- Constructive witness of ABCT regime non-identifiability on FiniteBranchingModel. -/
theorem abct_regime_non_identifiability_witness :
    ∃ (W : ActionFrame)
      (interp_absorb interp_liquidate : EconometricInterpretation W)
      (regimeOf : EconometricInterpretation W → CapitalRegime)
      (i : W.Agent) (t : W.Moment) (h : W.History),
      ObsEquiv W interp_absorb interp_liquidate i t h ∧
      regimeOf interp_absorb = CapitalRegime.Absorption ∧
      regimeOf interp_liquidate = CapitalRegime.Liquidation ∧
      regimeOf interp_absorb ≠ regimeOf interp_liquidate := by
  let W : ActionFrame := FiniteBranchingModel
  let i : W.Agent := (0 : Fin 2)
  let t : W.Moment := (0 : Fin 4)
  let h : W.History := (0 : Fin 3)
  let e_base : W.Ends := ModelEnd.baseline
  let e_alt : W.Ends := ModelEnd.quantity 0 1
  let interp_absorb : EconometricInterpretation W := {
    End_of := fun _ act _ _ =>
      if act = ModelAction.idle then e_base
      else e_alt
    Preference := W.Preference
    pref_asymm := W.pref_asymm
  }
  let interp_liquidate : EconometricInterpretation W := {
    End_of := fun _ _ _ _ => e_base
    Preference := W.Preference
    pref_asymm := W.pref_asymm
  }
  let regimeOf : EconometricInterpretation W → CapitalRegime :=
    fun interp =>
      if interp.End_of i ModelAction.consume t h = e_alt
      then CapitalRegime.Absorption else CapitalRegime.Liquidation
  refine ⟨W, interp_absorb, interp_liquidate, regimeOf, i, t, h, ?_, ?_, ?_, by decide⟩
  · dsimp [ObsEquiv, observe, interp_absorb, interp_liquidate]
    have h_idle : W.enacted i t h = ModelAction.idle := by
      rfl
    rw [h_idle]
    dsimp
  · dsimp [regimeOf, interp_absorb]
  · dsimp [regimeOf, interp_liquidate]

/-- Discrete economic causes of loan default. -/
inductive DefaultCause where
  | Illiquidity : DefaultCause
  | Strategic : DefaultCause
  deriving DecidableEq

/-- Strategic Default vs. Illiquidity Non-Identifiability:
External historical observation of default (inaction `alpha_zero` at maturity `t_mat`)
cannot identify whether the default was caused by hard physical illiquidity
(`omega borrower < repayment`, making repayment resource-infeasible)
or strategic default (`repayment ≤ omega borrower`, where repayment was feasible
but the borrower strictly preferred default/inaction). -/
theorem default_illiquidity_vs_strategic_non_identifiability
    {W : ActionFrame}
    (M : Set (EconometricInterpretation W))
    (causeOf : EconometricInterpretation W → DefaultCause)
    (borrower : W.Agent) (t_mat : W.Moment) (h : W.History)
    (interp_illiq interp_strat : EconometricInterpretation W)
    (h_illiq : interp_illiq ∈ M)
    (h_strat : interp_strat ∈ M)
    (h_obs : ObsEquiv W interp_illiq interp_strat borrower t_mat h)
    (h_diff_cause : causeOf interp_illiq ≠ causeOf interp_strat) :
    ¬ ∃ est : EconometricEstimator W DefaultCause,
      Identifies W M causeOf est borrower t_mat h :=
  non_identifiability_of_divergent_models M causeOf borrower t_mat h
    interp_illiq interp_strat h_illiq h_strat h_obs h_diff_cause

/-- Constructive witness of default cause non-identifiability on FiniteBranchingModel.
At loan maturity, external observation of borrower inaction cannot distinguish
illiquidity from strategic default. -/
theorem default_cause_non_identifiability_witness :
    ∃ (W : ActionFrame)
      (interp_illiq interp_strat : EconometricInterpretation W)
      (causeOf : EconometricInterpretation W → DefaultCause)
      (borrower : W.Agent) (t_mat : W.Moment) (h : W.History),
      ObsEquiv W interp_illiq interp_strat borrower t_mat h ∧
      causeOf interp_illiq = DefaultCause.Illiquidity ∧
      causeOf interp_strat = DefaultCause.Strategic ∧
      causeOf interp_illiq ≠ causeOf interp_strat := by
  let W : ActionFrame := FiniteBranchingModel
  let borrower : W.Agent := (0 : Fin 2)
  let t_mat : W.Moment := (0 : Fin 4)
  let h : W.History := (0 : Fin 3)
  let e_base : W.Ends := ModelEnd.baseline
  let e_repay : W.Ends := ModelEnd.quantity 0 1
  let interp_illiq : EconometricInterpretation W := {
    End_of := fun _ _ _ _ => e_base
    Preference := W.Preference
    pref_asymm := W.pref_asymm
  }
  let interp_strat : EconometricInterpretation W := {
    End_of := fun _ act _ _ =>
      if act = ModelAction.idle then e_base
      else e_repay
    Preference := W.Preference
    pref_asymm := W.pref_asymm
  }
  let causeOf : EconometricInterpretation W → DefaultCause :=
    fun interp =>
      if interp.End_of borrower ModelAction.consume t_mat h = e_repay
      then DefaultCause.Strategic else DefaultCause.Illiquidity
  refine ⟨W, interp_illiq, interp_strat, causeOf, borrower, t_mat, h, ?_, ?_, ?_, by decide⟩
  · dsimp [ObsEquiv, observe, interp_illiq, interp_strat]
    have h_idle : W.enacted borrower t_mat h = ModelAction.idle := rfl
    rw [h_idle]
    dsimp
  · dsimp [causeOf, interp_illiq]
  · dsimp [causeOf, interp_strat]

end Praxeology
