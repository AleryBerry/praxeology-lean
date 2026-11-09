/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Action
public import Praxeology.Subjective
public import Praxeology.Marginal.AllocationActionFrame
public import Praxeology.Catallactics.ProgramExchangeWitness
public import Praxeology.FirmWitness

/-!
# Veridical Scenario Constructors and Domain Witnesses

This module supplies the canonical veridical constructor and singleton-forecast
subjective constructor over arbitrary `ActionFrame`s, and demonstrates that
veridical allocation and spot exchange instantiate the same subjective action
architecture with verified `VeridicalAppraisal`.

Neither direction infers actual physical stocks from subjective forecasts or
conjectured scenarios without explicit veridical certificates.
-/

@[expose] public section

namespace Praxeology

/-- Canonical veridical scenario carrier for an ActionFrame: each scenario is a
decision moment and an actual history containing that moment. -/
structure VeridicalScenario (W : ActionFrame) where
  moment : W.Moment
  history : W.History
  mem_hist : W.mem_hist moment history

open Classical in
/-- The canonical veridical scenario frame over an arbitrary ActionFrame.
Scenarios are actual moments and valid histories; observation is the decision
node; and appraisal evaluates actions on the actual history embedding. -/
noncomputable def veridicalScenarioFrame (W : ActionFrame) : SubjectiveScenarioFrame W where
  Scenario := VeridicalScenario W
  Observation := W.Moment
  scenarioAnchor s := s.moment
  scenarioMenu i s := W.A_feas i s.moment s.history
  scenarioEnd i α s := W.End_of i α s.moment s.history
  observeActual _ t _ := t
  observeScenario _ s := s.moment
  MinPlausible _ t := { s : VeridicalScenario W | s.moment = t }
  plausible_nonempty _ t := by
    obtain ⟨h, hh⟩ := W.moment_in_history t
    exact ⟨⟨t, h, hh⟩, rfl⟩
  plausible_anchored_at_decision _ _ s hs := hs
  plausible_matches_actual_observation _ _ _ s _ hs := hs
  plausible_menus_cover_actual_options i t h s h_mem hs := by
    have hs_eq : s.moment = t := hs
    have hs_hist : t ∈ s.history := hs_eq ▸ s.mem_hist
    have h_eq : W.A_feas i t h = W.A_feas i s.moment s.history := by
      rw [hs_eq]
      exact W.A_feas_bundle_invariant i t h_mem hs_hist
    rw [h_eq]
  observation_shared_at_decision _ _ _ _ _ _ := rfl
  actualScenario _ t h :=
    if h_mem : W.mem_hist t h then ⟨t, h, h_mem⟩
    else ⟨t, Classical.choose (W.moment_in_history t),
      Classical.choose_spec (W.moment_in_history t)⟩
  actual_scenario_anchored _ t h _ := by split_ifs; rfl
  actual_scenario_observation _ t h _ := by split_ifs; rfl
  actual_scenario_end _ t h α _ := by split_ifs; rfl
  appraisedEnd i t h α := W.End_of i α t h
  appraisedEnd_supported i t h α h_mem hα := by
    refine ⟨⟨t, h, h_mem⟩, rfl, hα, rfl⟩
  appraisedEnd_respects_agreement _ t h α _ h_mem hagree := by
    have hs : (⟨t, h, h_mem⟩ : VeridicalScenario W) ∈
        { s : VeridicalScenario W | s.moment = t } := rfl
    have hres := hagree ⟨t, h, h_mem⟩ hs
    exact hres.2

/-- The canonical veridical frame satisfies the VeridicalAppraisal bridge. -/
theorem veridicalScenarioFrame_is_veridical (W : ActionFrame) :
    (veridicalScenarioFrame W).VeridicalAppraisal := by
  apply SubjectiveScenarioFrame.veridicalAppraisal_of_actual_scenario_selection
  intro i t h α h_mem
  dsimp [veridicalScenarioFrame]
  split_ifs
  rfl

/-- In the canonical veridical frame, subjective purposefulness coincides with
the ActionFrame's single `PurposefulAct` predicate. -/
@[simp] theorem purposefulAct_iff_veridical (W : ActionFrame)
    {i : W.Agent} {t : W.Moment} {h : W.History} {α : W.Action}
    (_h_mem : W.mem_hist t h) :
    (veridicalScenarioFrame W).PurposefulAct i t h α ↔
      @Praxeology.PurposefulAct W i t h α := by
  dsimp [SubjectiveScenarioFrame.PurposefulAct, PurposefulActWithEnd,
    Praxeology.PurposefulAct, PurposefulActUnder, veridicalScenarioFrame]
  rfl

/-!
## Subjective Singleton-Forecast Constructor
-/

/-- A specification of an independently conjectured economy for an ActionFrame.
Scenarios are independent of actual histories, forecasts are observation-dependent,
and the actor's intended end is obtained by executing conjectured scenarios. -/
structure SingletonForecastEconomy (W : ActionFrame) where
  Scenario : Type
  Observation : Type
  scenarioAnchor : Scenario → W.Moment
  scenarioMenu : W.Agent → Scenario → Finset W.Action
  scenarioEnd : W.Agent → W.Action → Scenario → W.Ends
  observeActual : W.Agent → W.Moment → W.History → Observation
  observeScenario : W.Agent → Scenario → Observation
  forecastScenario : W.Agent → W.Moment → Observation → Scenario
  forecast_anchored : ∀ i t obs, scenarioAnchor (forecastScenario i t obs) = t
  forecast_matches_observation : ∀ i t obs,
    observeScenario i (forecastScenario i t obs) = obs
  forecast_menu_covers : ∀ i t h, W.mem_hist t h →
    W.A_feas i t h ⊆ scenarioMenu i (forecastScenario i t (observeActual i t h))
  observation_shared_at_decision : ∀ i t h₁ h₂,
    W.mem_hist t h₁ → W.mem_hist t h₂ →
      observeActual i t h₁ = observeActual i t h₂
  actualScenario : W.Agent → W.Moment → W.History → Scenario
  actual_scenario_anchored : ∀ i t h, W.mem_hist t h →
    scenarioAnchor (actualScenario i t h) = t
  actual_scenario_observation : ∀ i t h, W.mem_hist t h →
    observeScenario i (actualScenario i t h) = observeActual i t h
  actual_scenario_end : ∀ i t h α, W.mem_hist t h →
    scenarioEnd i α (actualScenario i t h) = W.End_of i α t h

open Classical in
/-- Construct a SubjectiveScenarioFrame from an independently forecasted singleton economy. -/
noncomputable def singletonForecastScenarioFrame {W : ActionFrame}
    (E : SingletonForecastEconomy W) : SubjectiveScenarioFrame W where
  Scenario := E.Scenario
  Observation := E.Observation
  scenarioAnchor := E.scenarioAnchor
  scenarioMenu := E.scenarioMenu
  scenarioEnd := E.scenarioEnd
  observeActual := E.observeActual
  observeScenario := E.observeScenario
  MinPlausible i t := { s | s = E.forecastScenario i t
    (E.observeActual i t (Classical.choose (W.moment_in_history t))) }
  plausible_nonempty _ _ := ⟨_, rfl⟩
  plausible_anchored_at_decision i t s hs := by
    subst hs
    exact E.forecast_anchored i t _
  plausible_matches_actual_observation i t h s h_mem hs := by
    subst hs
    rw [E.forecast_matches_observation]
    exact E.observation_shared_at_decision i t
      (Classical.choose (W.moment_in_history t)) h
      (Classical.choose_spec (W.moment_in_history t)) h_mem
  plausible_menus_cover_actual_options i t h s h_mem hs := by
    subst hs
    have hobs := E.observation_shared_at_decision i t h
      (Classical.choose (W.moment_in_history t)) h_mem
      (Classical.choose_spec (W.moment_in_history t))
    rw [← hobs]
    exact E.forecast_menu_covers i t h h_mem
  observation_shared_at_decision := E.observation_shared_at_decision
  actualScenario := E.actualScenario
  actual_scenario_anchored := E.actual_scenario_anchored
  actual_scenario_observation := E.actual_scenario_observation
  actual_scenario_end := E.actual_scenario_end
  appraisedEnd i t h α :=
    E.scenarioEnd i α (E.forecastScenario i t (E.observeActual i t h))
  appraisedEnd_supported i t h α h_mem hα := by
    refine ⟨_, rfl, ?_, ?_⟩
    · have hobs := E.observation_shared_at_decision i t
        (Classical.choose (W.moment_in_history t)) h
        (Classical.choose_spec (W.moment_in_history t)) h_mem
      rw [hobs]
      exact E.forecast_menu_covers i t h h_mem hα
    · have hobs := E.observation_shared_at_decision i t
        (Classical.choose (W.moment_in_history t)) h
        (Classical.choose_spec (W.moment_in_history t)) h_mem
      rw [hobs]
  appraisedEnd_respects_agreement i t h α _ h_mem hagree := by
    have hmem : E.forecastScenario i t
        (E.observeActual i t (Classical.choose (W.moment_in_history t))) ∈
      { s | s = E.forecastScenario i t
        (E.observeActual i t (Classical.choose (W.moment_in_history t))) } := rfl
    have hobs := E.observation_shared_at_decision i t h
      (Classical.choose (W.moment_in_history t)) h_mem
      (Classical.choose_spec (W.moment_in_history t))
    rw [hobs]
    exact (hagree _ hmem).2

/-- Two independent singleton forecasts can change appraisal while sharing
the same actual physical frame. The cross-branch physical invariance makes the scope
explicit: intended ends differ across forecasts, while actual endowment and feasibility
remain identical across any histories incident at the decision moment by ActionFrame laws. -/
theorem forecast_change_preserves_physical_inventory
    {W : ActionFrame} (E₁ E₂ : SingletonForecastEconomy W)
    (i : W.Agent) (t : W.Moment) (h₁ h₂ : W.History) (m : W.Means)
    (α : W.Action) (hmem₁ : W.mem_hist t h₁) (hmem₂ : W.mem_hist t h₂) :
    W.omega i t h₁ m = W.omega i t h₂ m ∧
    (α ∈ W.A_feas i t h₁ ↔ α ∈ W.A_feas i t h₂) ∧
    (((singletonForecastScenarioFrame E₁).IntendedEnd i t h₁ α ≠
        (singletonForecastScenarioFrame E₂).IntendedEnd i t h₁ α) ↔
      (E₁.scenarioEnd i α (E₁.forecastScenario i t (E₁.observeActual i t h₁)) ≠
        E₂.scenarioEnd i α (E₂.forecastScenario i t (E₂.observeActual i t h₁)))) := by
  refine ⟨W.omega_bundle_invariant i t m hmem₁ hmem₂, ?_, ?_⟩
  · rw [W.A_feas_bundle_invariant i t hmem₁ hmem₂]
  · change (E₁.scenarioEnd i α (E₁.forecastScenario i t (E₁.observeActual i t h₁)) ≠
        E₂.scenarioEnd i α (E₂.forecastScenario i t (E₂.observeActual i t h₁))) ↔ _
    rfl

/-!
## Domain Veridical Instances: Allocation, Spot Exchange, and Firm
-/

/-- Veridical scenario frame for the two-agent allocation model. -/
noncomputable def allocationVeridicalScenarioFrame :
    SubjectiveScenarioFrame AllocationActionFrame.allocationChoiceFrame :=
  veridicalScenarioFrame AllocationActionFrame.allocationChoiceFrame

/-- The allocation veridical scenario frame satisfies VeridicalAppraisal. -/
theorem allocationVeridicalScenarioFrame_is_veridical :
    allocationVeridicalScenarioFrame.VeridicalAppraisal :=
  veridicalScenarioFrame_is_veridical AllocationActionFrame.allocationChoiceFrame

/-- The stock-one purposeful prefix choice lifts to the veridical scenario frame. -/
theorem allocation_stock_one_purposeful_in_veridical_frame :
    allocationVeridicalScenarioFrame.PurposefulAct
      (0 : Fin 2) none allocationFramePurposeHistory
      (allocationFrameRealize ({0} : Finset (Fin 3))) := by
  have hmem : AllocationActionFrame.allocationChoiceFrame.mem_hist
      none allocationFramePurposeHistory := Or.inl rfl
  exact (purposefulAct_iff_veridical AllocationActionFrame.allocationChoiceFrame hmem).2
    allocationFrame_stock_one_purposeful_prefix

/-- The stock-two purposeful prefix choice lifts to the veridical scenario frame. -/
theorem allocation_stock_two_purposeful_in_veridical_frame :
    allocationVeridicalScenarioFrame.PurposefulAct
      (1 : Fin 2) none allocationFramePurposeHistory
      (allocationFrameRealize ({0, 1} : Finset (Fin 3))) := by
  have hmem : AllocationActionFrame.allocationChoiceFrame.mem_hist
      none allocationFramePurposeHistory := Or.inl rfl
  exact (purposefulAct_iff_veridical AllocationActionFrame.allocationChoiceFrame hmem).2
    allocationFrame_stock_two_purposeful_prefix

/-- Veridical scenario frame for the matched two-good spot exchange witness. -/
noncomputable def exchangeVeridicalScenarioFrame :
    SubjectiveScenarioFrame ProgramExchangeWitness.frame :=
  veridicalScenarioFrame ProgramExchangeWitness.frame

/-- The spot exchange veridical scenario frame satisfies VeridicalAppraisal. -/
theorem exchangeVeridicalScenarioFrame_is_veridical :
    exchangeVeridicalScenarioFrame.VeridicalAppraisal :=
  veridicalScenarioFrame_is_veridical ProgramExchangeWitness.frame

/-- Veridical scenario frame for the concrete praxeological workshop model. -/
noncomputable def workshopVeridicalScenarioFrame :
    SubjectiveScenarioFrame WorkshopActionFrame :=
  veridicalScenarioFrame WorkshopActionFrame

/-- The workshop veridical scenario frame satisfies VeridicalAppraisal. -/
theorem workshopVeridicalScenarioFrame_is_veridical :
    workshopVeridicalScenarioFrame.VeridicalAppraisal :=
  veridicalScenarioFrame_is_veridical WorkshopActionFrame

/-- The entrepreneur's purposeful proposal lifts to the veridical scenario frame. -/
theorem workshop_entrepreneur_proposal_in_veridical_frame :
    workshopVeridicalScenarioFrame.PurposefulAct
      .entrepreneur WMoment.root (0 : WorkshopHist) WorkshopAction.proposeScope := by
  have hmem : WorkshopActionFrame.mem_hist WMoment.root (0 : WorkshopHist) := trivial
  exact (purposefulAct_iff_veridical WorkshopActionFrame hmem).2
    entrepreneur_purposeful_proposal

/-- Grand Unification: Allocation, spot exchange, and firm organization are all
instances of the exact same `SubjectiveScenarioFrame` architecture with verified
`VeridicalAppraisal` bridges. Neither requires identified forecasts or implicit
physical inventory facts. -/
theorem veridical_allocation_and_exchange_unified :
    allocationVeridicalScenarioFrame.VeridicalAppraisal ∧
    exchangeVeridicalScenarioFrame.VeridicalAppraisal ∧
    workshopVeridicalScenarioFrame.VeridicalAppraisal :=
  ⟨allocationVeridicalScenarioFrame_is_veridical,
   exchangeVeridicalScenarioFrame_is_veridical,
   workshopVeridicalScenarioFrame_is_veridical⟩

end Praxeology
