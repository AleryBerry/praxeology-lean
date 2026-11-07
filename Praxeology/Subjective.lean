/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Action

/-!
# Subjective appraisal over conjectured economies

This interface separates conjectured scenarios from actual ActionFrame
histories. Plausible scenarios share the observed decision node and its
observation, while their unobserved inventories and financing histories may
differ. The frame supplies its appraisal rule explicitly. A separate optional
veridical projection is needed before subjective ends can be used as actual
intended ends in the existing `PurposefulAct` predicate.
-/

@[expose] public section

namespace Praxeology

/-- A subjective scenario system over an existing physical and behavioral
ActionFrame. The scenario carrier is independent of actual histories. -/
structure SubjectiveScenarioFrame (W : ActionFrame) where
  Scenario : Type
  Observation : Type
  scenarioAnchor : Scenario → W.Moment
  scenarioMenu : W.Agent → Scenario → Finset W.Action
  scenarioEnd : W.Agent → W.Action → Scenario → W.Ends
  observeActual : W.Agent → W.Moment → W.History → Observation
  observeScenario : W.Agent → Scenario → Observation
  MinPlausible : W.Agent → W.Moment → Set Scenario
  plausible_nonempty : ∀ i t, (MinPlausible i t).Nonempty
  plausible_anchored_at_decision : ∀ i t s, s ∈ MinPlausible i t →
    scenarioAnchor s = t
  plausible_matches_actual_observation : ∀ i t h s,
    W.mem_hist t h → s ∈ MinPlausible i t →
      observeScenario i s = observeActual i t h
  plausible_menus_cover_actual_options : ∀ i t h s,
    W.mem_hist t h → s ∈ MinPlausible i t →
      W.A_feas i t h ⊆ scenarioMenu i s
  observation_shared_at_decision : ∀ i t h₁ h₂,
    W.mem_hist t h₁ → W.mem_hist t h₂ →
      observeActual i t h₁ = observeActual i t h₂
  /-- Every actual decision has an associated scenario. Its membership in the
  agent's plausible set is intentionally not required. -/
  actualScenario : W.Agent → W.Moment → W.History → Scenario
  actual_scenario_anchored : ∀ i t h, W.mem_hist t h →
    scenarioAnchor (actualScenario i t h) = t
  actual_scenario_observation : ∀ i t h, W.mem_hist t h →
    observeScenario i (actualScenario i t h) = observeActual i t h
  /-- The actual-economy embedding agrees with the ActionFrame's actual
  intended end. This does not assert that the embedding is plausible. -/
  actual_scenario_end : ∀ i t h α, W.mem_hist t h →
    scenarioEnd i α (actualScenario i t h) = W.End_of i α t h
  /-- The selected appraisal rule maps an action to one end, even when several
  plausible scenarios disagree. -/
  appraisedEnd : W.Agent → W.Moment → W.History → W.Action → W.Ends
  appraisedEnd_supported : ∀ i t h α, W.mem_hist t h →
    α ∈ W.A_feas i t h →
      ∃ s, s ∈ MinPlausible i t ∧ α ∈ scenarioMenu i s ∧
        appraisedEnd i t h α = scenarioEnd i α s
  /-- If all plausible scenarios agree on an action's end, appraisal respects
  that agreement. Multiple-scenario aggregation remains an explicit frame
  input rather than an implicit identification with actual inventories. -/
  appraisedEnd_respects_agreement : ∀ i t h α e,
    W.mem_hist t h →
      (∀ s, s ∈ MinPlausible i t →
        α ∈ scenarioMenu i s ∧ scenarioEnd i α s = e) →
      appraisedEnd i t h α = e

namespace SubjectiveScenarioFrame

variable {W : ActionFrame} (M : SubjectiveScenarioFrame W)

/-- The subjective intended end supplied by the explicit appraisal rule. -/
abbrev IntendedEnd (i : W.Agent) (t : W.Moment) (h : W.History)
    (α : W.Action) : W.Ends := M.appraisedEnd i t h α

/-- Subjective purposefulness is the same generic choice condition with the
scenario appraisal as its intended-end evaluator. Physical feasibility and
execution still refer to the actual ActionFrame. -/
abbrev PurposefulAct (i : W.Agent) (t : W.Moment) (h : W.History)
    (α : W.Action) : Prop :=
  PurposefulActWithEnd (fun j β s h' => M.IntendedEnd j s h' β)
    (W.Preference i t h) i t h α

/-- An optional bridge showing that appraisal in a particular model is
veridical. The scenario system itself does not require this bridge. -/
structure VeridicalAppraisal : Prop where
  appraised_as_actual_scenario : ∀ i t h α, W.mem_hist t h →
    M.appraisedEnd i t h α =
      M.scenarioEnd i α (M.actualScenario i t h)

/-- A scenario-grounded choice certificate records physical feasibility and
execution separately from subjective improvement and menu undominatedness.
It is evidence for the single ActionFrame `PurposefulAct` only after a
veridical appraisal projection is supplied. -/
structure PurposefulAppraisalCertificate
    (i : W.Agent) (t : W.Moment) (h : W.History) (α : W.Action) : Prop where
  feasible : α ∈ W.A_feas i t h
  executes : @Exec W i t α h
  improves_on_idle : α = W.alpha_zero ∨
    W.Preference i t h (M.IntendedEnd i t h α)
      (M.IntendedEnd i t h W.alpha_zero)
  undominated : ∀ β, β ∈ W.A_feas i t h →
    ¬ W.Preference i t h (M.IntendedEnd i t h β)
      (M.IntendedEnd i t h α)

/-- Scenario-based appraisal evidence proves the common purposeful-choice
condition without projecting the conjectured end onto actual inventory. -/
theorem purposefulAct_of_appraisal_certificate_subjective
    {i : W.Agent} {t : W.Moment} {h : W.History} {α : W.Action}
    (C : M.PurposefulAppraisalCertificate i t h α) :
    M.PurposefulAct i t h α :=
  ⟨C.feasible, C.executes, C.improves_on_idle, C.undominated⟩

/-- Veridical scenario appraisal converts its choice certificate into the
existing purposeful-action predicate without inferring physical stock facts
from a conjectured scenario. -/
theorem purposefulAct_of_appraisal_certificate
    {i : W.Agent} {t : W.Moment} {h : W.History} {α : W.Action}
    (V : M.VeridicalAppraisal)
    (C : M.PurposefulAppraisalCertificate i t h α) :
    @Praxeology.PurposefulAct W i t h α := by
  have hsubjective : M.PurposefulAct i t h α :=
    M.purposefulAct_of_appraisal_certificate_subjective C
  have hprojection (β : W.Action) :
      (fun j γ s h' => M.IntendedEnd j s h' γ) i β t h = End_of i β t h := by
    change M.appraisedEnd i t h β = End_of i β t h
    rw [V.appraised_as_actual_scenario i t h β C.executes.1]
    exact M.actual_scenario_end i t h β C.executes.1
  refine ⟨hsubjective.1, hsubjective.2.1, ?_, ?_⟩
  · rcases hsubjective.2.2.1 with hzero | himproves
    · exact Or.inl hzero
    · exact Or.inr (by
        rw [hprojection α, hprojection W.alpha_zero] at himproves
        exact himproves)
  · intro β hβ hbetter
    have hnot := hsubjective.2.2.2 β hβ
    rw [← hprojection β, ← hprojection α] at hbetter
    exact hnot hbetter

/-- A veridical appraisal rule is obtained when the model's explicit rule
selects the scenario embedding of the actual economy. Membership of that
embedded scenario in `MinPlausible` remains unnecessary. -/
theorem veridicalAppraisal_of_actual_scenario_selection
    (hselect : ∀ i t h α, W.mem_hist t h →
      M.appraisedEnd i t h α = M.scenarioEnd i α (M.actualScenario i t h)) :
    M.VeridicalAppraisal :=
  ⟨hselect⟩

end SubjectiveScenarioFrame

end Praxeology

