/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Catallactics
public import Praxeology.FiniteEconomy.ProgramActionFrame

/-!
# Matched exchange in the recursive physical ActionFrame

This witness executes one matched two-good exchange through a finite physical
program. Each agent's preference is an explicit ordinal ranking of the good
they seek. Preferences are not inferred from the transfer or its technology.
-/

@[expose] public section

namespace Praxeology
namespace ProgramExchangeWitness

abbrev Agent := Fin 2
abbrev Means := Fin 2
abbrev Operation := Unit
abbrev Service := Unit

def agent0 : Agent := 0
def agent1 : Agent := 1
def good0 : Means := 0
def good1 : Means := 1

def offer : EconomyAction Agent Means Operation :=
  .offer 0 1 1 1 1 0

def accept : EconomyAction Agent Means Operation :=
  .accept 1 0 1 1 1 0

def tradeProfile : ActionProfile (Agent := Agent) (Means := Means)
    (Operation := Operation) := fun actor => if actor = 0 then offer else accept

def operations : OperationSemantics Operation Means Service where
  input := fun _ _ => 0
  output := fun _ _ => 0
  service := fun _ _ => 0

def initialState : PhysicalState Agent Means Service where
  stock := fun actor good =>
    if actor = 0 then if good = 1 then 1 else 0
    else if good = 0 then 1 else 0
  services := fun _ _ => 0

def choices : FiniteChoiceStage Agent Means Operation :=
  FiniteChoiceStage.ofProfile tradeProfile {0, 1}
    (by
      intro actor hactor
      simp only [Finset.mem_insert, Finset.mem_singleton] at hactor
      rcases hactor with hactor | hactor
      · subst actor
        simp [tradeProfile, offer]
      · subst actor
        simp [tradeProfile, accept])
    (by
      intro actor
      fin_cases actor <;>
        simp [tradeProfile, offer, accept, EconomyAction.WellFormed])

def physicalStage : FinitePhysicalChoiceStage Agent Means Operation Service where
  choices := choices
  operations := operations
  before := initialState
  menu_affordable := by
    intro actor action haction good
    fin_cases actor
    · change action ∈ insert EconomyAction.idle
        ({tradeProfile 0} : Finset (EconomyAction Agent Means Operation)) at haction
      rcases Finset.mem_insert.mp haction with haction | haction
      · subst action
        simp [rawActionUse]
      · simp only [Finset.mem_singleton] at haction
        subst action
        fin_cases good <;>
          simp [rawActionUse, tradeProfile, offer, initialState]
    · change action ∈ insert EconomyAction.idle
        ({tradeProfile 1} : Finset (EconomyAction Agent Means Operation)) at haction
      rcases Finset.mem_insert.mp haction with haction | haction
      · subst action
        simp [rawActionUse]
      · simp only [Finset.mem_singleton] at haction
        subst action
        fin_cases good <;>
          simp [rawActionUse, tradeProfile, accept, initialState]

def selectedProfile : physicalStage.choices.Profile :=
  ⟨tradeProfile, by
    intro actor
    fin_cases actor
    · change offer ∈ insert EconomyAction.idle
        ({offer} : Finset (EconomyAction Agent Means Operation))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · change accept ∈ insert EconomyAction.idle
        ({accept} : Finset (EconomyAction Agent Means Operation))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

def terminalContinuation (profile : physicalStage.choices.Profile) :
    FinitePhysicalEconomyProgram Agent Means Operation Service 0
      (physicalStage.advance profile) := .halt

def program : FinitePhysicalEconomyProgram Agent Means Operation Service 1
    initialState := .decision (state := initialState) physicalStage terminalContinuation

theorem stable_operations : program.HasStableOperationSemantics operations := by
  simp [program, FinitePhysicalEconomyProgram.HasStableOperationSemantics,
    physicalStage, operations, terminalContinuation]

def tradeHistory : program.History := by
  change FiniteEconomyProgram.ProgramHistory
    (FiniteEconomyProgram.physicalDecision 0 physicalStage
      (fun profile => FinitePhysicalEconomyProgram.toFiniteEconomyProgram
        (terminalContinuation profile)))
  exact FiniteEconomyProgram.ProgramHistory.decision selectedProfile
    (FiniteEconomyProgram.ProgramHistory.halt :
      FiniteEconomyProgram.ProgramHistory
        (FinitePhysicalEconomyProgram.toFiniteEconomyProgram
          (terminalContinuation selectedProfile)))

def idleProfile : physicalStage.choices.Profile :=
  ⟨fun _ => .idle, choices.idle_mem⟩

def idleHistory : program.History := by
  change FiniteEconomyProgram.ProgramHistory
    (FiniteEconomyProgram.physicalDecision 0 physicalStage
      (fun profile => FinitePhysicalEconomyProgram.toFiniteEconomyProgram
        (terminalContinuation profile)))
  exact FiniteEconomyProgram.ProgramHistory.decision idleProfile
    (FiniteEconomyProgram.ProgramHistory.halt :
      FiniteEconomyProgram.ProgramHistory
        (FinitePhysicalEconomyProgram.toFiniteEconomyProgram
          (terminalContinuation idleProfile)))

def endScore (actor : Agent) : program.End → ℕ
  | .bundle bundle => bundle actor
  | .timed ending _ => endScore actor ending
  | .quantity good quantity => if good = actor then quantity else 0

theorem endScore_eq_requirement (actor : Agent) (ending : program.End) :
    endScore actor ending = finiteProgramEndRequirement ending actor := by
  induction ending with
  | bundle bundle => rfl
  | timed ending moment ih => exact ih
  | quantity good quantity =>
      simp [endScore, finiteProgramEndRequirement, eq_comm]

def valuedEnd (actor : Agent) (ending : program.End) : Prop :=
  0 < finiteProgramEndRequirement ending actor ∧
    ∀ good, good ≠ actor → finiteProgramEndRequirement ending good = 0

noncomputable def referenceHistoryAt (_actor : Agent) (moment : program.Moment) :
    program.History :=
  if moment = FiniteEconomyProgram.ProgramMoment.root then tradeHistory
  else Classical.choose (FiniteEconomyProgram.ProgramMoment.exists_history moment)

theorem referenceHistoryAt_mem (actor : Agent) (moment : program.Moment) :
    FiniteEconomyProgram.ProgramMoment.memHist program.toFiniteEconomyProgram moment
      (referenceHistoryAt actor moment) := by
  by_cases hroot : moment = FiniteEconomyProgram.ProgramMoment.root
  · subst moment
    exact FiniteEconomyProgram.ProgramMoment.root_memHist _
  · change FiniteEconomyProgram.ProgramMoment.memHist program.toFiniteEconomyProgram moment
      (if moment = FiniteEconomyProgram.ProgramMoment.root then tradeHistory
        else Classical.choose (FiniteEconomyProgram.ProgramMoment.exists_history moment))
    rw [ite_eq_right hroot]
    exact Classical.choose_spec
      (FiniteEconomyProgram.ProgramMoment.exists_history moment)

noncomputable def behavior : program.ActionFrameBehavior where
  referenceHistory := referenceHistoryAt
  referenceHistory_mem := referenceHistoryAt_mem
  selectedHistory := fun actor moment action history =>
    program.selectAt actor moment action history
  selectedHistory_mem := by
    intro actor moment action history hmem
    exact program.selectAt_memHist actor moment action history hmem
  selectedHistory_past := by
    intro actor moment action history hmem haction past hbefore other
    have hselectedMem := program.selectAt_memHist actor moment action history hmem
    exact FiniteEconomyProgram.ProgramHistory.enactedAt_eq_of_shared_future
      (program.selectAt actor moment action history) history past moment hbefore
      hselectedMem hmem other
  selectedHistory_action := by
    intro actor moment action history hmem haction
    exact program.selectAt_enacted actor moment action history hmem haction
  selectedHistory_other := by
    intro actor other moment action history hne hmem haction
    exact program.selectAt_other actor other moment action history hmem haction hne.symm
  selectedHistory_centered := by
    intro actor moment action history hmem haction henacted
    exact program.selectAt_centered actor moment action history hmem haction henacted
  evaluationHorizon := fun _ _ _ => .terminalSettlement
  valuedEnd := fun actor _ _ ending => valuedEnd actor ending
  valuedEnd_invariant := by
    intro actor moment h₁ h₂ ending hmem₁ hmem₂
    rfl
  preference := fun actor _ _ e₁ e₂ => endScore actor e₂ < endScore actor e₁
  preference_invariant := by
    intro actor moment h₁ h₂ hmem₁ hmem₂
    rfl
  preference_asymmetric := by
    intro actor moment history e₁ e₂ h₁ h₂
    exact Nat.lt_asymm h₁ h₂
  teleological_dominance_prefers := by
    intro actor moment history b₁ b₂ hdominates
    rcases hdominates with ⟨_h_all, ⟨ends, h_valued, h_attains, h_misses⟩⟩
    have h_attains₁ :
        ends.sum (fun ending => finiteProgramEndRequirement ending actor) ≤ b₁ actor :=
      h_attains actor
    have h_not_attains₂ :
        ¬ ends.sum (fun ending => finiteProgramEndRequirement ending actor) ≤ b₂ actor := by
      intro hsum
      apply h_misses
      intro good
      by_cases hgood : good = actor
      · subst good
        exact hsum
      · have hzero : ends.sum (fun ending =>
          finiteProgramEndRequirement ending good) = 0 :=
            Finset.sum_eq_zero (fun ending hending =>
              (h_valued ending hending).2 good hgood)
        simp [hzero]
    have hstrict : b₂ actor < b₁ actor :=
      lt_of_lt_of_le (Nat.lt_of_not_ge h_not_attains₂) h_attains₁
    change endScore actor (.bundle b₂) < endScore actor (.bundle b₁)
    simpa [endScore] using hstrict

@[instance_reducible] noncomputable def frame : ActionFrame :=
  program.toActionFrame operations stable_operations behavior

private theorem terminalState_eq_advance (history : program.History) :
    history.terminalState = physicalStage.advance history.rootProfile := by
  cases history with
  | decision profile tail => cases tail; rfl

private theorem terminalStock (history : program.History) (actor : Agent)
    (good : Means) :
    (program.stateAt history.terminalMoment).stock actor good =
      (physicalStage.advance history.rootProfile).stock actor good := by
  rw [program.stateAt_terminalMoment, terminalState_eq_advance]

private theorem horizonStock (actor : Agent) (action : EconomyAction Agent Means Operation)
    (history : program.History) (good : Means) :
    frame.omega actor (frame.ExpectedMaturation actor action
      FiniteEconomyProgram.ProgramMoment.root history) history good =
      (physicalStage.advance history.rootProfile).stock actor good := by
  change (program.stateAt
    (program.expectedMaturation behavior actor
      FiniteEconomyProgram.ProgramMoment.root action history)).stock actor good = _
  simpa [FinitePhysicalEconomyProgram.expectedMaturation, behavior,
    FinitePhysicalEconomyProgram.horizonMoment,
    FinitePhysicalEconomyProgram.terminalSettlementHorizon] using
      terminalStock history actor good

private theorem jointEndI_score (i j : Agent) (actionI actionJ :
    EconomyAction Agent Means Operation) (history : program.History) :
    endScore i (jointEndI (W := frame) i j FiniteEconomyProgram.ProgramMoment.root
      history actionI actionJ) =
      (physicalStage.advance
        (jointBranch (W := frame) i j FiniteEconomyProgram.ProgramMoment.root
          history actionI actionJ).rootProfile).stock i i := by
  change (program.stateAt
    (program.expectedMaturation behavior i FiniteEconomyProgram.ProgramMoment.root
      actionI (jointBranch (W := frame) i j FiniteEconomyProgram.ProgramMoment.root
        history actionI actionJ))).stock i i = _
  simpa [FinitePhysicalEconomyProgram.expectedMaturation, behavior,
    FinitePhysicalEconomyProgram.horizonMoment,
    FinitePhysicalEconomyProgram.terminalSettlementHorizon] using
      terminalStock (jointBranch (W := frame) i j
        FiniteEconomyProgram.ProgramMoment.root history actionI actionJ) i i

private theorem jointEndJ_score (i j : Agent) (actionI actionJ :
    EconomyAction Agent Means Operation) (history : program.History) :
    endScore j (jointEndJ (W := frame) i j FiniteEconomyProgram.ProgramMoment.root
      history actionI actionJ) =
      (physicalStage.advance
        (jointBranch (W := frame) i j FiniteEconomyProgram.ProgramMoment.root
          history actionI actionJ).rootProfile).stock j j := by
  change (program.stateAt
    (program.expectedMaturation behavior j FiniteEconomyProgram.ProgramMoment.root
      actionJ (jointBranch (W := frame) i j FiniteEconomyProgram.ProgramMoment.root
        history actionI actionJ))).stock j j = _
  simpa [FinitePhysicalEconomyProgram.expectedMaturation, behavior,
    FinitePhysicalEconomyProgram.horizonMoment,
    FinitePhysicalEconomyProgram.terminalSettlementHorizon] using
      terminalStock (jointBranch (W := frame) i j
        FiniteEconomyProgram.ProgramMoment.root history actionI actionJ) j j

private theorem frame_preference (actor : Agent) (ending₁ ending₂ : program.End) :
    frame.Preference actor FiniteEconomyProgram.ProgramMoment.root tradeHistory
      ending₁ ending₂ = (endScore actor ending₂ < endScore actor ending₁) := by
  rfl

private theorem matchedTrade_gains (profile : physicalStage.choices.Profile)
    (h0 : profile.1 0 = offer) (h1 : profile.1 1 = accept) :
    (physicalStage.advance profile).stock agent0 good0 = 1 ∧
      (physicalStage.advance profile).stock agent1 good1 = 1 := by
  have hbalance₀ := physicalStage.advance_balance profile agent0 good0
  have hbalance₁ := physicalStage.advance_balance profile agent1 good1
  have huse₀ : effectiveUse operations profile.1 agent0 good0 = 0 := by
    norm_num [effectiveUse, h0, h1, offer, accept, agent0, agent1, good0, good1]
  have hyield₀ : effectiveYield operations profile.1 agent0 good0 = 1 := by
    norm_num [effectiveYield, h0, h1, offer, accept, agent0, agent1, good0, good1]
  have huse₁ : effectiveUse operations profile.1 agent1 good1 = 0 := by
    norm_num [effectiveUse, h0, h1, offer, accept, agent0, agent1, good0, good1]
  have hyield₁ : effectiveYield operations profile.1 agent1 good1 = 1 := by
    norm_num [effectiveYield, h0, h1, offer, accept, agent0, agent1, good0, good1]
  change (physicalStage.advance profile).stock agent0 good0 +
      effectiveUse operations profile.1 agent0 good0 =
    initialState.stock agent0 good0 +
      effectiveYield operations profile.1 agent0 good0 at hbalance₀
  change (physicalStage.advance profile).stock agent1 good1 +
      effectiveUse operations profile.1 agent1 good1 =
    initialState.stock agent1 good1 +
      effectiveYield operations profile.1 agent1 good1 at hbalance₁
  rw [huse₀, hyield₀] at hbalance₀
  rw [huse₁, hyield₁] at hbalance₁
  have hinitial₀ : initialState.stock agent0 good0 = 0 := by rfl
  have hinitial₁ : initialState.stock agent1 good1 = 0 := by rfl
  rw [hinitial₀] at hbalance₀
  rw [hinitial₁] at hbalance₁
  constructor <;> omega

private theorem idleAgent_stock_unchanged (profile : physicalStage.choices.Profile)
    (actor : Agent) (haction : profile.1 actor = .idle) (good : Means) :
    (physicalStage.advance profile).stock actor good = initialState.stock actor good := by
  have hbalance := physicalStage.advance_balance profile actor good
  have huse : effectiveUse operations profile.1 actor good = 0 := by
    simp [effectiveUse, haction]
  have hyield : effectiveYield operations profile.1 actor good = 0 := by
    simp [effectiveYield, haction]
  change (physicalStage.advance profile).stock actor good +
      effectiveUse operations profile.1 actor good =
    initialState.stock actor good +
      effectiveYield operations profile.1 actor good at hbalance
  rw [huse, hyield] at hbalance
  omega

private theorem frame_enacted_root_eq_profile (history : program.History)
    (actor : Agent) :
    frame.enacted actor FiniteEconomyProgram.ProgramMoment.root history =
      history.rootProfile.1 actor := by
  cases history with
  | decision profile tail => cases tail; rfl

private theorem jointBranch_root_actions (actionI actionJ :
    EconomyAction Agent Means Operation)
    (feasibleI : actionI ∈ frame.A_feas agent0
      FiniteEconomyProgram.ProgramMoment.root tradeHistory)
    (feasibleJ : actionJ ∈ frame.A_feas agent1
      FiniteEconomyProgram.ProgramMoment.root
        (frame.sigma agent0 FiniteEconomyProgram.ProgramMoment.root actionI tradeHistory)) :
    (jointBranch (W := frame) agent0 agent1 FiniteEconomyProgram.ProgramMoment.root
      tradeHistory actionI actionJ).rootProfile.1 agent0 = actionI ∧
    (jointBranch (W := frame) agent0 agent1 FiniteEconomyProgram.ProgramMoment.root
      tradeHistory actionI actionJ).rootProfile.1 agent1 = actionJ := by
  have hreal := jointBranch_realizes_pair (W := frame) agent0 agent1
    FiniteEconomyProgram.ProgramMoment.root tradeHistory actionI actionJ
    (by decide) (FiniteEconomyProgram.ProgramMoment.root_memHist tradeHistory)
    feasibleI feasibleJ
  have hprofile0 := frame_enacted_root_eq_profile
    (jointBranch (W := frame) agent0 agent1 FiniteEconomyProgram.ProgramMoment.root
      tradeHistory actionI actionJ) agent0
  have hprofile1 := frame_enacted_root_eq_profile
    (jointBranch (W := frame) agent0 agent1 FiniteEconomyProgram.ProgramMoment.root
      tradeHistory actionI actionJ) agent1
  constructor
  · rw [← hprofile0]
    exact hreal.2.1
  · rw [← hprofile1]
    exact hreal.2.2

private theorem rootTradeActions_feasible :
    offer ∈ frame.A_feas agent0 FiniteEconomyProgram.ProgramMoment.root tradeHistory ∧
    accept ∈ frame.A_feas agent1 FiniteEconomyProgram.ProgramMoment.root tradeHistory := by
  have hroot : frame.mem_hist FiniteEconomyProgram.ProgramMoment.root tradeHistory :=
    FiniteEconomyProgram.ProgramMoment.root_memHist tradeHistory
  have h0 : frame.enacted agent0 FiniteEconomyProgram.ProgramMoment.root
      tradeHistory = offer := rfl
  have h1 : frame.enacted agent1 FiniteEconomyProgram.ProgramMoment.root
      tradeHistory = accept := rfl
  constructor
  · rw [← h0]
    exact frame.enacted_in_A_feas agent0 FiniteEconomyProgram.ProgramMoment.root
      tradeHistory hroot
  · rw [← h1]
    exact frame.enacted_in_A_feas agent1 FiniteEconomyProgram.ProgramMoment.root
      tradeHistory hroot

/-- The recursive physical compiler proves a concrete matched exchange
voluntary when the supplied ordinal rankings value the good each trader
receives. The transfer and terminal inventories are derived from the shared
physical interpreter. -/
theorem recursive_compiled_exchange_is_voluntary :
    IsVoluntaryExchange (W := frame) agent0 agent1
      FiniteEconomyProgram.ProgramMoment.root tradeHistory offer accept := by
  have hroot : frame.mem_hist FiniteEconomyProgram.ProgramMoment.root tradeHistory :=
    FiniteEconomyProgram.ProgramMoment.root_memHist tradeHistory
  have htradeFeasible := rootTradeActions_feasible
  have hcenterOffer : frame.sigma agent0 FiniteEconomyProgram.ProgramMoment.root
      offer tradeHistory = tradeHistory :=
    frame.sigma_centering agent0 FiniteEconomyProgram.ProgramMoment.root tradeHistory hroot rfl
  have hactual := jointBranch_root_actions offer accept htradeFeasible.1
    (by rw [hcenterOffer]; exact htradeFeasible.2)
  have hzeroI := frame.alpha_zero_feasible agent0
    FiniteEconomyProgram.ProgramMoment.root tradeHistory
  have hzeroI_branch := frame.sigma_realization agent0
    FiniteEconomyProgram.ProgramMoment.root tradeHistory tradeHistory
    hroot hzeroI hroot
  have hzeroJ := frame.alpha_zero_feasible agent1
    FiniteEconomyProgram.ProgramMoment.root
    (frame.sigma agent0 FiniteEconomyProgram.ProgramMoment.root frame.alpha_zero tradeHistory)
  have hbaseline := jointBranch_root_actions frame.alpha_zero frame.alpha_zero
    hzeroI (by exact hzeroJ)
  have hofferBranch := jointBranch_root_actions offer frame.alpha_zero
    htradeFeasible.1
    (frame.alpha_zero_feasible agent1 FiniteEconomyProgram.ProgramMoment.root
      (frame.sigma agent0 FiniteEconomyProgram.ProgramMoment.root offer tradeHistory))
  have hacceptAtIdle : accept ∈ frame.A_feas agent1
      FiniteEconomyProgram.ProgramMoment.root
      (frame.sigma agent0 FiniteEconomyProgram.ProgramMoment.root
        frame.alpha_zero tradeHistory) := by
    rw [frame.A_feas_bundle_invariant agent1 FiniteEconomyProgram.ProgramMoment.root
      hzeroI_branch.1 hroot]
    exact htradeFeasible.2
  have hacceptBranch := jointBranch_root_actions frame.alpha_zero accept
    hzeroI hacceptAtIdle
  refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
  · intro hinvasive
    rcases hinvasive with ⟨good, hless⟩
    let branch := jointBranch (W := frame) agent0 agent1
      FiniteEconomyProgram.ProgramMoment.root tradeHistory offer frame.alpha_zero
    have hunchanged := idleAgent_stock_unchanged branch.rootProfile agent1
      (by rw [hofferBranch.2]; rfl) good
    have hrootStock : frame.omega agent1 FiniteEconomyProgram.ProgramMoment.root
        tradeHistory good = initialState.stock agent1 good := rfl
    change frame.omega agent1 (frame.ExpectedMaturation agent1 frame.alpha_zero
        FiniteEconomyProgram.ProgramMoment.root branch) branch good <
      frame.omega agent1 FiniteEconomyProgram.ProgramMoment.root tradeHistory good at hless
    rw [horizonStock, hrootStock] at hless
    rw [hunchanged] at hless
    exact Nat.lt_irrefl _ hless
  · intro hinvasive
    rcases hinvasive with ⟨good, hless⟩
    let branch := jointBranch (W := frame) agent0 agent1
      FiniteEconomyProgram.ProgramMoment.root tradeHistory frame.alpha_zero accept
    have hunchanged := idleAgent_stock_unchanged branch.rootProfile agent0
      (by rw [hacceptBranch.1]; rfl) good
    have hrootStock : frame.omega agent0 FiniteEconomyProgram.ProgramMoment.root
        tradeHistory good = initialState.stock agent0 good := rfl
    change frame.omega agent0 (frame.ExpectedMaturation agent0 frame.alpha_zero
        FiniteEconomyProgram.ProgramMoment.root branch) branch good <
      frame.omega agent0 FiniteEconomyProgram.ProgramMoment.root tradeHistory good at hless
    rw [horizonStock, hrootStock] at hless
    rw [hunchanged] at hless
    exact Nat.lt_irrefl _ hless
  · have hscore : endScore agent0
        (jointEndI (W := frame) agent0 agent1
          FiniteEconomyProgram.ProgramMoment.root tradeHistory
          frame.alpha_zero frame.alpha_zero) <
        endScore agent0
          (jointEndI (W := frame) agent0 agent1
            FiniteEconomyProgram.ProgramMoment.root tradeHistory offer accept) := by
      rw [jointEndI_score agent0 agent1 frame.alpha_zero frame.alpha_zero tradeHistory,
        jointEndI_score agent0 agent1 offer accept tradeHistory]
      have hzero := idleAgent_stock_unchanged
        (jointBranch (W := frame) agent0 agent1 FiniteEconomyProgram.ProgramMoment.root
          tradeHistory frame.alpha_zero frame.alpha_zero).rootProfile
        agent0 (by rw [hbaseline.1]; rfl) good0
      have hzero' : (physicalStage.advance
          ((jointBranch (W := frame) agent0 agent1
            FiniteEconomyProgram.ProgramMoment.root tradeHistory
            frame.alpha_zero frame.alpha_zero).rootProfile)).stock agent0 agent0 =
          initialState.stock agent0 agent0 := by
        simpa [agent0, good0] using hzero
      rw [hzero']
      have hinitial : initialState.stock agent0 agent0 = 0 := by
        norm_num [initialState, agent0]
      rw [hinitial]
      have hgain := matchedTrade_gains
        (jointBranch (W := frame) agent0 agent1 FiniteEconomyProgram.ProgramMoment.root
          tradeHistory offer accept).rootProfile hactual.1 hactual.2
      have hgain₀ : (physicalStage.advance
          ((jointBranch (W := frame) agent0 agent1
            FiniteEconomyProgram.ProgramMoment.root tradeHistory offer accept).rootProfile)).stock
          agent0 agent0 = 1 := by
        simpa [agent0, good0] using hgain.1
      rw [hgain₀]
      decide
    rw [frame_preference]
    exact hscore
  · have hscore : endScore agent1
        (jointEndJ (W := frame) agent0 agent1
          FiniteEconomyProgram.ProgramMoment.root tradeHistory
          frame.alpha_zero frame.alpha_zero) <
        endScore agent1
          (jointEndJ (W := frame) agent0 agent1
            FiniteEconomyProgram.ProgramMoment.root tradeHistory offer accept) := by
      rw [jointEndJ_score agent0 agent1 frame.alpha_zero frame.alpha_zero tradeHistory,
        jointEndJ_score agent0 agent1 offer accept tradeHistory]
      have hzero := idleAgent_stock_unchanged
        (jointBranch (W := frame) agent0 agent1 FiniteEconomyProgram.ProgramMoment.root
          tradeHistory frame.alpha_zero frame.alpha_zero).rootProfile
        agent1 (by rw [hbaseline.2]; rfl) good1
      have hzero' : (physicalStage.advance
          ((jointBranch (W := frame) agent0 agent1
            FiniteEconomyProgram.ProgramMoment.root tradeHistory
            frame.alpha_zero frame.alpha_zero).rootProfile)).stock agent1 agent1 =
          initialState.stock agent1 agent1 := by
        simpa [agent1, good1] using hzero
      rw [hzero']
      have hinitial : initialState.stock agent1 agent1 = 0 := by
        norm_num [initialState, agent1]
      rw [hinitial]
      have hgain := matchedTrade_gains
        (jointBranch (W := frame) agent0 agent1 FiniteEconomyProgram.ProgramMoment.root
          tradeHistory offer accept).rootProfile hactual.1 hactual.2
      have hgain₁ : (physicalStage.advance
          ((jointBranch (W := frame) agent0 agent1
            FiniteEconomyProgram.ProgramMoment.root tradeHistory offer accept).rootProfile)).stock
          agent1 agent1 = 1 := by
        simpa [agent1, good1] using hgain.2
      rw [hgain₁]
      decide
    rw [frame_preference]
    exact hscore

end ProgramExchangeWitness
end Praxeology

end
