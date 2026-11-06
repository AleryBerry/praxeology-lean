/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.ProgramActionFrame

/-!
# A small executed-operation witness for the recursive frame adapter

One agent starts with one unit of a means and can either idle or use an
operation that consumes one unit and yields two. The other agent only idles.
The example instantiates the recursive physical program and its ActionFrame
adapter. Its preference ranking is an explicit behavioral premise; it is not
inferred from the production technology.
-/

@[expose] public section

namespace Praxeology
namespace ProgramActionFrameWitness

abbrev Agent := Fin 2
abbrev Means := Fin 1
abbrev Operation := Unit
abbrev Service := Unit

def operations : OperationSemantics Operation Means Service where
  input := fun _ _ => 1
  output := fun _ _ => 2
  service := fun _ _ => 0

def initialState : PhysicalState Agent Means Service where
  stock := fun actor _ => if actor = 0 then 1 else 0
  services := fun _ _ => 0

def selectedProfile : ActionProfile (Agent := Agent) (Means := Means)
    (Operation := Operation) := fun actor =>
  if actor = 0 then .operate () else .idle

def choices : FiniteChoiceStage Agent Means Operation :=
  { menu := fun actor =>
      if actor = 0 then insert .idle {.operate ()} else {.idle}
    idle_mem := by
      intro actor
      by_cases hactor : actor = 0 <;> simp [hactor]
    activeAgents := {0}
    active_iff := by
      intro actor
      fin_cases actor <;> simp
    maxActiveAgents := 1
    activity_bound := by simp
    menu_wellFormed := by
      intro actor action haction
      fin_cases actor
      · change action ∈ insert EconomyAction.idle
          ({EconomyAction.operate ()} : Finset (EconomyAction Agent Means Operation))
          at haction
        rcases Finset.mem_insert.mp haction with haction | haction
        · subst action
          simp [EconomyAction.WellFormed]
        · have haction : action = EconomyAction.operate () :=
            Finset.mem_singleton.mp haction
          subst action
          simp [EconomyAction.WellFormed]
      · change action ∈
          ({EconomyAction.idle} : Finset (EconomyAction Agent Means Operation)) at haction
        have haction : action = EconomyAction.idle := Finset.mem_singleton.mp haction
        subst action
        simp [EconomyAction.WellFormed] }

def physicalStage : FinitePhysicalChoiceStage Agent Means Operation Service where
  choices := choices
  operations := operations
  before := initialState
  menu_affordable := by
    intro actor action haction m
    fin_cases actor
    · fin_cases m
      change action ∈ insert EconomyAction.idle
        ({EconomyAction.operate ()} : Finset (EconomyAction Agent Means Operation)) at haction
      rcases Finset.mem_insert.mp haction with haction | haction
      · subst action
        simp [rawActionUse]
      · have haction : action = EconomyAction.operate () :=
          Finset.mem_singleton.mp haction
        subst action
        simp [rawActionUse, operations, initialState]
    · fin_cases m
      change action ∈
        ({EconomyAction.idle} : Finset (EconomyAction Agent Means Operation)) at haction
      have haction : action = EconomyAction.idle := Finset.mem_singleton.mp haction
      subst action
      simp [rawActionUse]

def terminalContinuation (profile : physicalStage.choices.Profile) :
    FinitePhysicalEconomyProgram Agent Means Operation Service 0
      (physicalStage.advance profile) :=
  .halt

def program : FinitePhysicalEconomyProgram Agent Means Operation Service 1 initialState :=
  .decision (state := initialState) physicalStage terminalContinuation

theorem stable_operations : program.HasStableOperationSemantics operations := by
  simp [program, FinitePhysicalEconomyProgram.HasStableOperationSemantics,
    physicalStage, operations, terminalContinuation]

def operatedProfile : physicalStage.choices.Profile :=
  ⟨selectedProfile, by
    intro actor
    fin_cases actor
    · change EconomyAction.operate () ∈ choices.menu 0
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · change EconomyAction.idle ∈
        ({EconomyAction.idle} : Finset (EconomyAction Agent Means Operation))
      exact Finset.mem_singleton_self _
  ⟩

/-- A second one-step stage with the same menu and technology, typed to its
actual pre-state and carrying an explicit affordability proof. -/
def delayedSecondStage (before : PhysicalState Agent Means Service)
    (actor0_funded : 1 ≤ before.stock 0 0) :
    FinitePhysicalChoiceStage Agent Means Operation Service where
  choices := choices
  operations := operations
  before := before
  menu_affordable := by
    intro actor action hmenu
    unfold actionAffordable
    intro means
    fin_cases actor
    · change action ∈ insert EconomyAction.idle
        ({EconomyAction.operate ()} : Finset (EconomyAction Agent Means Operation))
        at hmenu
      rcases Finset.mem_insert.mp hmenu with hidle | hoperate
      · subst action
        simp [rawActionUse]
      · have haction : action = EconomyAction.operate () :=
          Finset.mem_singleton.mp hoperate
        subst action
        fin_cases means
        simpa [rawActionUse, operations] using actor0_funded
    · change action ∈
        ({EconomyAction.idle} : Finset (EconomyAction Agent Means Operation))
        at hmenu
      have haction : action = EconomyAction.idle := Finset.mem_singleton.mp hmenu
      subst action
      simp [rawActionUse]

theorem firstStage_funds_delayed_stage (profile : physicalStage.choices.Profile) :
    1 ≤ (physicalStage.advance profile).stock 0 0 := by
  have hbalance := physicalStage.advance_balance profile 0 0
  have hmenu : profile.1 0 ∈ choices.menu 0 := profile.2 0
  change profile.1 0 ∈ insert EconomyAction.idle
    ({EconomyAction.operate ()} : Finset (EconomyAction Agent Means Operation)) at hmenu
  rcases Finset.mem_insert.mp hmenu with hidle | hoperate
  · have haction : profile.1 0 = EconomyAction.idle := hidle
    have huse : effectiveUse physicalStage.operations profile.1 0 0 = 0 := by
      simp [effectiveUse, haction]
    have hyield : effectiveYield physicalStage.operations profile.1 0 0 = 0 := by
      simp [effectiveYield, haction]
    rw [huse, hyield] at hbalance
    have hbefore : physicalStage.before.stock 0 0 = 1 := rfl
    rw [hbefore] at hbalance
    omega
  · have haction : profile.1 0 = EconomyAction.operate () :=
      Finset.mem_singleton.mp hoperate
    have huse : effectiveUse physicalStage.operations profile.1 0 0 = 1 := by
      simp [effectiveUse, haction, physicalStage, operations]
    have hyield : effectiveYield physicalStage.operations profile.1 0 0 = 2 := by
      simp [effectiveYield, haction, physicalStage, operations]
    rw [huse, hyield] at hbalance
    have hbefore : physicalStage.before.stock 0 0 = 1 := rfl
    rw [hbefore] at hbalance
    omega

/-- Two successive production decisions make the terminal inventory differ
from the inventory immediately after the first decision. -/
def delayedContinuation (profile : physicalStage.choices.Profile) :
    FinitePhysicalEconomyProgram Agent Means Operation Service 1
      (physicalStage.advance profile) :=
  FinitePhysicalEconomyProgram.decision
    (state := physicalStage.advance profile)
    (delayedSecondStage (physicalStage.advance profile)
      (firstStage_funds_delayed_stage profile)) (fun _ => .halt)

def delayedProgram : FinitePhysicalEconomyProgram Agent Means Operation Service 2
    initialState :=
  FinitePhysicalEconomyProgram.decision (state := initialState)
    physicalStage delayedContinuation

theorem delayedProgram_stable_operations :
    delayedProgram.HasStableOperationSemantics operations := by
  change physicalStage.operations = operations ∧
    ∀ profile, (delayedContinuation profile).HasStableOperationSemantics operations
  constructor
  · rfl
  · intro profile
    change (delayedSecondStage (physicalStage.advance profile)
        (firstStage_funds_delayed_stage profile)).operations = operations ∧
      ∀ secondProfile,
        FinitePhysicalEconomyProgram.HasStableOperationSemantics
          (FinitePhysicalEconomyProgram.halt :
            FinitePhysicalEconomyProgram Agent Means Operation Service 0
              ((delayedSecondStage (physicalStage.advance profile)
                (firstStage_funds_delayed_stage profile)).advance secondProfile))
          operations
    exact ⟨rfl, by intro secondProfile; trivial⟩

def idleProfile : physicalStage.choices.Profile :=
  ⟨fun _ => EconomyAction.idle, choices.idle_mem⟩

def operatedThenOperatedHistory : delayedProgram.History :=
  .decision operatedProfile (.decision operatedProfile .halt)

def idledThenOperatedHistory : delayedProgram.History :=
  .decision idleProfile (.decision operatedProfile .halt)

def operatedDelayedTail :
    FiniteEconomyProgram.ProgramHistory
      (delayedContinuation operatedProfile).toFiniteEconomyProgram :=
  .decision operatedProfile .halt

def idledDelayedTail :
    FiniteEconomyProgram.ProgramHistory
      (delayedContinuation idleProfile).toFiniteEconomyProgram :=
  .decision operatedProfile .halt

def operatedFirstSuccessor : delayedProgram.Moment :=
  FiniteEconomyProgram.ProgramMoment.afterProfile operatedProfile
    FiniteEconomyProgram.ProgramMoment.root

def operatedTerminalMoment : delayedProgram.Moment :=
  operatedThenOperatedHistory.terminalMoment

def idledFirstSuccessor : delayedProgram.Moment :=
  FiniteEconomyProgram.ProgramMoment.afterProfile idleProfile
    FiniteEconomyProgram.ProgramMoment.root

def idledTerminalMoment : delayedProgram.Moment :=
  idledThenOperatedHistory.terminalMoment

theorem operated_branch_horizon_points :
    delayedProgram.horizonMoment .immediateSuccessor
        FiniteEconomyProgram.ProgramMoment.root operatedThenOperatedHistory =
      operatedFirstSuccessor ∧
    delayedProgram.horizonMoment .terminalSettlement
        FiniteEconomyProgram.ProgramMoment.root operatedThenOperatedHistory =
      operatedTerminalMoment := by
  constructor
  · change FiniteEconomyProgram.ProgramMoment.root.maturationAt
      (FiniteEconomyProgram.ProgramHistory.decision operatedProfile operatedDelayedTail) =
      operatedFirstSuccessor
    rw [FiniteEconomyProgram.ProgramMoment.maturationAt]
    rw [FiniteEconomyProgram.ProgramMoment.nextOnHistory_root]
    rfl
  · rfl

theorem idled_branch_horizon_points :
    delayedProgram.horizonMoment .immediateSuccessor
        FiniteEconomyProgram.ProgramMoment.root idledThenOperatedHistory =
      idledFirstSuccessor ∧
    delayedProgram.horizonMoment .terminalSettlement
        FiniteEconomyProgram.ProgramMoment.root idledThenOperatedHistory =
      idledTerminalMoment := by
  constructor
  · change FiniteEconomyProgram.ProgramMoment.root.maturationAt
      (FiniteEconomyProgram.ProgramHistory.decision idleProfile idledDelayedTail) =
      idledFirstSuccessor
    rw [FiniteEconomyProgram.ProgramMoment.maturationAt]
    rw [FiniteEconomyProgram.ProgramMoment.nextOnHistory_root]
    rfl
  · rfl

/-- The immediate outcome and terminal inventory differ on both delayed
branches. This records only interpreter-derived physical holdings; the longer
horizon supplies no preference, purposeful-choice, or regret premise. -/
theorem terminal_node_horizons_stay_at_terminal_moment :
    delayedProgram.horizonMoment .immediateSuccessor
        operatedThenOperatedHistory.terminalMoment
        operatedThenOperatedHistory = operatedTerminalMoment ∧
    delayedProgram.horizonMoment .terminalSettlement
        operatedThenOperatedHistory.terminalMoment operatedThenOperatedHistory =
      operatedTerminalMoment := by
  have hterminal :
      operatedThenOperatedHistory.terminalMoment.maturationAt
          operatedThenOperatedHistory =
        operatedThenOperatedHistory.terminalMoment := by
    have hfuture :=
      FiniteEconomyProgram.ProgramMoment.maturationAt_memHist_future
        operatedThenOperatedHistory.terminalMoment operatedThenOperatedHistory
        operatedThenOperatedHistory.terminalMoment_memHist
    rcases hfuture.2 with heq | hprecedence
    · exact heq.symm
    · exact (operatedThenOperatedHistory.terminalMoment_is_last
        (operatedThenOperatedHistory.terminalMoment.maturationAt
          operatedThenOperatedHistory) hprecedence).elim
  constructor
  · change operatedTerminalMoment.maturationAt operatedThenOperatedHistory =
      operatedThenOperatedHistory.terminalMoment
    exact hterminal
  · rfl

def programEndScore : program.End → ℕ
  | .bundle bundle => bundle 0
  | .timed ending _ => programEndScore ending
  | .quantity means quantity => if means = 0 then quantity else 0

theorem programEndScore_eq_requirement (ending : program.End) :
    programEndScore ending = finiteProgramEndRequirement ending 0 := by
  induction ending with
  | bundle bundle => rfl
  | timed ending moment ih => exact ih
  | quantity means quantity =>
      simp [programEndScore, finiteProgramEndRequirement, eq_comm]

def valuedProgramEnd (ending : program.End) : Prop := 0 < programEndScore ending

noncomputable def referenceHistoryAt (_actor : Agent) (moment : program.Moment) :
    program.History :=
  if moment = FiniteEconomyProgram.ProgramMoment.root then program.allIdleHistory
  else Classical.choose (FiniteEconomyProgram.ProgramMoment.exists_history moment)

theorem referenceHistoryAt_mem (actor : Agent) (moment : program.Moment) :
    FiniteEconomyProgram.ProgramMoment.memHist program.toFiniteEconomyProgram moment
      (referenceHistoryAt actor moment) := by
  by_cases hroot : moment = FiniteEconomyProgram.ProgramMoment.root
  · subst moment
    exact FiniteEconomyProgram.ProgramMoment.root_memHist _
  · change FiniteEconomyProgram.ProgramMoment.memHist program.toFiniteEconomyProgram moment
      (if moment = FiniteEconomyProgram.ProgramMoment.root then program.allIdleHistory
        else Classical.choose (FiniteEconomyProgram.ProgramMoment.exists_history moment))
    rw [ite_eq_right hroot]
    exact Classical.choose_spec
      (FiniteEconomyProgram.ProgramMoment.exists_history moment)

noncomputable def behavior : program.ActionFrameBehavior where
  referenceHistory := referenceHistoryAt
  referenceHistory_mem := by
    intro actor moment
    exact referenceHistoryAt_mem actor moment
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
  valuedEnd := fun _ _ _ ending => valuedProgramEnd ending
  valuedEnd_invariant := by
    intro actor moment h₁ h₂ ending hmem₁ hmem₂
    rfl
  preference := fun _ _ _ e₁ e₂ => programEndScore e₂ < programEndScore e₁
  preference_invariant := by
    intro actor moment h₁ h₂ hmem₁ hmem₂
    rfl
  preference_asymmetric := by
    intro actor moment history e₁ e₂ h₁ h₂
    exact Nat.lt_asymm h₁ h₂
  teleological_dominance_prefers := by
    intro actor moment history b₁ b₂ hdominates
    rcases hdominates with ⟨_h_all, ⟨ends, h_valued, h_attains, h_misses⟩⟩
    have h_requirements_positive : ∀ ending ∈ ends,
        0 < finiteProgramEndRequirement ending 0 := by
      intro ending hending
      rw [← programEndScore_eq_requirement]
      exact h_valued ending hending
    have h_attains₁ :
        ends.sum (fun ending => finiteProgramEndRequirement ending 0) ≤ b₁ 0 :=
      h_attains 0
    have h_not_attains₂ :
        ¬ ends.sum (fun ending => finiteProgramEndRequirement ending 0) ≤ b₂ 0 := by
      intro hsum
      apply h_misses
      intro means
      fin_cases means
      exact hsum
    have h_strict : b₂ 0 < b₁ 0 := by
      have h_lower : b₂ 0 < ends.sum (fun ending =>
          finiteProgramEndRequirement ending 0) := by omega
      exact lt_of_lt_of_le h_lower h_attains₁
    change programEndScore (.bundle b₂) < programEndScore (.bundle b₁)
    simpa [programEndScore] using h_strict

@[instance_reducible] noncomputable def frame : ActionFrame :=
  program.toActionFrame operations stable_operations behavior

def operatedSuccessorMoment : program.Moment :=
  FiniteEconomyProgram.ProgramMoment.afterProfile operatedProfile
    FiniteEconomyProgram.ProgramMoment.root

def operatedHistory : program.History := by
  change FiniteEconomyProgram.ProgramHistory
    (FiniteEconomyProgram.physicalDecision 0 physicalStage
      (fun profile => FinitePhysicalEconomyProgram.toFiniteEconomyProgram
        (terminalContinuation profile)))
  exact FiniteEconomyProgram.ProgramHistory.decision operatedProfile
    (FiniteEconomyProgram.ProgramHistory.halt :
      FiniteEconomyProgram.ProgramHistory
        (FinitePhysicalEconomyProgram.toFiniteEconomyProgram
          (terminalContinuation operatedProfile)))

theorem operated_successor_on_history :
    FiniteEconomyProgram.ProgramMoment.memHist program.toFiniteEconomyProgram
      operatedSuccessorMoment operatedHistory := by
  change ∃ hprofile : operatedProfile = operatedProfile,
      FiniteEconomyProgram.ProgramMoment.memHist
        (FinitePhysicalEconomyProgram.toFiniteEconomyProgram
          (terminalContinuation operatedProfile))
        FiniteEconomyProgram.ProgramMoment.root
        (hprofile ▸ (FiniteEconomyProgram.ProgramHistory.halt :
          FiniteEconomyProgram.ProgramHistory
            (FinitePhysicalEconomyProgram.toFiniteEconomyProgram
              (terminalContinuation operatedProfile))))
  exact ⟨rfl, FiniteEconomyProgram.ProgramMoment.root_memHist _⟩

theorem operated_branch_has_two_units :
    (physicalStage.advance operatedProfile).stock (0 : Agent) (0 : Means) = 2 := by
  have hbalance := physicalStage.advance_balance operatedProfile (0 : Agent) (0 : Means)
  have hprofile : operatedProfile.1 0 = EconomyAction.operate () := rfl
  have huse : effectiveUse operations operatedProfile.1 0 0 = 1 := by
    simp [effectiveUse, operations, hprofile]
  have hyield : effectiveYield operations operatedProfile.1 0 0 = 2 := by
    simp [effectiveYield, operations, hprofile]
  have hbefore : initialState.stock 0 0 = 1 := rfl
  change (physicalStage.advance operatedProfile).stock 0 0 +
      effectiveUse operations operatedProfile.1 0 0 =
    initialState.stock 0 0 + effectiveYield operations operatedProfile.1 0 0 at hbalance
  rw [huse, hyield, hbefore] at hbalance
  omega

/-- The declared immediate horizon sees the first transition, while terminal
settlement includes the delayed second transition on both operated and idle
branches. These are physical outcomes only; the difference itself implies no
preference, purposeful choice, or contextual regret. -/
theorem delayed_action_horizons_have_distinct_inventories :
    (delayedProgram.stateAt operatedFirstSuccessor).stock 0 0 = 2 ∧
    (delayedProgram.stateAt operatedTerminalMoment).stock 0 0 = 3 ∧
    (delayedProgram.stateAt idledFirstSuccessor).stock 0 0 = 1 ∧
    (delayedProgram.stateAt idledTerminalMoment).stock 0 0 = 2 := by
  have hoperatedFirst :
      (delayedProgram.stateAt operatedFirstSuccessor).stock 0 0 = 2 := by
    change (physicalStage.advance operatedProfile).stock 0 0 = 2
    exact operated_branch_has_two_units
  have hidledFirst :
      (delayedProgram.stateAt idledFirstSuccessor).stock 0 0 = 1 := by
    change (physicalStage.advance idleProfile).stock 0 0 = 1
    have hbalance := physicalStage.advance_balance idleProfile 0 0
    have huse : effectiveUse operations idleProfile.1 0 0 = 0 := by
      simp [effectiveUse, idleProfile]
    have hyield : effectiveYield operations idleProfile.1 0 0 = 0 := by
      simp [effectiveYield, idleProfile]
    have hbefore : physicalStage.before.stock 0 0 = 1 := rfl
    change (physicalStage.advance idleProfile).stock 0 0 +
        effectiveUse operations idleProfile.1 0 0 =
      physicalStage.before.stock 0 0 +
        effectiveYield operations idleProfile.1 0 0 at hbalance
    rw [huse, hyield, hbefore] at hbalance
    omega
  have hoperatedTerminal :
      (delayedProgram.stateAt operatedTerminalMoment).stock 0 0 = 3 := by
    let stage := delayedSecondStage (physicalStage.advance operatedProfile)
      (firstStage_funds_delayed_stage operatedProfile)
    change (stage.advance operatedProfile).stock 0 0 = 3
    have hbalance := stage.advance_balance operatedProfile 0 0
    have huse : effectiveUse operations operatedProfile.1 0 0 = 1 := by
      simp [effectiveUse, operatedProfile, selectedProfile, operations]
    have hyield : effectiveYield operations operatedProfile.1 0 0 = 2 := by
      simp [effectiveYield, operatedProfile, selectedProfile, operations]
    have hbefore : stage.before.stock 0 0 = 2 := by
      change (physicalStage.advance operatedProfile).stock 0 0 = 2
      exact operated_branch_has_two_units
    change (stage.advance operatedProfile).stock 0 0 +
        effectiveUse operations operatedProfile.1 0 0 =
      stage.before.stock 0 0 +
        effectiveYield operations operatedProfile.1 0 0 at hbalance
    rw [huse, hyield, hbefore] at hbalance
    omega
  have hidledTerminal :
      (delayedProgram.stateAt idledTerminalMoment).stock 0 0 = 2 := by
    let stage := delayedSecondStage (physicalStage.advance idleProfile)
      (firstStage_funds_delayed_stage idleProfile)
    change (stage.advance operatedProfile).stock 0 0 = 2
    have hbalance := stage.advance_balance operatedProfile 0 0
    have huse : effectiveUse operations operatedProfile.1 0 0 = 1 := by
      simp [effectiveUse, operatedProfile, selectedProfile, operations]
    have hyield : effectiveYield operations operatedProfile.1 0 0 = 2 := by
      simp [effectiveYield, operatedProfile, selectedProfile, operations]
    have hbefore : stage.before.stock 0 0 = 1 := by
      change (physicalStage.advance idleProfile).stock 0 0 = 1
      exact hidledFirst
    change (stage.advance operatedProfile).stock 0 0 +
        effectiveUse operations operatedProfile.1 0 0 =
      stage.before.stock 0 0 +
        effectiveYield operations operatedProfile.1 0 0 at hbalance
    rw [huse, hyield, hbefore] at hbalance
    omega
  exact ⟨hoperatedFirst, hoperatedTerminal, hidledFirst, hidledTerminal⟩

/-- The adapted frame records the action in the selected history and its
feasibility follows from the frame's generated menu and stock ledger. -/
theorem actionFrame_records_operated_action :
    frame.enacted (0 : Agent) FiniteEconomyProgram.ProgramMoment.root operatedHistory =
        EconomyAction.operate () ∧
      EconomyAction.operate () ∈
        frame.A_feas (0 : Agent) FiniteEconomyProgram.ProgramMoment.root operatedHistory := by
  have hroot : frame.mem_hist FiniteEconomyProgram.ProgramMoment.root operatedHistory := by
    change FiniteEconomyProgram.ProgramMoment.memHist
      program.toFiniteEconomyProgram FiniteEconomyProgram.ProgramMoment.root operatedHistory
    exact FiniteEconomyProgram.ProgramMoment.root_memHist operatedHistory
  have henacted :
      frame.enacted (0 : Agent) FiniteEconomyProgram.ProgramMoment.root operatedHistory =
        EconomyAction.operate () := by
    change operatedHistory.rootProfile.1 0 = EconomyAction.operate ()
    rfl
  refine ⟨henacted, ?_⟩
  rw [← henacted]
  exact frame.enacted_in_A_feas (0 : Agent)
    FiniteEconomyProgram.ProgramMoment.root operatedHistory hroot

/-- The recursive ActionFrame adapter reports the stock computed for the
operated program branch, rather than a separate inventory assignment. -/
theorem actionFrame_stock_matches_executed_branch :
    frame.omega (0 : Agent) operatedSuccessorMoment operatedHistory
      (0 : Means) = 2 := by
  change (program.stateAt operatedSuccessorMoment).stock 0 0 = 2
  simpa [FinitePhysicalEconomyProgram.stateAt, operatedSuccessorMoment,
    FiniteEconomyProgram.ProgramMoment.currentState, program,
    FinitePhysicalEconomyProgram.toFiniteEconomyProgram,
    FiniteEconomyProgram.physicalDecision] using operated_branch_has_two_units

end ProgramActionFrameWitness
end Praxeology

end
