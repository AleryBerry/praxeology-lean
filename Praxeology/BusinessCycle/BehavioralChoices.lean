/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.BehavioralProgram

/-!
# Choice profiles for the five-project household program

The initial household plan stage exposes the finite, affordable menu. These
lemmas identify a unilateral plan choice with the profile used by the direct
physical runner; every other actor keeps the stage's scheduled action.
-/

@[expose] public section

namespace Praxeology

/-- Every physically feasible action at the household's plan node is either
idling or one of the explicitly enumerated deposit, consumption, and offer
plans. -/
theorem fiveProjectHouseholdSavingAction_complete_menu
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation)
    (haction : action ∈ fiveProjectHouseholdSavingActionFrame.A_feas
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
      fiveProjectHouseholdSavingSuffix.selectedHistory) :
    action = EconomyAction.idle ∨
      ∃ plan ∈ fiveProjectHouseholdPlanChoices
        (fiveProjectRegimeData .householdTransfer),
        action = .operate (.chooseHouseholdPlan plan) := by
  let D := fiveProjectRegimeData .householdTransfer
  let run := fiveProjectInitialRun D
  let suffix := fiveProjectHouseholdSavingSuffix
  have hrootMenu : action ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu
        fiveProjectHousehold :=
    (mem_feasibleMenu_iff fiveProjectPhysicalOperations
      (suffix.program.stateAt FiniteEconomyProgram.ProgramMoment.root)
      fiveProjectHousehold
      ((FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu
          fiveProjectHousehold) action).1 haction |>.1
  have hphase : run.cursor.remainingPhases.head? = some .chooseHouseholdPlan := by
    decide
  have hinstruction : fiveProjectPhysicalInstruction D run.cursor run.state =
      fiveProjectHouseholdPlanInstruction D := by
    cases hremaining : run.cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
        have hphase' : phase = .chooseHouseholdPlan := by
          simpa [hremaining] using hphase
        subst phase
        simp [fiveProjectPhysicalInstruction, hremaining]
  change action ∈ (fiveProjectPhysicalInstruction D run.cursor run.state).stageMenu
      fiveProjectPhysicalOperations run.state fiveProjectHousehold at hrootMenu
  rw [hinstruction, PhysicalProfileInstruction.stageMenu] at hrootMenu
  have hscheduled : (fiveProjectHouseholdPlanInstruction D).affordableProfile
      fiveProjectPhysicalOperations run.state fiveProjectHousehold =
        fiveProjectHouseholdSavingAction := by
    decide
  rw [hscheduled] at hrootMenu
  simp only [Finset.mem_insert] at hrootMenu
  rcases hrootMenu with hidle | hscheduled' | halt
  · exact Or.inl hidle
  · right
    refine ⟨fiveProjectHouseholdPlanOf D, ?_, ?_⟩
    · decide
    · simpa [fiveProjectHouseholdSavingAction] using hscheduled'
  · change action ∈
      (fiveProjectHouseholdPlanChoiceActions D).filter
        (fun proposed => actionAffordable fiveProjectPhysicalOperations
          run.state fiveProjectHousehold proposed) at halt
    rcases Finset.mem_filter.mp halt with ⟨hchoice, _⟩
    rcases Finset.mem_image.mp hchoice with ⟨plan, hplan, haction⟩
    exact Or.inr ⟨plan, hplan, haction.symm⟩

/-- Every plan in the generated household menu is a root-stage action. -/
theorem fiveProjectHouseholdPlanAction_mem_root_menu
    (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer)) :
    EconomyAction.operate (.chooseHouseholdPlan plan) ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := fiveProjectHouseholdSavingSuffix.program.toFiniteEconomyProgram)).menu
        fiveProjectHousehold := by
  let D := fiveProjectRegimeData .householdTransfer
  let run := fiveProjectInitialRun D
  have hphase : run.cursor.remainingPhases.head? = some .chooseHouseholdPlan := by
    decide
  have hinstruction : fiveProjectPhysicalInstruction D run.cursor run.state =
      fiveProjectHouseholdPlanInstruction D := by
    cases hremaining : run.cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
        have hphase' : phase = .chooseHouseholdPlan := by
          simpa [hremaining] using hphase
        subst phase
        simp [fiveProjectPhysicalInstruction, hremaining]
  change EconomyAction.operate (.chooseHouseholdPlan plan) ∈
    (fiveProjectPhysicalInstruction D run.cursor run.state).stageMenu
      fiveProjectPhysicalOperations run.state fiveProjectHousehold
  rw [hinstruction, PhysicalProfileInstruction.stageMenu]
  simp only [Finset.mem_insert]
  right
  right
  simp only [fiveProjectHouseholdPlanInstruction,
    fiveProjectHouseholdPlanChoiceActions]
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_image.mpr ⟨plan, hplan, rfl⟩
  · intro good
    simp [rawActionUse, fiveProjectPhysicalOperations]

/-- A unilateral profile that selects a listed household plan is the same
profile obtained by replacing the household's scheduled plan in the selected
root profile. This is the profile-level link used by both compiled histories
and the direct cursor runner. -/
theorem fiveProjectHouseholdPlan_unilateralProfile_eq_replacement
    (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer)) :
    let D := fiveProjectRegimeData .householdTransfer
    let run := fiveProjectInitialRun D
    let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
    let stage := instruction.stage fiveProjectPhysicalOperations run.state
    let action := EconomyAction.operate (.chooseHouseholdPlan plan)
    let hmenu : action ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := fiveProjectHouseholdSavingSuffix.program.toFiniteEconomyProgram)).menu
        fiveProjectHousehold :=
      fiveProjectHouseholdPlanAction_mem_root_menu plan hplan
    stage.choices.unilateralProfile fiveProjectHousehold action hmenu =
      stage.choices.replaceProfile
        (instruction.selectedProfile fiveProjectPhysicalOperations run.state)
        fiveProjectHousehold action hmenu := by
  let D := fiveProjectRegimeData .householdTransfer
  let run := fiveProjectInitialRun D
  let instruction :=
    (fiveProjectPhysicalRegimeGenerator D).instruction run.cursor run.state
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation := .operate (.chooseHouseholdPlan plan)
  let hmenu : action ∈ stage.choices.menu fiveProjectHousehold :=
    by
      change EconomyAction.operate (.chooseHouseholdPlan plan) ∈
        (FiniteEconomyProgram.ProgramMoment.root.currentStage
          (program := fiveProjectHouseholdSavingSuffix.program.toFiniteEconomyProgram)).menu
          fiveProjectHousehold
      exact fiveProjectHouseholdPlanAction_mem_root_menu plan hplan
  have hphase : run.cursor.remainingPhases.head? = some .chooseHouseholdPlan := by
    decide
  have hinstruction : instruction = fiveProjectHouseholdPlanInstruction D := by
    cases hremaining : run.cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
        have hphase' : phase = .chooseHouseholdPlan := by
          simpa [hremaining] using hphase
        subst phase
        simp [instruction, fiveProjectPhysicalRegimeGenerator,
          fiveProjectPhysicalInstruction, hremaining]
  have hscheduled_other (actor : FiveProjectPhysicalAgent)
      (hactor : actor ≠ fiveProjectHousehold) :
      (instruction.selectedProfile fiveProjectPhysicalOperations run.state).1 actor =
        EconomyAction.idle := by
    rw [hinstruction]
    simp [PhysicalProfileInstruction.selectedProfile,
      PhysicalProfileInstruction.affordableProfile,
      fiveProjectHouseholdPlanInstruction, hactor,
      actionAffordable, rawActionUse, fiveProjectPhysicalOperations]
  change stage.choices.unilateralProfile fiveProjectHousehold action hmenu =
    stage.choices.replaceProfile
      (instruction.selectedProfile fiveProjectPhysicalOperations run.state)
      fiveProjectHousehold action hmenu
  apply Subtype.ext
  funext actor
  by_cases hactor : actor = fiveProjectHousehold
  · subst actor
    simp [FiniteChoiceStage.unilateralProfile, FiniteChoiceStage.replaceProfile,
      action]
  · have hleft := stage.choices.unilateralProfile_other
      fiveProjectHousehold actor action hmenu hactor
    have hright := stage.choices.replaceProfile_other
      (instruction.selectedProfile fiveProjectPhysicalOperations run.state)
      (i := fiveProjectHousehold) (j := actor) action hmenu hactor
    rw [hleft, hright]
    exact (hscheduled_other actor hactor).symm

/-- Direct run after a plan choice, used to compare the physical cursor with
the selected continuation of a typed program history. -/
def fiveProjectHouseholdPlanRunFromSuffix
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run)
    (hphase : run.cursor.remainingPhases.head? = some .chooseHouseholdPlan)
    (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices D) : FiveProjectPhysicalRun :=
  fiveProjectRunChoices D (List.replicate suffix.fuel true)
    (fiveProjectRunSelectedHouseholdPlan D run plan hphase hplan)

/-- A plan replay and the corresponding typed ActionFrame branch have the
same terminal inventory. The common root profile is the household's selected
action with the reference schedule's peer actions preserved. -/
theorem fiveProjectHouseholdPlan_typed_replay_state
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run)
    (hphase : run.cursor.remainingPhases.head? = some .chooseHouseholdPlan)
    (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices D) :
    let action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
        FiveProjectPhysicalOperation := .operate (.chooseHouseholdPlan plan)
    ((fiveProjectPhysicalSuffixBehavior suffix 0).selectedHistory
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root action
      suffix.selectedHistory).terminalState =
      (fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan).state := by
  classical
  let instruction :=
    (fiveProjectPhysicalRegimeGenerator D).instruction run.cursor run.state
  have hinstruction : instruction = fiveProjectHouseholdPlanInstruction D := by
    cases hremaining : run.cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
        have hphase' : phase = .chooseHouseholdPlan := by
          simpa [hremaining] using hphase
        subst phase
        simp [instruction, fiveProjectPhysicalRegimeGenerator,
          fiveProjectPhysicalInstruction, hremaining]
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation := .operate (.chooseHouseholdPlan plan)
  let scheduled := instruction.selectedProfile fiveProjectPhysicalOperations run.state
  have hmenu : action ∈ stage.choices.menu fiveProjectHousehold := by
    change action ∈ instruction.stageMenu fiveProjectPhysicalOperations run.state
      fiveProjectHousehold
    rw [hinstruction]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨plan, hplan, rfl⟩, ?_⟩
    intro good
    simp [rawActionUse, action, fiveProjectPhysicalOperations]
  let profile := stage.choices.replaceProfile scheduled fiveProjectHousehold action hmenu
  have hrootMenu : action ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu fiveProjectHousehold := by
    change action ∈ stage.choices.menu fiveProjectHousehold
    exact hmenu
  have hroot := fiveProjectPhysicalSuffixBehavior_selectedHistory_root
    suffix 0 fiveProjectHousehold action suffix.selectedHistory hrootMenu
  have hbase : suffix.selectedHistory =
      FiniteEconomyProgram.ProgramHistory.decision scheduled
        (physicalProfileGeneratorHistory fiveProjectPhysicalOperations
          (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
          (fiveProjectNextCursor D run.cursor run.state
            ⟨instruction, scheduled⟩)
          (stage.advance scheduled)) := by
    rfl
  have hrootProfile : suffix.selectedHistory.rootProfile = scheduled := by
    rw [hbase]
    rfl
  have hdirect :
      (fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan).state =
        executePhysicalProfileGenerator fiveProjectPhysicalOperations
          (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
          (fiveProjectNextCursor D run.cursor run.state ⟨instruction, profile⟩)
          (stage.advance profile) := by
    unfold fiveProjectHouseholdPlanRunFromSuffix
    rw [fiveProjectRunChoices_all_selected_state]
    unfold fiveProjectRunSelectedHouseholdPlan
    change (executePhysicalProfileGenerator fiveProjectPhysicalOperations
        (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
        (fiveProjectNextCursor D run.cursor run.state ⟨instruction, profile⟩)
        (stage.advance profile)) = _
    rfl
  change ((fiveProjectPhysicalSuffixBehavior suffix 0).selectedHistory
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root action
      suffix.selectedHistory).terminalState =
    (fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan).state
  cases hhistory : suffix.selectedHistory with
  | decision rootProfile tail =>
      have hrootProfile' : rootProfile = scheduled := by
        rw [hhistory, FiniteEconomyProgram.ProgramHistory.rootProfile] at hrootProfile
        exact hrootProfile
      subst rootProfile
      rw [hhistory] at hroot
      rw [hroot]
      simp only [FiniteEconomyProgram.ProgramHistory.selectActorAtRootWithContinuation]
      by_cases hselected : action = scheduled.1 fiveProjectHousehold
      · have hdirectProfile : profile = scheduled := by
          apply Subtype.ext
          funext actor'
          by_cases hactor : actor' = fiveProjectHousehold
          · subst actor'
            simpa [profile, FiniteChoiceStage.replaceProfile] using hselected
          · exact stage.choices.replaceProfile_other scheduled
              (i := fiveProjectHousehold) (j := actor') action hmenu hactor
        have htail : tail = physicalProfileGeneratorHistory fiveProjectPhysicalOperations
            (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
            (fiveProjectNextCursor D run.cursor run.state
              ⟨instruction, scheduled⟩) (stage.advance scheduled) := by
          have hEq := hbase.symm.trans hhistory
          cases hEq
          rfl
        simp only [hselected]
        change tail.terminalState =
          (fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan).state
        calc
          tail.terminalState = executePhysicalProfileGenerator fiveProjectPhysicalOperations
              (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
              (fiveProjectNextCursor D run.cursor run.state ⟨instruction, scheduled⟩)
              (stage.advance scheduled) := by
                rw [htail]
                exact physicalProfileGeneratorHistory_terminalState _ _ _ _ _
          _ = (fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan).state := by
            simpa [hdirectProfile] using hdirect.symm
      · let replaced := stage.choices.replaceProfile scheduled
          fiveProjectHousehold action hrootMenu
        have hprofile : replaced = profile := by
          apply Subtype.ext
          funext actor'
          by_cases hactor : actor' = fiveProjectHousehold
          · subst actor'
            simp [replaced, profile, FiniteChoiceStage.replaceProfile]
          · simp [replaced, profile, FiniteChoiceStage.replaceProfile, hactor]
        simp only [hselected]
        change (physicalProfileGeneratorHistory fiveProjectPhysicalOperations
            (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
            (fiveProjectNextCursor D run.cursor run.state ⟨instruction, replaced⟩)
            (stage.advance replaced)).terminalState =
          (fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan).state
        calc
          (physicalProfileGeneratorHistory fiveProjectPhysicalOperations
            (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
            (fiveProjectNextCursor D run.cursor run.state ⟨instruction, replaced⟩)
            (stage.advance replaced)).terminalState =
              executePhysicalProfileGenerator fiveProjectPhysicalOperations
                (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
                (fiveProjectNextCursor D run.cursor run.state ⟨instruction, replaced⟩)
              (stage.advance replaced) := by
                exact physicalProfileGeneratorHistory_terminalState _ _ _ _ _
          _ = (fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan).state := by
            rw [hprofile, ← hdirect]

/-- The household's named root plan branch is the same typed history that
the ActionFrame evaluates. -/
theorem fiveProjectHouseholdPlan_typed_replay_state_named
    (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer)) :
    let suffix := fiveProjectHouseholdSavingSuffix
    let initial := fiveProjectInitialRun
      (fiveProjectRegimeData .householdTransfer)
    let hphase : initial.cursor.remainingPhases.head? = some .chooseHouseholdPlan := by
      decide
    let action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
        FiveProjectPhysicalOperation := .operate (.chooseHouseholdPlan plan)
    ((fiveProjectPhysicalSuffixBehavior suffix 0).selectedHistory
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root action
      suffix.selectedHistory).terminalState =
      (fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan).state := by
  let initial := fiveProjectInitialRun (fiveProjectRegimeData .householdTransfer)
  have hphase : initial.cursor.remainingPhases.head? = some .chooseHouseholdPlan := by
    decide
  exact fiveProjectHouseholdPlan_typed_replay_state
    fiveProjectHouseholdSavingSuffix hphase plan hplan

/-- The suffix replay starts from the same initial run and consumes exactly
the remaining physical phases used by the full household-plan runner. -/
theorem fiveProjectHouseholdPlanRunFromSuffix_eq_runFor
    (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer)) :
    let initial := fiveProjectInitialRun
      (fiveProjectRegimeData .householdTransfer)
    let hphase : initial.cursor.remainingPhases.head? = some .chooseHouseholdPlan := by
      decide
    fiveProjectHouseholdPlanRunFromSuffix
      fiveProjectHouseholdSavingSuffix hphase plan hplan =
      fiveProjectHouseholdPlanRunFor
        (fiveProjectRegimeData .householdTransfer) plan hplan := by
  rfl

/-- The household's terminal ActionFrame outcome for a listed root plan agrees
with the same plan's full physical replay, including delivered services and
the holdings tie-breaker. -/
theorem fiveProjectHouseholdPlan_typed_outcome_eq_physical
    (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer)) :
    let suffix := fiveProjectHouseholdSavingSuffix
    let action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
        FiveProjectPhysicalOperation := .operate (.chooseHouseholdPlan plan)
    fiveProjectProgramEndHouseholdOutcome suffix.program
      (suffix.program.intendedEnd
        (fiveProjectPhysicalSuffixBehavior suffix 0)
        fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root action) =
      fiveProjectHouseholdPlanOutcomeFor
        (fiveProjectRegimeData .householdTransfer) plan := by
  let suffix := fiveProjectHouseholdSavingSuffix
  let initial := fiveProjectInitialRun
    (fiveProjectRegimeData .householdTransfer)
  have hphase : initial.cursor.remainingPhases.head? = some .chooseHouseholdPlan := by
    decide
  let action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation := .operate (.chooseHouseholdPlan plan)
  let behavior := fiveProjectPhysicalSuffixBehavior suffix 0
  let selectedHistory := behavior.selectedHistory fiveProjectHousehold
    FiniteEconomyProgram.ProgramMoment.root action suffix.selectedHistory
  let direct := fiveProjectHouseholdPlanRunFromSuffix suffix hphase plan hplan
  have hbranch : selectedHistory.terminalState = direct.state := by
    simpa [selectedHistory, action, suffix, initial, hphase] using
      fiveProjectHouseholdPlan_typed_replay_state_named plan hplan
  have hrun : direct = fiveProjectHouseholdRunForPlan
      (fiveProjectRegimeData .householdTransfer) plan := by
    simpa [direct, fiveProjectHouseholdRunForPlan, hplan] using
      fiveProjectHouseholdPlanRunFromSuffix_eq_runFor plan hplan
  have hmenu : action ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu fiveProjectHousehold := by
    simpa [suffix, action] using fiveProjectHouseholdPlanAction_mem_root_menu plan hplan
  have hhorizon : behavior.evaluationHorizon fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root action = .terminalSettlement := by
    simp [behavior, fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  have hmat : suffix.program.expectedMaturation behavior fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root action selectedHistory =
        selectedHistory.terminalMoment := by
    simp [FinitePhysicalEconomyProgram.expectedMaturation,
      FinitePhysicalEconomyProgram.horizonMoment, hhorizon,
      FinitePhysicalEconomyProgram.terminalSettlementHorizon]
  have href : behavior.referenceHistory fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root = suffix.selectedHistory := by
    simp [behavior, fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  change fiveProjectProgramEndHouseholdOutcome suffix.program
      (suffix.program.intendedEnd behavior fiveProjectHousehold
        FiniteEconomyProgram.ProgramMoment.root action) =
      fiveProjectHouseholdPlanOutcomeFor
        (fiveProjectRegimeData .householdTransfer) plan
  rw [suffix.program.intendedEnd_uses_behavior_selected_history
    behavior fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root action hmenu]
  rw [href, hmat]
  unfold fiveProjectHouseholdPlanOutcomeFor
  rw [← hrun]
  simp [fiveProjectProgramEndHouseholdOutcome,
    FinitePhysicalEconomyProgram.outcomeAt, finiteProgramEndRequirement,
    FinitePhysicalEconomyProgram.stateAt_terminalMoment,
    FiveProjectPhysicalRun.householdOutcome, hbranch]

/-- The scheduled saving plan is purposeful under the household's stated
terminal reserve, service, money, and holdings preference. Feasibility and
execution come from the ActionFrame; improvement and undominatedness are
proved against idle and the complete twelve-plan menu. -/
theorem fiveProjectHouseholdSavingAction_purposeful :
    @Praxeology.PurposefulAct fiveProjectHouseholdSavingActionFrame
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
      fiveProjectHouseholdSavingSuffix.selectedHistory
      fiveProjectHouseholdSavingAction := by
  refine ⟨fiveProjectHouseholdSavingAction_feasible,
    fiveProjectHouseholdSavingAction_executes, Or.inr ?_, ?_⟩
  · exact fiveProjectHouseholdSavingAction_beats_idle
  · intro alternative halternative hbetter
    rcases fiveProjectHouseholdSavingAction_complete_menu alternative halternative with
      hidle | ⟨plan, hplan, haction⟩
    · subst alternative
      exact (fiveProjectHouseholdSavingActionFrame.pref_asymm
        fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
        fiveProjectHouseholdSavingSuffix.selectedHistory
        fiveProjectHouseholdSavingAction_beats_idle) hbetter
    · subst alternative
      have hselectedPlan : fiveProjectHouseholdPlanOf
          (fiveProjectRegimeData .householdTransfer) ∈
            fiveProjectHouseholdPlanChoices
              (fiveProjectRegimeData .householdTransfer) := by
        decide
      change fiveProjectHouseholdPrefers
        (fiveProjectProgramEndHouseholdOutcome
          fiveProjectHouseholdSavingSuffix.program
          (fiveProjectHouseholdSavingSuffix.program.intendedEnd
            (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
            fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
            (.operate (.chooseHouseholdPlan plan))))
        (fiveProjectProgramEndHouseholdOutcome
          fiveProjectHouseholdSavingSuffix.program
          (fiveProjectHouseholdSavingSuffix.program.intendedEnd
            (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
            fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
            fiveProjectHouseholdSavingAction)) at hbetter
      rw [fiveProjectHouseholdPlan_typed_outcome_eq_physical plan hplan] at hbetter
      have hselectedEnd :
          fiveProjectProgramEndHouseholdOutcome
              fiveProjectHouseholdSavingSuffix.program
              (fiveProjectHouseholdSavingSuffix.program.intendedEnd
                (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
                fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
                fiveProjectHouseholdSavingAction) =
            fiveProjectHouseholdPlanOutcomeFor
              (fiveProjectRegimeData .householdTransfer)
              (fiveProjectHouseholdPlanOf
                (fiveProjectRegimeData .householdTransfer)) := by
        simpa [fiveProjectHouseholdSavingAction] using
          fiveProjectHouseholdPlan_typed_outcome_eq_physical
            (fiveProjectHouseholdPlanOf
              (fiveProjectRegimeData .householdTransfer)) hselectedPlan
      rw [hselectedEnd] at hbetter
      exact (fiveProject_household_saving_plan_is_menu_undominated plan hplan) hbetter

end Praxeology
