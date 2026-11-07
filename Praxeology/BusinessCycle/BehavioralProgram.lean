/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.Outcome
public import Praxeology.Veridical

/-!
# Behavioral decision stages for the finite physical program

The helpers here expose a generated suffix beginning at a named physical
phase. They reuse the existing cursor transition and schedule uniqueness
proofs; they do not change the economic instructions or their order.
-/

@[expose] public section

namespace Praxeology

theorem fiveProjectRunStep_remainingPhases (D : FiveProjectRegimeData)
    (enactScheduled : Bool) (run : FiveProjectPhysicalRun) :
    (fiveProjectRunStep D enactScheduled run).cursor.remainingPhases =
      run.cursor.remainingPhases.drop 1 := by
  simp [fiveProjectRunStep, fiveProjectNextCursor_remainingPhases]

theorem fiveProjectRunUntilPhaseFuel_reaches_head (D : FiveProjectRegimeData)
    (target : FiveProjectPhysicalPhase) (fuel : ℕ)
    (run : FiveProjectPhysicalRun)
    (hfuel : run.cursor.remainingPhases.length ≤ fuel)
    (hnodup : run.cursor.remainingPhases.Nodup)
    (htarget : target ∈ run.cursor.remainingPhases) :
    (fiveProjectRunUntilPhaseFuel D target fuel run).cursor.remainingPhases.head? =
      some target := by
  induction fuel generalizing run with
  | zero =>
      have hnil : run.cursor.remainingPhases = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      rw [hnil] at htarget
      simp at htarget
  | succ fuel ih =>
      cases hremaining : run.cursor.remainingPhases with
      | nil =>
          rw [hremaining] at htarget
          simp at htarget
      | cons phase rest =>
          have htarget' : target ∈ phase :: rest := by
            simpa [hremaining] using htarget
          rcases List.mem_cons.mp htarget' with heq | htail
          · have hphase : phase = target := heq.symm
            subst phase
            simp [fiveProjectRunUntilPhaseFuel, hremaining]
          · have hnextLength :
                (fiveProjectRunStep D true run).cursor.remainingPhases.length ≤ fuel := by
              rw [fiveProjectRunStep_remainingPhases]
              have hfuel' : rest.length ≤ fuel := by
                have hcons : rest.length + 1 ≤ fuel + 1 := by
                  simpa [hremaining] using hfuel
                omega
              simpa [hremaining] using hfuel'
            have hnodupCons : (phase :: rest).Nodup := by
              simpa [hremaining] using hnodup
            have hrestNodup : rest.Nodup := (List.nodup_cons.mp hnodupCons).2
            have hnextNodup :
                (fiveProjectRunStep D true run).cursor.remainingPhases.Nodup := by
              rw [fiveProjectRunStep_remainingPhases]
              simpa [hremaining] using hrestNodup
            have hnextTarget : target ∈
                (fiveProjectRunStep D true run).cursor.remainingPhases := by
              rw [fiveProjectRunStep_remainingPhases]
              simpa [hremaining] using htail
            have hnot : phase ≠ target := by
              intro heq
              have hmem : phase ∈ rest := by simpa [heq] using htail
              exact (List.nodup_cons.mp hnodupCons).1 hmem
            simpa [fiveProjectRunUntilPhaseFuel, hremaining, hnot] using
              ih (fiveProjectRunStep D true run) hnextLength hnextNodup hnextTarget

theorem fiveProjectRunUntilPhase_reaches_head (D : FiveProjectRegimeData)
    (target : FiveProjectPhysicalPhase) (run : FiveProjectPhysicalRun)
    (hnodup : run.cursor.remainingPhases.Nodup)
    (htarget : target ∈ run.cursor.remainingPhases) :
    (fiveProjectRunUntilPhase D target run).cursor.remainingPhases.head? =
      some target := by
  exact fiveProjectRunUntilPhaseFuel_reaches_head D target _ run le_rfl hnodup htarget

/-- Compile the unconsumed physical schedule from a reachable run. The
nonempty case unfolds to the existing decision constructor; the empty case
is the existing halt constructor. -/
def fiveProjectPhysicalSuffixProgram (D : FiveProjectRegimeData)
    (run : FiveProjectPhysicalRun) :
    FinitePhysicalEconomyProgram FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Nat run.cursor.remainingPhases.length run.state :=
  compilePhysicalProfileGenerator fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) run.cursor.remainingPhases.length
    run.cursor run.state

/-- Selected suffix history generated from the same cursor, state, and
instructions as `fiveProjectPhysicalSuffixProgram`. -/
def fiveProjectPhysicalSuffixHistory (D : FiveProjectRegimeData)
    (run : FiveProjectPhysicalRun) :
    (fiveProjectPhysicalSuffixProgram D run).History :=
  physicalProfileGeneratorHistory fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) run.cursor.remainingPhases.length
    run.cursor run.state

/-- Change one action only at a suffix root, then let the same physical
generator choose every continuation profile from its resulting cursor and
inventory. A later phase cannot be mistaken for the root because each cursor
transition strictly shortens the remaining schedule. -/
def fiveProjectPhysicalSuffixRootActionSelector
    (D : FiveProjectRegimeData) (startingCursor : FiveProjectPhysicalCursor)
    (actor : FiveProjectPhysicalAgent)
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation) : FiveProjectPhysicalProfileSelector D :=
  fun cursor state =>
    let instruction := fiveProjectPhysicalInstruction D cursor state
    let stage := instruction.stage fiveProjectPhysicalOperations state
    let scheduled := instruction.selectedProfile fiveProjectPhysicalOperations state
    if _hroot : cursor.remainingPhases.length = startingCursor.remainingPhases.length then
      if hmenu : action ∈ stage.choices.menu actor then
        stage.choices.replaceProfile scheduled actor action hmenu
      else scheduled
    else scheduled

/-- A root counterfactual history for a suffix delegates every later profile
to the same state-dependent physical generator. -/
def fiveProjectPhysicalSuffixHistoryWithRootAction
    (D : FiveProjectRegimeData) (run : FiveProjectPhysicalRun)
    (actor : FiveProjectPhysicalAgent)
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation) :
    (fiveProjectPhysicalSuffixProgram D run).History :=
  physicalProfileGeneratorHistoryWithPolicy fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D)
    (fiveProjectPhysicalSuffixRootActionSelector D run.cursor actor action)
    run.cursor.remainingPhases.length run.cursor run.state

/-- A nonempty generated suffix carries its exact fuel, compiled program, and
selected history. The length equation ensures every cursor phase is consumed
exactly once by the recursive program. -/
structure FiveProjectPhysicalSuffix (D : FiveProjectRegimeData)
    (run : FiveProjectPhysicalRun) where
  fuel : ℕ
  fuel_matches_remaining : fuel + 1 = run.cursor.remainingPhases.length

def FiveProjectPhysicalSuffix.program {D : FiveProjectRegimeData}
    {run : FiveProjectPhysicalRun} (suffix : FiveProjectPhysicalSuffix D run) :
    FinitePhysicalEconomyProgram FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Nat (suffix.fuel + 1) run.state :=
  compilePhysicalProfileGenerator fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) (suffix.fuel + 1)
    run.cursor run.state

def FiveProjectPhysicalSuffix.selectedHistory {D : FiveProjectRegimeData}
    {run : FiveProjectPhysicalRun} (suffix : FiveProjectPhysicalSuffix D run) :
    suffix.program.History :=
  physicalProfileGeneratorHistory fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) (suffix.fuel + 1)
    run.cursor run.state

/-- Compile a nonempty run suffix from its current cursor and inventory. -/
def fiveProjectPhysicalSuffix (D : FiveProjectRegimeData)
    (run : FiveProjectPhysicalRun)
    (hnonempty : run.cursor.remainingPhases ≠ []) :
    FiveProjectPhysicalSuffix D run := by
  cases hphases : run.cursor.remainingPhases with
  | nil => exact False.elim (hnonempty hphases)
  | cons phase rest =>
      refine {
        fuel := rest.length
        fuel_matches_remaining := ?_ }
      simp [hphases]

def fiveProjectProgramEndEntrepreneurOutcome {Moment : Type}
    (project : Fin 5) (ending : FiniteProgramEnd Moment FiveProjectPhysicalGood) :
    FiveProjectEntrepreneurOutcome :=
  { collateralOwned := finiteProgramEndRequirement ending
      (fiveProjectCollateralGood project)
    terminalMoney := finiteProgramEndRequirement ending fiveProjectMoneyGood
    totalPhysicalHoldings := Finset.univ.sum fun good =>
      finiteProgramEndRequirement ending good }

def fiveProjectProgramEndHouseholdOutcome {fuel : ℕ}
    {state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
    (program : FinitePhysicalEconomyProgram FiveProjectPhysicalAgent
      FiveProjectPhysicalGood FiveProjectPhysicalOperation Nat fuel state)
    (ending : program.End) : FiveProjectHouseholdOutcome :=
  { terminalMoney := finiteProgramEndRequirement ending fiveProjectMoneyGood
    deliveredServices := match ending with
      | .timed _ moment =>
          (program.stateAt moment).services fiveProjectHousehold
            fiveProjectConsumptionService
      | _ => 0
    totalPhysicalHoldings := Finset.univ.sum fun good =>
      finiteProgramEndRequirement ending good }

theorem fiveProjectHouseholdPrefers_of_more_money_same_services
    (preferred other : FiveProjectHouseholdOutcome)
    (hservices : preferred.deliveredServices = other.deliveredServices)
    (hmoney : preferred.terminalMoney > other.terminalMoney) :
    fiveProjectHouseholdPrefers preferred other := by
  unfold fiveProjectHouseholdPrefers fiveProjectHouseholdPreferenceRank
  dsimp
  by_cases hp : 5 ≤ preferred.terminalMoney
  · by_cases ho : 5 ≤ other.terminalMoney
    · right
      refine ⟨by simp [hp, ho], Or.inr ⟨hservices, Or.inl hmoney⟩⟩
    · exact Or.inl (by simp [hp, ho])
  · have ho : ¬ 5 ≤ other.terminalMoney := by omega
    right
    exact ⟨by simp [hp, ho], Or.inr ⟨hservices, Or.inl hmoney⟩⟩

/-- Actor-specific ordinal comparison for the generated program. Borrowers use
the existing collateral-first preference, the household uses its stated
reserve/service/money/holdings order, and remaining actors use strict money
comparison. -/
def fiveProjectPhysicalSuffixPreference {fuel : ℕ} {state : PhysicalState
      FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
    (program : FinitePhysicalEconomyProgram FiveProjectPhysicalAgent
      FiveProjectPhysicalGood FiveProjectPhysicalOperation Nat fuel state)
    (project : Fin 5) (actor : FiveProjectPhysicalAgent)
    (_moment : program.Moment) (_history : program.History)
    (preferred other : program.End) : Prop :=
  if actor = fiveProjectPhysicalBorrower project then
    fiveProjectEntrepreneurPrefers
      (fiveProjectProgramEndEntrepreneurOutcome project preferred)
      (fiveProjectProgramEndEntrepreneurOutcome project other)
  else if actor = fiveProjectHousehold then
    fiveProjectHouseholdPrefers
      (fiveProjectProgramEndHouseholdOutcome program preferred)
      (fiveProjectProgramEndHouseholdOutcome program other)
  else
    finiteProgramEndRequirement preferred fiveProjectMoneyGood >
      finiteProgramEndRequirement other fiveProjectMoneyGood

theorem fiveProjectPhysicalSuffixPreference_asymmetric {fuel : ℕ}
    {state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
    (program : FinitePhysicalEconomyProgram FiveProjectPhysicalAgent
      FiveProjectPhysicalGood FiveProjectPhysicalOperation Nat fuel state)
    (project : Fin 5) (actor : FiveProjectPhysicalAgent)
    (moment : program.Moment) (history : program.History)
    {preferred other : program.End}
    (hprefer : fiveProjectPhysicalSuffixPreference program project actor
      moment history preferred other) :
    ¬ fiveProjectPhysicalSuffixPreference program project actor moment history
      other preferred := by
  by_cases hborrower : actor = fiveProjectPhysicalBorrower project
  · subst actor
    simp only [fiveProjectPhysicalSuffixPreference] at hprefer ⊢
    exact fiveProjectEntrepreneurPrefers_asymmetric _ _ hprefer
  · by_cases hhousehold : actor = fiveProjectHousehold
    · have hhouseholdNotBorrower :
          fiveProjectHousehold ≠ fiveProjectPhysicalBorrower project := by
        intro heq
        exact hborrower (hhousehold.trans heq)
      subst actor
      simp only [fiveProjectPhysicalSuffixPreference,
        ite_eq_right hhouseholdNotBorrower] at hprefer ⊢
      change fiveProjectHouseholdPrefers
        (fiveProjectProgramEndHouseholdOutcome program preferred)
        (fiveProjectProgramEndHouseholdOutcome program other) at hprefer
      change ¬ fiveProjectHouseholdPrefers
        (fiveProjectProgramEndHouseholdOutcome program other)
        (fiveProjectProgramEndHouseholdOutcome program preferred)
      exact fiveProjectHouseholdPrefers_asymmetric _ _ hprefer
    · simp only [fiveProjectPhysicalSuffixPreference, ite_eq_right hborrower,
        ite_eq_right hhousehold] at hprefer ⊢
      omega

/-- A teleological comparison of bundles must strictly increase a good that
is the sole requirement of every valued end. -/
theorem subjective_teleological_focus_good_increases
    {Ends Means : Type} [DecidableEq Ends]
    (requirement : Ends → Means → ℕ) (good : Means)
    (preferred other : Means → ℕ)
    (hdominates : SubjectiveTeleologicalDominates requirement
      (fun ending => 0 < requirement ending good ∧
        ∀ means, means ≠ good → requirement ending means = 0)
      preferred other) :
    preferred good > other good := by
  rcases hdominates with ⟨_, ⟨ends, hvalued, hattains, hmisses⟩⟩
  have hsomeMiss : ∃ means, ¬ ends.sum (fun ending => requirement ending means) ≤
      other means := by
    by_contra hno
    have hattainsOther : ∀ means,
        ends.sum (fun ending => requirement ending means) ≤ other means := by
      intro means
      by_contra hmissAtMean
      exact hno ⟨means, hmissAtMean⟩
    exact hmisses hattainsOther
  rcases hsomeMiss with ⟨means, hmiss⟩
  have hstrict : other means < ends.sum (fun ending => requirement ending means) :=
    Nat.lt_of_not_ge hmiss
  by_cases hgood : means = good
  · subst means
    have hbound := hattains good
    omega
  · have hsumZero : ends.sum (fun ending => requirement ending means) = 0 := by
      apply Finset.sum_eq_zero
      intro ending hending
      exact (hvalued ending hending).2 means hgood
    rw [hsumZero] at hstrict
    omega

/-- The borrower's valued ends focus on pledged collateral; other actors'
valued ends focus on money. This makes the generic teleological compatibility
law follow from the stated ordinal preference rather than a vacuous empty
valuation. -/
def fiveProjectPhysicalSuffixValuedEnd {fuel : ℕ}
    {state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
    (program : FinitePhysicalEconomyProgram FiveProjectPhysicalAgent
      FiveProjectPhysicalGood FiveProjectPhysicalOperation Nat fuel state)
    (project : Fin 5) (actor : FiveProjectPhysicalAgent)
    (_moment : program.Moment) (_history : program.History)
    (ending : program.End) : Prop :=
  let good := if actor = fiveProjectPhysicalBorrower project then
      fiveProjectCollateralGood project else fiveProjectMoneyGood
  0 < finiteProgramEndRequirement ending good ∧
    ∀ means, means ≠ good → finiteProgramEndRequirement ending means = 0

theorem fiveProjectPhysicalSuffixValuedEnd_borrower {fuel : ℕ}
    {state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
    (program : FinitePhysicalEconomyProgram FiveProjectPhysicalAgent
      FiveProjectPhysicalGood FiveProjectPhysicalOperation Nat fuel state)
    (project : Fin 5) (moment : program.Moment) (history : program.History) :
    fiveProjectPhysicalSuffixValuedEnd program project
        (fiveProjectPhysicalBorrower project) moment history =
      (fun ending => 0 < finiteProgramEndRequirement ending
          (fiveProjectCollateralGood project) ∧
        ∀ means, means ≠ fiveProjectCollateralGood project →
          finiteProgramEndRequirement ending means = 0) := by
  funext ending
  simp [fiveProjectPhysicalSuffixValuedEnd]

theorem fiveProjectPhysicalSuffixValuedEnd_other {fuel : ℕ}
    {state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
    (program : FinitePhysicalEconomyProgram FiveProjectPhysicalAgent
      FiveProjectPhysicalGood FiveProjectPhysicalOperation Nat fuel state)
    (project : Fin 5) (actor : FiveProjectPhysicalAgent)
    (hactor : actor ≠ fiveProjectPhysicalBorrower project)
    (moment : program.Moment) (history : program.History) :
    fiveProjectPhysicalSuffixValuedEnd program project actor moment history =
      (fun ending => 0 < finiteProgramEndRequirement ending fiveProjectMoneyGood ∧
        ∀ means, means ≠ fiveProjectMoneyGood →
          finiteProgramEndRequirement ending means = 0) := by
  funext ending
  simp [fiveProjectPhysicalSuffixValuedEnd, hactor]

noncomputable def fiveProjectPhysicalSuffixReferenceHistory
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run)
    (_actor : FiveProjectPhysicalAgent) (moment : suffix.program.Moment) :
    suffix.program.History := by
  classical
  exact if hroot : moment = FiniteEconomyProgram.ProgramMoment.root then
    suffix.selectedHistory
  else Classical.choose (FiniteEconomyProgram.ProgramMoment.exists_history moment)

theorem fiveProjectPhysicalSuffixReferenceHistory_mem
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run)
    (_actor : FiveProjectPhysicalAgent) (moment : suffix.program.Moment) :
    FiniteEconomyProgram.ProgramMoment.memHist suffix.program.toFiniteEconomyProgram
      moment (fiveProjectPhysicalSuffixReferenceHistory suffix _actor moment) := by
  classical
  by_cases hroot : moment = FiniteEconomyProgram.ProgramMoment.root
  · subst moment
    exact FiniteEconomyProgram.ProgramMoment.root_memHist _
  · unfold fiveProjectPhysicalSuffixReferenceHistory
    rw [dite_eq_right hroot]
    exact Classical.choose_spec
      (FiniteEconomyProgram.ProgramMoment.exists_history moment)

@[simp]
theorem fiveProjectPhysicalSuffixReferenceHistory_root
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run) (actor : FiveProjectPhysicalAgent) :
    fiveProjectPhysicalSuffixReferenceHistory suffix actor
      FiniteEconomyProgram.ProgramMoment.root = suffix.selectedHistory := by
  unfold fiveProjectPhysicalSuffixReferenceHistory
  by_cases hroot : True
  · simp
  · exact False.elim (hroot trivial)

/-- Behavioral specification for a physical suffix. Its selected history is
the generator's enacted profile; changed root actions keep the same peers and
regenerate every later instruction from the resulting state and cursor. -/
noncomputable def fiveProjectPhysicalSuffixBaseBehavior
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run) (project : Fin 5) :
    suffix.program.ActionFrameBehavior := by
  classical
  let preference := fiveProjectPhysicalSuffixPreference suffix.program project
  let base := FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory
    (fiveProjectPhysicalSuffixReferenceHistory suffix)
    (fiveProjectPhysicalSuffixReferenceHistory_mem suffix)
    (fiveProjectPhysicalSuffixValuedEnd suffix.program project)
    (by intro actor moment h₁ h₂ ending hm₁ hm₂; rfl)
    preference
    (by intro actor moment h₁ h₂ hm₁ hm₂; rfl)
    (by
      intro actor moment history preferred other hprefer
      exact fiveProjectPhysicalSuffixPreference_asymmetric suffix.program
        project actor moment history hprefer)
    (by
      intro actor moment history b₁ b₂ hdominates
      by_cases hborrower : actor = fiveProjectPhysicalBorrower project
      · have hfocus : SubjectiveTeleologicalDominates finiteProgramEndRequirement
            (fun ending : suffix.program.End => 0 < finiteProgramEndRequirement ending
                (fiveProjectCollateralGood project) ∧
              ∀ means, means ≠ fiveProjectCollateralGood project →
                finiteProgramEndRequirement ending means = 0) b₁ b₂ := by
          subst actor
          rw [fiveProjectPhysicalSuffixValuedEnd_borrower] at hdominates
          exact hdominates
        have hcollateral := subjective_teleological_focus_good_increases
          finiteProgramEndRequirement (fiveProjectCollateralGood project) b₁ b₂ (by
            exact hfocus)
        subst actor
        dsimp [preference]
        simp only [fiveProjectPhysicalSuffixPreference]
        change fiveProjectEntrepreneurPrefers
          (fiveProjectProgramEndEntrepreneurOutcome project (.bundle b₁))
          (fiveProjectProgramEndEntrepreneurOutcome project (.bundle b₂))
        unfold fiveProjectEntrepreneurPrefers
        exact Or.inl hcollateral
      · have hfocus : SubjectiveTeleologicalDominates finiteProgramEndRequirement
            (fun ending : suffix.program.End =>
              0 < finiteProgramEndRequirement ending fiveProjectMoneyGood ∧
              ∀ means, means ≠ fiveProjectMoneyGood →
                finiteProgramEndRequirement ending means = 0) b₁ b₂ := by
          rw [fiveProjectPhysicalSuffixValuedEnd_other suffix.program project actor
            hborrower moment history] at hdominates
          exact hdominates
        have hmoney := subjective_teleological_focus_good_increases
          finiteProgramEndRequirement fiveProjectMoneyGood b₁ b₂ (by
            exact hfocus)
        dsimp [preference]
        by_cases hhousehold : actor = fiveProjectHousehold
        · have hhouseholdNotBorrower :
              fiveProjectHousehold ≠ fiveProjectPhysicalBorrower project := by
            intro heq
            exact hborrower (hhousehold.trans heq)
          subst actor
          simp only [fiveProjectPhysicalSuffixPreference,
            ite_eq_right hhouseholdNotBorrower]
          change fiveProjectHouseholdPrefers
            (fiveProjectProgramEndHouseholdOutcome suffix.program (.bundle b₁))
            (fiveProjectProgramEndHouseholdOutcome suffix.program (.bundle b₂))
          apply fiveProjectHouseholdPrefers_of_more_money_same_services
          · rfl
          · exact hmoney
        · simp only [fiveProjectPhysicalSuffixPreference,
            ite_eq_right hborrower, ite_eq_right hhousehold]
          change finiteProgramEndRequirement (.bundle b₁) fiveProjectMoneyGood >
            finiteProgramEndRequirement (.bundle b₂) fiveProjectMoneyGood
          simpa [finiteProgramEndRequirement] using hmoney)
  exact base

noncomputable def fiveProjectPhysicalSuffixBehavior
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run) (project : Fin 5) :
    suffix.program.ActionFrameBehavior := by
  classical
  let instruction :=
    (fiveProjectPhysicalRegimeGenerator D).instruction run.cursor run.state
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let continueWith := fun profile =>
    physicalProfileGeneratorHistory fiveProjectPhysicalOperations
      (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
      (fiveProjectNextCursor D run.cursor run.state ⟨instruction, profile⟩)
      (stage.advance profile)
  exact (fiveProjectPhysicalSuffixBaseBehavior suffix project).withRootContinuation
    continueWith

theorem fiveProjectPhysicalSuffixBehavior_selectedHistory_root
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run) (project : Fin 5)
    (actor : FiveProjectPhysicalAgent)
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation) (history : suffix.program.History)
    (hmenu : action ∈ (FiniteEconomyProgram.ProgramMoment.root.currentStage
      (program := suffix.program.toFiniteEconomyProgram)).menu actor) :
    (fiveProjectPhysicalSuffixBehavior suffix project).selectedHistory
      actor FiniteEconomyProgram.ProgramMoment.root action history =
    history.selectActorAtRootWithContinuation actor action hmenu
      (fun profile =>
        physicalProfileGeneratorHistory fiveProjectPhysicalOperations
          (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
          (fiveProjectNextCursor D run.cursor run.state
        ⟨(fiveProjectPhysicalRegimeGenerator D).instruction run.cursor run.state,
          profile⟩)
      ((((fiveProjectPhysicalRegimeGenerator D).instruction run.cursor run.state).stage
            fiveProjectPhysicalOperations run.state).advance profile)) := by
  classical
  let instruction :=
    (fiveProjectPhysicalRegimeGenerator D).instruction run.cursor run.state
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let continueWith := fun profile =>
    physicalProfileGeneratorHistory fiveProjectPhysicalOperations
      (fiveProjectPhysicalRegimeGenerator D) suffix.fuel
      (fiveProjectNextCursor D run.cursor run.state ⟨instruction, profile⟩)
      (stage.advance profile)
  have hphysicalMenu : action ∈ stage.choices.menu actor := by
    change action ∈ stage.choices.menu actor at hmenu
    exact hmenu
  have hselected :
      (fiveProjectPhysicalSuffixBehavior suffix project).selectedHistory
        actor FiniteEconomyProgram.ProgramMoment.root action history =
      history.selectActorAtRootWithContinuation actor action hphysicalMenu continueWith := by
    change ((fiveProjectPhysicalSuffixBaseBehavior suffix project).withRootContinuation
      continueWith).selectedHistory actor FiniteEconomyProgram.ProgramMoment.root
        action history = _
    exact FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation_selectedHistory_root
      (fiveProjectPhysicalSuffixBaseBehavior suffix project) continueWith
      actor action history hphysicalMenu
  rw [hselected]

/-- The branch-sensitive behavioral specification on a physical suffix
compiled into the common ActionFrame interface. -/
@[instance_reducible] noncomputable def fiveProjectPhysicalSuffixActionFrame
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run) (project : Fin 5) : ActionFrame :=
  suffix.program.toActionFrame fiveProjectPhysicalOperations
    (compilePhysicalProfileGenerator_stable fiveProjectPhysicalOperations
      (fiveProjectPhysicalRegimeGenerator D) (suffix.fuel + 1)
      run.cursor run.state)
    (fiveProjectPhysicalSuffixBehavior suffix project)

theorem fiveProjectRunStep_preservesSchedule
    (D : FiveProjectRegimeData) (run : FiveProjectPhysicalRun)
    (hschedule : run.cursor.preservesSchedule) :
    (fiveProjectRunStep D true run).cursor.preservesSchedule := by
  let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let profile : stage.choices.Profile :=
    instruction.selectedProfile fiveProjectPhysicalOperations run.state
  change (fiveProjectNextCursor D run.cursor run.state ⟨instruction, profile⟩).preservesSchedule
  exact fiveProjectNextCursor_preserves_schedule D run.cursor run.state
    ⟨instruction, profile⟩ hschedule

theorem fiveProjectRunUntilPhaseFuel_preservesSchedule
    (D : FiveProjectRegimeData) (target : FiveProjectPhysicalPhase) :
    ∀ fuel run, run.cursor.preservesSchedule →
      (fiveProjectRunUntilPhaseFuel D target fuel run).cursor.preservesSchedule := by
  intro fuel
  induction fuel with
  | zero =>
      intro run hschedule
      exact hschedule
  | succ fuel ih =>
      intro run hschedule
      unfold fiveProjectRunUntilPhaseFuel
      cases hphases : run.cursor.remainingPhases with
      | nil => exact hschedule
      | cons phase rest =>
          by_cases htarget : phase = target
          · simp only [ite_eq_left htarget]
            exact hschedule
          · simp only [ite_eq_right htarget]
            exact ih _ (fiveProjectRunStep_preservesSchedule D run hschedule)

theorem fiveProjectRunUntilPhase_preservesSchedule
    (D : FiveProjectRegimeData) (target : FiveProjectPhysicalPhase)
    (run : FiveProjectPhysicalRun) (hschedule : run.cursor.preservesSchedule) :
    (fiveProjectRunUntilPhase D target run).cursor.preservesSchedule := by
  unfold fiveProjectRunUntilPhase
  exact fiveProjectRunUntilPhaseFuel_preservesSchedule D target
    run.cursor.remainingPhases.length run hschedule

theorem fiveProjectPhysicalPhases_contains_loan_acceptance (project : Fin 5) :
    FiveProjectPhysicalPhase.loanAcceptance project ∈ fiveProjectPhysicalPhases := by
  fin_cases project <;> decide

def fiveProjectFourFactorForecastAcceptancePrefix (project : Fin 5) :
    FiveProjectPhysicalRun :=
  fiveProjectRunUntilPhase fiveProjectFourFactorForecastData
    (.loanAcceptance project)
    (fiveProjectInitialRun fiveProjectFourFactorForecastData)

theorem fiveProjectFourFactorForecastAcceptancePrefix_at_phase (project : Fin 5) :
    (fiveProjectFourFactorForecastAcceptancePrefix project).cursor.remainingPhases.head? =
      some (.loanAcceptance project) := by
  apply fiveProjectRunUntilPhase_reaches_head
  · change fiveProjectPhysicalPhases.Nodup
    exact fiveProjectPhysicalPhases_nodup
  · exact fiveProjectPhysicalPhases_contains_loan_acceptance project

theorem fiveProjectFourFactorForecastAcceptancePrefix_preservesSchedule
    (project : Fin 5) :
    (fiveProjectFourFactorForecastAcceptancePrefix project).cursor.preservesSchedule := by
  apply fiveProjectRunUntilPhase_preservesSchedule
  · exact fiveProjectInitialCursor_preserves_schedule _

def fiveProjectFourFactorForecastAcceptanceSuffix (project : Fin 5) :
    FiveProjectPhysicalSuffix fiveProjectFourFactorForecastData
      (fiveProjectFourFactorForecastAcceptancePrefix project) := by
  apply fiveProjectPhysicalSuffix
  intro hnil
  have hhead := fiveProjectFourFactorForecastAcceptancePrefix_at_phase project
  simp [hnil] at hhead

theorem fiveProjectPhysicalSuffixAction_end_moment_is_terminal
    {D : FiveProjectRegimeData} {run : FiveProjectPhysicalRun}
    (suffix : FiveProjectPhysicalSuffix D run) (project : Fin 5)
    (actor : FiveProjectPhysicalAgent) (moment : suffix.program.Moment)
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation) :
    let selectedHistory := suffix.program.selectByBehavior
      (fiveProjectPhysicalSuffixBehavior suffix project) actor moment action
      ((fiveProjectPhysicalSuffixBehavior suffix project).referenceHistory actor moment)
    suffix.program.expectedMaturation
      (fiveProjectPhysicalSuffixBehavior suffix project) actor moment action selectedHistory =
      selectedHistory.terminalMoment := by
  simp [FinitePhysicalEconomyProgram.expectedMaturation,
    FinitePhysicalEconomyProgram.horizonMoment,
    fiveProjectPhysicalSuffixBehavior,
    fiveProjectPhysicalSuffixBaseBehavior,
    FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
    FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory,
    FinitePhysicalEconomyProgram.terminalSettlementHorizon]

/-- Full generated suffix at the household's plan decision in the named
household-transfer regime. -/
def fiveProjectHouseholdSavingSuffix :
    FiveProjectPhysicalSuffix (fiveProjectRegimeData .householdTransfer)
      (fiveProjectInitialRun (fiveProjectRegimeData .householdTransfer)) := by
  apply fiveProjectPhysicalSuffix
  intro hnil
  have hhead : (fiveProjectInitialRun
      (fiveProjectRegimeData .householdTransfer)).cursor.remainingPhases.head? =
        some .chooseHouseholdPlan := by
    decide
  simp [hnil] at hhead

def fiveProjectHouseholdSavingAction :
    EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  .operate (.chooseHouseholdPlan
    (fiveProjectHouseholdPlanOf (fiveProjectRegimeData .householdTransfer)))

@[instance_reducible] noncomputable def fiveProjectHouseholdSavingActionFrame : ActionFrame :=
  fiveProjectPhysicalSuffixActionFrame fiveProjectHouseholdSavingSuffix 0

theorem fiveProjectHouseholdSavingAction_selected :
    FiniteEconomyProgram.ProgramHistory.enactedAt
      fiveProjectHouseholdSavingSuffix.selectedHistory
      FiniteEconomyProgram.ProgramMoment.root fiveProjectHousehold =
      fiveProjectHouseholdSavingAction := by
  simp [FiniteEconomyProgram.ProgramHistory.enactedAt,
    FiveProjectPhysicalSuffix.selectedHistory, physicalProfileGeneratorHistory,
    fiveProjectPhysicalRegimeGenerator, fiveProjectPhysicalInstruction,
    fiveProjectHouseholdSavingSuffix, fiveProjectInitialRun,
    fiveProjectInitialCursor, fiveProjectPhysicalPhases,
    fiveProjectHouseholdSavingAction, fiveProjectHouseholdPlanInstruction,
    fiveProjectHouseholdPlanChoiceActions, fiveProjectHouseholdPlanOf,
    PhysicalProfileInstruction.selectedProfile,
    PhysicalProfileInstruction.affordableProfile,
    actionAffordable, rawActionUse, fiveProjectPhysicalOperations]

theorem fiveProjectHouseholdSavingAction_mem_root_menu :
    fiveProjectHouseholdSavingAction ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := fiveProjectHouseholdSavingSuffix.program.toFiniteEconomyProgram)).menu
        fiveProjectHousehold := by
  have hmenu := FiniteEconomyProgram.ProgramHistory.enactedAt_root_mem_menu
    fiveProjectHouseholdSavingSuffix.selectedHistory fiveProjectHousehold
  rw [fiveProjectHouseholdSavingAction_selected] at hmenu
  exact hmenu

theorem fiveProjectHouseholdSavingAction_feasible :
    fiveProjectHouseholdSavingAction ∈ fiveProjectHouseholdSavingActionFrame.A_feas
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
      fiveProjectHouseholdSavingSuffix.selectedHistory := by
  let suffix := fiveProjectHouseholdSavingSuffix
  change fiveProjectHouseholdSavingAction ∈ feasibleMenu
    fiveProjectPhysicalOperations (suffix.program.stateAt
      FiniteEconomyProgram.ProgramMoment.root) fiveProjectHousehold
      ((FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu fiveProjectHousehold)
  have hmenu := fiveProjectHouseholdSavingAction_mem_root_menu
  apply (mem_feasibleMenu_iff fiveProjectPhysicalOperations
    (suffix.program.stateAt FiniteEconomyProgram.ProgramMoment.root)
    fiveProjectHousehold
    ((FiniteEconomyProgram.ProgramMoment.root.currentStage
      (program := suffix.program.toFiniteEconomyProgram)).menu fiveProjectHousehold)
    fiveProjectHouseholdSavingAction).2
  refine ⟨hmenu, ?_⟩
  intro good
  simp [rawActionUse, fiveProjectHouseholdSavingAction,
    fiveProjectPhysicalOperations]

theorem fiveProjectHouseholdSavingAction_executes :
    @Exec fiveProjectHouseholdSavingActionFrame fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root fiveProjectHouseholdSavingAction
      fiveProjectHouseholdSavingSuffix.selectedHistory := by
  change FiniteEconomyProgram.ProgramMoment.memHist
      fiveProjectHouseholdSavingSuffix.program.toFiniteEconomyProgram
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectHouseholdSavingSuffix.selectedHistory ∧
    FiniteEconomyProgram.ProgramHistory.enactedAt
      fiveProjectHouseholdSavingSuffix.selectedHistory
      FiniteEconomyProgram.ProgramMoment.root fiveProjectHousehold =
      fiveProjectHouseholdSavingAction
  exact ⟨FiniteEconomyProgram.ProgramMoment.root_memHist _,
    fiveProjectHouseholdSavingAction_selected⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
-- The suffix contains all scheduled transitions, and the terminal inventory
-- comparison reduces those transitions through the physical interpreter.
theorem fiveProjectHouseholdSavingAction_terminal_money :
    finiteProgramEndRequirement
      (fiveProjectHouseholdSavingSuffix.program.intendedEnd
        (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
        fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
        fiveProjectHouseholdSavingAction)
      fiveProjectMoneyGood = 5 := by
  let behavior := fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0
  have hmenu := fiveProjectHouseholdSavingAction_mem_root_menu
  have hcenter : behavior.selectedHistory fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root fiveProjectHouseholdSavingAction
      fiveProjectHouseholdSavingSuffix.selectedHistory =
        fiveProjectHouseholdSavingSuffix.selectedHistory := by
    exact behavior.selectedHistory_centered fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root fiveProjectHouseholdSavingAction
      fiveProjectHouseholdSavingSuffix.selectedHistory
      (FiniteEconomyProgram.ProgramMoment.root_memHist _)
      hmenu fiveProjectHouseholdSavingAction_selected
  have hterminal : fiveProjectHouseholdSavingSuffix.program.expectedMaturation
      behavior fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
      fiveProjectHouseholdSavingAction fiveProjectHouseholdSavingSuffix.selectedHistory =
        fiveProjectHouseholdSavingSuffix.selectedHistory.terminalMoment := by
    simp [behavior, FinitePhysicalEconomyProgram.expectedMaturation,
      FinitePhysicalEconomyProgram.horizonMoment,
      fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory,
      FinitePhysicalEconomyProgram.terminalSettlementHorizon]
  have href :
      (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0).referenceHistory
          fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root =
        fiveProjectHouseholdSavingSuffix.selectedHistory := by
    simp [fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  change finiteProgramEndRequirement
    (fiveProjectHouseholdSavingSuffix.program.intendedEnd
      (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
      fiveProjectHouseholdSavingAction) fiveProjectMoneyGood = 5
  rw [fiveProjectHouseholdSavingSuffix.program.intendedEnd_uses_behavior_selected_history
    (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
    fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
    fiveProjectHouseholdSavingAction hmenu]
  rw [href, hcenter, hterminal]
  simp only [finiteProgramEndRequirement, FinitePhysicalEconomyProgram.outcomeAt]
  rw [FinitePhysicalEconomyProgram.stateAt_terminalMoment]
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
-- The counterfactual idling branch runs the same remaining physical schedule.
theorem fiveProjectHouseholdIdleAction_terminal_money :
    finiteProgramEndRequirement
      (fiveProjectHouseholdSavingSuffix.program.intendedEnd
        (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
        fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
        EconomyAction.idle)
      fiveProjectMoneyGood = 2 := by
  let behavior := fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0
  have href : behavior.referenceHistory fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root =
        fiveProjectHouseholdSavingSuffix.selectedHistory := by
    simp [behavior, fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  let hmenu := (FiniteEconomyProgram.ProgramMoment.root.currentStage
    (program := fiveProjectHouseholdSavingSuffix.program.toFiniteEconomyProgram)).idle_mem
    fiveProjectHousehold
  let idleHistory := (fiveProjectHouseholdSavingSuffix.selectedHistory
    ).selectActorAtRootWithContinuation fiveProjectHousehold EconomyAction.idle
      hmenu
      (fun profile => physicalProfileGeneratorHistory fiveProjectPhysicalOperations
        (fiveProjectPhysicalRegimeGenerator
          (fiveProjectRegimeData FiveProjectRegime.householdTransfer))
        fiveProjectHouseholdSavingSuffix.fuel
        (fiveProjectNextCursor
          (fiveProjectRegimeData FiveProjectRegime.householdTransfer)
          (fiveProjectInitialRun
            (fiveProjectRegimeData FiveProjectRegime.householdTransfer)).cursor
          (fiveProjectInitialRun
            (fiveProjectRegimeData FiveProjectRegime.householdTransfer)).state
          { instruction := fiveProjectPhysicalInstruction
              (fiveProjectRegimeData FiveProjectRegime.householdTransfer)
              (fiveProjectInitialRun
                (fiveProjectRegimeData FiveProjectRegime.householdTransfer)).cursor
              (fiveProjectInitialRun
                (fiveProjectRegimeData FiveProjectRegime.householdTransfer)).state,
            profile := profile })
        ((PhysicalProfileInstruction.stage fiveProjectPhysicalOperations
          (fiveProjectInitialRun
            (fiveProjectRegimeData FiveProjectRegime.householdTransfer)).state
          (fiveProjectPhysicalInstruction
            (fiveProjectRegimeData FiveProjectRegime.householdTransfer)
            (fiveProjectInitialRun
              (fiveProjectRegimeData FiveProjectRegime.householdTransfer)).cursor
            (fiveProjectInitialRun
              (fiveProjectRegimeData FiveProjectRegime.householdTransfer)).state)).advance
          profile))
  have hselected : behavior.selectedHistory fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle
      fiveProjectHouseholdSavingSuffix.selectedHistory = idleHistory := by
    change (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0).selectedHistory
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle
      fiveProjectHouseholdSavingSuffix.selectedHistory = idleHistory
    exact fiveProjectPhysicalSuffixBehavior_selectedHistory_root
      fiveProjectHouseholdSavingSuffix 0 fiveProjectHousehold EconomyAction.idle
      fiveProjectHouseholdSavingSuffix.selectedHistory hmenu
  have hhorizon : behavior.evaluationHorizon fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle =
        .terminalSettlement := by
    simp [behavior, fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  have hterminal : fiveProjectHouseholdSavingSuffix.program.expectedMaturation
      behavior fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
      EconomyAction.idle idleHistory = idleHistory.terminalMoment := by
    change fiveProjectHouseholdSavingSuffix.program.horizonMoment
      (behavior.evaluationHorizon fiveProjectHousehold
        FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle)
      FiniteEconomyProgram.ProgramMoment.root idleHistory = idleHistory.terminalMoment
    rw [hhorizon]
    rfl
  change finiteProgramEndRequirement
    (fiveProjectHouseholdSavingSuffix.program.intendedEnd
      (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
      fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
    EconomyAction.idle) fiveProjectMoneyGood = 2
  rw [fiveProjectHouseholdSavingSuffix.program.intendedEnd_uses_behavior_selected_history
    (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
    fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
    EconomyAction.idle
    hmenu]
  rw [href, hselected, hterminal]
  simp only [finiteProgramEndRequirement, FinitePhysicalEconomyProgram.outcomeAt]
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
-- This comparison uses terminal outcomes computed through the two physical
-- histories and the household's fixed lexicographic preference.
theorem fiveProjectHouseholdSavingAction_beats_idle :
    fiveProjectHouseholdSavingActionFrame.Preference fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectHouseholdSavingSuffix.selectedHistory
      (fiveProjectHouseholdSavingActionFrame.End_of fiveProjectHousehold
        fiveProjectHouseholdSavingAction FiniteEconomyProgram.ProgramMoment.root
        fiveProjectHouseholdSavingSuffix.selectedHistory)
      (fiveProjectHouseholdSavingActionFrame.End_of fiveProjectHousehold
        EconomyAction.idle FiniteEconomyProgram.ProgramMoment.root
        fiveProjectHouseholdSavingSuffix.selectedHistory) := by
  change fiveProjectHouseholdPrefers
    (fiveProjectProgramEndHouseholdOutcome fiveProjectHouseholdSavingSuffix.program
      (fiveProjectHouseholdSavingSuffix.program.intendedEnd
        (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
        fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
        fiveProjectHouseholdSavingAction))
    (fiveProjectProgramEndHouseholdOutcome fiveProjectHouseholdSavingSuffix.program
      (fiveProjectHouseholdSavingSuffix.program.intendedEnd
        (fiveProjectPhysicalSuffixBehavior fiveProjectHouseholdSavingSuffix 0)
        fiveProjectHousehold FiniteEconomyProgram.ProgramMoment.root
        EconomyAction.idle))
  unfold fiveProjectHouseholdPrefers fiveProjectHouseholdPreferenceRank
  simp only [fiveProjectProgramEndHouseholdOutcome]
  simp [fiveProjectHouseholdSavingAction_terminal_money,
    fiveProjectHouseholdIdleAction_terminal_money]

/-- Reach a named loan-acceptance decision in the actual fiduciary-expansion
run. The cursor phase, rather than a numeric offset, identifies the node. -/
def fiveProjectFiduciaryAcceptancePrefix (project : Fin 5) :
    FiveProjectPhysicalRun :=
  fiveProjectRunUntilPhase (fiveProjectRegimeData .fiduciaryExpansion)
    (.loanAcceptance project)
    (fiveProjectInitialRun (fiveProjectRegimeData .fiduciaryExpansion))

theorem fiveProjectFiduciaryAcceptancePrefix_at_phase (project : Fin 5) :
    (fiveProjectFiduciaryAcceptancePrefix project).cursor.remainingPhases.head? =
      some (.loanAcceptance project) := by
  apply fiveProjectRunUntilPhase_reaches_head
  · change fiveProjectPhysicalPhases.Nodup
    exact fiveProjectPhysicalPhases_nodup
  · exact fiveProjectPhysicalPhases_contains_loan_acceptance project

/-- Compiled suffix at one actual borrower's published acceptance node. -/
def fiveProjectFiduciaryAcceptanceSuffix (project : Fin 5) :
    FiveProjectPhysicalSuffix (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectFiduciaryAcceptancePrefix project) := by
  apply fiveProjectPhysicalSuffix
  intro hnil
  have hhead := fiveProjectFiduciaryAcceptancePrefix_at_phase project
  simp [hnil] at hhead

def fiveProjectProjectTwoAcceptanceSuffix :=
  fiveProjectFiduciaryAcceptanceSuffix 2

def fiveProjectProjectTwoAcceptanceAction :
    EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  .accept (fiveProjectPhysicalBorrower 2) fiveProjectBank
    fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
    (fiveProjectCollateralGood 2)

@[instance_reducible] noncomputable def fiveProjectProjectTwoAcceptanceFrame : ActionFrame :=
  fiveProjectPhysicalSuffixActionFrame fiveProjectProjectTwoAcceptanceSuffix 2

set_option maxRecDepth 4096 in
/-- The named direct-run four-factor forecast and the actual expansion path
show the borrower the same current cash, collateral, and published quote at
project two's acceptance node. Their differing household resource plan is
not included in this actor's observation. -/
theorem fiveProjectProjectTwoForecast_preserves_observed_local_data :
    (fiveProjectFiduciaryAcceptancePrefix 2).state.stock
        (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood =
      (fiveProjectFourFactorForecastAcceptancePrefix 2).state.stock
        (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood ∧
    (fiveProjectFiduciaryAcceptancePrefix 2).state.stock
        (fiveProjectPhysicalBorrower 2) (fiveProjectCollateralGood 2) =
      (fiveProjectFourFactorForecastAcceptancePrefix 2).state.stock
        (fiveProjectPhysicalBorrower 2) (fiveProjectCollateralGood 2) ∧
    (fiveProjectFiduciaryAcceptancePrefix 2).cursor.loanQuote =
      (fiveProjectFourFactorForecastAcceptancePrefix 2).cursor.loanQuote ∧
    (fiveProjectFiduciaryAcceptancePrefix 2).state.stock
        fiveProjectHousehold fiveProjectCompletionGood = 2 ∧
    (fiveProjectFourFactorForecastAcceptancePrefix 2).state.stock
        fiveProjectHousehold fiveProjectCompletionGood = 2 := by
  decide

/-- The subjective forecast observes only the entrepreneur's local cash and
collateral and the published repayment quote. It deliberately leaves later
aggregate household factor use outside that observation. -/
structure FiveProjectProjectTwoLoanObservation where
  borrowerMoney : ℕ
  borrowerCollateral : ℕ
  publishedRepayment : Option ℕ
  deriving DecidableEq, Repr

def fiveProjectProjectTwoLoanObservationAt
    (moment : fiveProjectProjectTwoAcceptanceSuffix.program.Moment) :
    FiveProjectProjectTwoLoanObservation :=
  { borrowerMoney := moment.currentState.stock
      (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood
    borrowerCollateral := moment.currentState.stock
      (fiveProjectPhysicalBorrower 2) (fiveProjectCollateralGood 2)
    publishedRepayment := some 4 }

structure FiveProjectProjectTwoForecastScenario where
  moment : fiveProjectProjectTwoAcceptanceSuffix.program.Moment
  history : fiveProjectProjectTwoAcceptanceSuffix.program.History
  incident : fiveProjectProjectTwoAcceptanceFrame.mem_hist moment history
  observation : FiveProjectProjectTwoLoanObservation
  fourFactorForecast : Bool

noncomputable def fiveProjectProjectTwoScenarioMenu
    (actor : FiveProjectPhysicalAgent)
    (scenario : FiveProjectProjectTwoForecastScenario) :
    Finset (EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation) :=
  fiveProjectProjectTwoAcceptanceFrame.A_feas actor scenario.moment scenario.history

noncomputable def fiveProjectProjectTwoScenarioEnd (actor : FiveProjectPhysicalAgent)
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation)
    (scenario : FiveProjectProjectTwoForecastScenario) :
    fiveProjectProjectTwoAcceptanceFrame.Ends := by
  if hforecast : scenario.fourFactorForecast ∧
      actor = fiveProjectPhysicalBorrower 2 then
    if haccept : action = fiveProjectProjectTwoAcceptanceAction then
      exact .bundle (fiveProjectFourFactorForecastRun.state.stock actor)
    else if hidle : action = EconomyAction.idle then
      exact .bundle ((fiveProjectFourFactorForecastDeclineRun 2).state.stock actor)
    else
      exact fiveProjectProjectTwoAcceptanceFrame.End_of actor action
        scenario.moment scenario.history
  else
    exact fiveProjectProjectTwoAcceptanceFrame.End_of actor action
      scenario.moment scenario.history

noncomputable def fiveProjectProjectTwoForecastScenarioAt
    (actor : FiveProjectPhysicalAgent)
    (moment : fiveProjectProjectTwoAcceptanceSuffix.program.Moment)
    (observation : FiveProjectProjectTwoLoanObservation) :
    FiveProjectProjectTwoForecastScenario :=
  { moment := moment
    history := fiveProjectPhysicalSuffixReferenceHistory
      fiveProjectProjectTwoAcceptanceSuffix actor moment
    incident := fiveProjectPhysicalSuffixReferenceHistory_mem
      fiveProjectProjectTwoAcceptanceSuffix actor moment
    observation := observation
    fourFactorForecast := decide
      (actor = fiveProjectPhysicalBorrower 2 ∧
        moment = FiniteEconomyProgram.ProgramMoment.root) }

noncomputable def fiveProjectProjectTwoActualScenario
    (actor : FiveProjectPhysicalAgent)
    (moment : fiveProjectProjectTwoAcceptanceSuffix.program.Moment)
    (history : fiveProjectProjectTwoAcceptanceSuffix.program.History) :
    FiveProjectProjectTwoForecastScenario := by
  classical
  exact if hmem : fiveProjectProjectTwoAcceptanceFrame.mem_hist moment history then
    { moment := moment
      history := history
      incident := hmem
      observation := fiveProjectProjectTwoLoanObservationAt moment
      fourFactorForecast := false }
  else
    { moment := moment
      history := fiveProjectPhysicalSuffixReferenceHistory
        fiveProjectProjectTwoAcceptanceSuffix actor moment
      incident := fiveProjectPhysicalSuffixReferenceHistory_mem
        fiveProjectProjectTwoAcceptanceSuffix actor moment
      observation := fiveProjectProjectTwoLoanObservationAt moment
      fourFactorForecast := false }

noncomputable def fiveProjectProjectTwoForecastEconomy :
    SingletonForecastEconomy fiveProjectProjectTwoAcceptanceFrame where
  Scenario := FiveProjectProjectTwoForecastScenario
  Observation := FiveProjectProjectTwoLoanObservation
  scenarioAnchor := FiveProjectProjectTwoForecastScenario.moment
  scenarioMenu := fiveProjectProjectTwoScenarioMenu
  scenarioEnd := fiveProjectProjectTwoScenarioEnd
  observeActual _ moment _ := fiveProjectProjectTwoLoanObservationAt moment
  observeScenario _ scenario := scenario.observation
  forecastScenario := fiveProjectProjectTwoForecastScenarioAt
  forecast_anchored _ _ _ := rfl
  forecast_matches_observation _ _ _ := rfl
  forecast_menu_covers actor moment history hmem := by
    let forecast := fiveProjectProjectTwoForecastScenarioAt actor moment
      (fiveProjectProjectTwoLoanObservationAt moment)
    have hmenu := fiveProjectProjectTwoAcceptanceFrame.A_feas_bundle_invariant
      actor moment hmem forecast.incident
    change fiveProjectProjectTwoAcceptanceFrame.A_feas actor moment history ⊆
      fiveProjectProjectTwoAcceptanceFrame.A_feas actor forecast.moment forecast.history
    rw [hmenu]
    exact Finset.Subset.rfl
  observation_shared_at_decision _ _ _ _ _ _ := rfl
  actualScenario := fiveProjectProjectTwoActualScenario
  actual_scenario_anchored _ moment history hmem := by
    simp [fiveProjectProjectTwoActualScenario, hmem]
  actual_scenario_observation _ moment history hmem := by
    simp [fiveProjectProjectTwoActualScenario, hmem]
  actual_scenario_end _ moment history action hmem := by
    simp [fiveProjectProjectTwoScenarioEnd,
      fiveProjectProjectTwoActualScenario, hmem]

noncomputable def fiveProjectProjectTwoSubjectiveFrame :
    SubjectiveScenarioFrame fiveProjectProjectTwoAcceptanceFrame :=
  singletonForecastScenarioFrame fiveProjectProjectTwoForecastEconomy

theorem fiveProjectProjectTwoSubjectiveFrame_forecast_is_singleton :
    fiveProjectProjectTwoSubjectiveFrame.MinPlausible
      (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root =
      { fiveProjectProjectTwoForecastEconomy.forecastScenario
          (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
          (fiveProjectProjectTwoForecastEconomy.observeActual
            (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
            (Classical.choose
              (fiveProjectProjectTwoAcceptanceFrame.moment_in_history
                FiniteEconomyProgram.ProgramMoment.root))) } := by
  ext scenario
  exact Iff.rfl

set_option maxRecDepth 8192 in
theorem fiveProjectProjectTwoAcceptanceAction_selected :
    FiniteEconomyProgram.ProgramHistory.enactedAt
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
      FiniteEconomyProgram.ProgramMoment.root (fiveProjectPhysicalBorrower 2) =
      fiveProjectProjectTwoAcceptanceAction := by
  decide

theorem fiveProjectProjectTwoAcceptanceAction_feasible :
    fiveProjectProjectTwoAcceptanceAction ∈
      fiveProjectProjectTwoAcceptanceFrame.A_feas
        (fiveProjectPhysicalBorrower 2)
        FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory := by
  let suffix := fiveProjectProjectTwoAcceptanceSuffix
  change fiveProjectProjectTwoAcceptanceAction ∈ feasibleMenu
    fiveProjectPhysicalOperations (suffix.program.stateAt
      FiniteEconomyProgram.ProgramMoment.root) (fiveProjectPhysicalBorrower 2)
      ((FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu
        (fiveProjectPhysicalBorrower 2))
  have hmenu := FiniteEconomyProgram.ProgramHistory.enactedAt_root_mem_menu
    suffix.selectedHistory (fiveProjectPhysicalBorrower 2)
  rw [fiveProjectProjectTwoAcceptanceAction_selected] at hmenu
  apply (mem_feasibleMenu_iff fiveProjectPhysicalOperations
    (suffix.program.stateAt FiniteEconomyProgram.ProgramMoment.root)
    (fiveProjectPhysicalBorrower 2)
    ((FiniteEconomyProgram.ProgramMoment.root.currentStage
      (program := suffix.program.toFiniteEconomyProgram)).menu
      (fiveProjectPhysicalBorrower 2))
    fiveProjectProjectTwoAcceptanceAction).2
  refine ⟨hmenu, ?_⟩
  intro good
  by_cases hgood : good = fiveProjectCollateralGood 2
  · subst good
    change 1 ≤ (fiveProjectFiduciaryAcceptancePrefix 2).state.stock
      (fiveProjectPhysicalBorrower 2) (fiveProjectCollateralGood 2)
    decide
  · simp only [rawActionUse, fiveProjectProjectTwoAcceptanceAction,
      fiveProjectLoanMarket, ite_eq_right hgood]
    exact Nat.zero_le _

theorem fiveProjectProjectTwoAcceptanceAction_executes :
    @Exec fiveProjectProjectTwoAcceptanceFrame
      (fiveProjectPhysicalBorrower 2)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceAction
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory := by
  change FiniteEconomyProgram.ProgramMoment.memHist
      fiveProjectProjectTwoAcceptanceSuffix.program.toFiniteEconomyProgram
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory ∧
    FiniteEconomyProgram.ProgramHistory.enactedAt
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
      FiniteEconomyProgram.ProgramMoment.root (fiveProjectPhysicalBorrower 2) =
        fiveProjectProjectTwoAcceptanceAction
  exact ⟨FiniteEconomyProgram.ProgramMoment.root_memHist _,
    fiveProjectProjectTwoAcceptanceAction_selected⟩

theorem fiveProjectProjectTwoForecast_accept_end :
    fiveProjectProjectTwoSubjectiveFrame.IntendedEnd
      (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
      fiveProjectProjectTwoAcceptanceAction =
    .bundle (fiveProjectFourFactorForecastRun.state.stock
      (fiveProjectPhysicalBorrower 2)) := by
  simp [SubjectiveScenarioFrame.IntendedEnd,
    fiveProjectProjectTwoSubjectiveFrame,
    singletonForecastScenarioFrame,
    fiveProjectProjectTwoForecastEconomy,
    fiveProjectProjectTwoForecastScenarioAt,
    fiveProjectProjectTwoScenarioEnd,
    fiveProjectProjectTwoLoanObservationAt,
    fiveProjectProjectTwoAcceptanceAction]

theorem fiveProjectProjectTwoForecast_idle_end :
    fiveProjectProjectTwoSubjectiveFrame.IntendedEnd
      (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory EconomyAction.idle =
    .bundle ((fiveProjectFourFactorForecastDeclineRun 2).state.stock
      (fiveProjectPhysicalBorrower 2)) := by
  simp [SubjectiveScenarioFrame.IntendedEnd,
    fiveProjectProjectTwoSubjectiveFrame,
    singletonForecastScenarioFrame,
    fiveProjectProjectTwoForecastEconomy,
    fiveProjectProjectTwoForecastScenarioAt,
    fiveProjectProjectTwoScenarioEnd,
    fiveProjectProjectTwoLoanObservationAt,
    fiveProjectProjectTwoAcceptanceAction]

set_option maxRecDepth 16384 in
theorem fiveProjectProjectTwoForecast_accept_improves_on_idle :
    fiveProjectProjectTwoAcceptanceFrame.Preference
      (fiveProjectPhysicalBorrower 2)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
      (fiveProjectProjectTwoSubjectiveFrame.IntendedEnd
        (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
        fiveProjectProjectTwoAcceptanceAction)
      (fiveProjectProjectTwoSubjectiveFrame.IntendedEnd
        (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory EconomyAction.idle) := by
  rw [fiveProjectProjectTwoForecast_accept_end,
    fiveProjectProjectTwoForecast_idle_end]
  let acceptEnd : fiveProjectProjectTwoAcceptanceSuffix.program.End :=
    .bundle (fiveProjectFourFactorForecastRun.state.stock
      (fiveProjectPhysicalBorrower 2))
  let idleEnd : fiveProjectProjectTwoAcceptanceSuffix.program.End :=
    .bundle ((fiveProjectFourFactorForecastDeclineRun 2).state.stock
      (fiveProjectPhysicalBorrower 2))
  change fiveProjectEntrepreneurPrefers
    (fiveProjectProgramEndEntrepreneurOutcome 2 acceptEnd)
    (fiveProjectProgramEndEntrepreneurOutcome 2 idleEnd)
  have haccept :
      fiveProjectProgramEndEntrepreneurOutcome 2 acceptEnd =
        fiveProjectFourFactorForecastRun.entrepreneurOutcome 2 := by
    dsimp [acceptEnd]
    decide
  have hidle :
      fiveProjectProgramEndEntrepreneurOutcome 2 idleEnd =
        (fiveProjectFourFactorForecastDeclineRun 2).entrepreneurOutcome 2 := by
    dsimp [idleEnd]
    decide
  rw [haccept, hidle]
  rcases fiveProject_four_factor_forecast_marginal_entry_improves_on_declining with
    ⟨_, _, _, _, _, _, hpreferTwo, _, _, _, _, _, _, _⟩
  exact hpreferTwo

/-- The borrower faces only the published loan acceptance and idling at the
named acceptance phase. This menu follows from that phase's transfer
instruction; it is not imposed as an appraisal premise. -/
theorem fiveProjectProjectTwoAcceptanceAction_complete_menu
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation)
    (haction : action ∈ fiveProjectProjectTwoAcceptanceFrame.A_feas
      (fiveProjectPhysicalBorrower 2)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory) :
    action = EconomyAction.idle ∨ action = fiveProjectProjectTwoAcceptanceAction := by
  let acceptancePrefix := fiveProjectFiduciaryAcceptancePrefix 2
  let suffix := fiveProjectProjectTwoAcceptanceSuffix
  have hrootMenu : action ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu
          (fiveProjectPhysicalBorrower 2) :=
    (mem_feasibleMenu_iff fiveProjectPhysicalOperations
      (suffix.program.stateAt FiniteEconomyProgram.ProgramMoment.root)
      (fiveProjectPhysicalBorrower 2)
      ((FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu
          (fiveProjectPhysicalBorrower 2)) action).1 haction |>.1
  have hplanned : acceptancePrefix.cursor.plannedAdvances[2]? = some ⟨2, 6⟩ := by
    decide
  have hinstruction : fiveProjectPhysicalInstruction
      (fiveProjectRegimeData .fiduciaryExpansion) acceptancePrefix.cursor
        acceptancePrefix.state =
        fiveProjectAdvanceInstruction ⟨2, 6⟩ := by
    have hphase := fiveProjectFiduciaryAcceptancePrefix_at_phase 2
    change acceptancePrefix.cursor.remainingPhases.head? =
      some (.loanAcceptance 2) at hphase
    cases hremaining : acceptancePrefix.cursor.remainingPhases with
    | nil =>
        simp [hremaining] at hphase
    | cons phase rest =>
        have hphase' : phase = .loanAcceptance 2 := by
          simpa [hremaining] using hphase
        subst phase
        simp [fiveProjectPhysicalInstruction, hremaining, hplanned]
  change action ∈ (fiveProjectPhysicalInstruction
    (fiveProjectRegimeData .fiduciaryExpansion) acceptancePrefix.cursor
      acceptancePrefix.state).stageMenu
      fiveProjectPhysicalOperations acceptancePrefix.state
      (fiveProjectPhysicalBorrower 2) at hrootMenu
  rw [hinstruction, PhysicalProfileInstruction.stageMenu,
    Finset.mem_insert, Finset.mem_insert] at hrootMenu
  rcases hrootMenu with hidle | hscheduled | halt
  · exact Or.inl hidle
  · have hscheduled' : (fiveProjectAdvanceInstruction ⟨2, 6⟩).affordableProfile
        fiveProjectPhysicalOperations acceptancePrefix.state
        (fiveProjectPhysicalBorrower 2) =
          fiveProjectProjectTwoAcceptanceAction := by
      change (if actionAffordable fiveProjectPhysicalOperations acceptancePrefix.state
        (fiveProjectPhysicalBorrower 2)
        (fiveProjectScheduledTransferProfile fiveProjectBank
          (fiveProjectPhysicalBorrower 2) 1 fiveProjectMoneyGood 1
          (fiveProjectCollateralGood 2) (fiveProjectPhysicalBorrower 2))
        then fiveProjectScheduledTransferProfile fiveProjectBank
          (fiveProjectPhysicalBorrower 2) 1 fiveProjectMoneyGood 1
          (fiveProjectCollateralGood 2) (fiveProjectPhysicalBorrower 2)
        else EconomyAction.idle) = fiveProjectProjectTwoAcceptanceAction
      decide
    exact Or.inr (hscheduled'.symm ▸ hscheduled)
  · have hempty :
        (fiveProjectAdvanceInstruction ⟨2, 6⟩).affordableAlternatives
          fiveProjectPhysicalOperations acceptancePrefix.state
          (fiveProjectPhysicalBorrower 2) = ∅ := by
      simp [PhysicalProfileInstruction.affordableAlternatives,
        fiveProjectAdvanceInstruction, fiveProjectTransferInstruction]
    rw [hempty] at halt
    simp at halt

/-- The marginal borrower purposefully accepts under the stated four-factor
forecast. Current feasibility and execution are actual, while improvement and
menu undominatedness are evaluated through the independent forecast scenario.
-/
theorem fiveProjectProjectTwoAcceptanceAction_purposeful :
    fiveProjectProjectTwoSubjectiveFrame.PurposefulAct
      (fiveProjectPhysicalBorrower 2)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
      fiveProjectProjectTwoAcceptanceAction := by
  apply SubjectiveScenarioFrame.purposefulAct_of_appraisal_certificate_subjective
    fiveProjectProjectTwoSubjectiveFrame
  refine ⟨fiveProjectProjectTwoAcceptanceAction_feasible,
    fiveProjectProjectTwoAcceptanceAction_executes, Or.inr ?_, ?_⟩
  · exact fiveProjectProjectTwoForecast_accept_improves_on_idle
  · intro alternative halternative hbetter
    have hmenu := fiveProjectProjectTwoAcceptanceAction_complete_menu
      alternative halternative
    change fiveProjectPhysicalSuffixPreference
      fiveProjectProjectTwoAcceptanceSuffix.program 2
      (fiveProjectPhysicalBorrower 2)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
      (fiveProjectProjectTwoSubjectiveFrame.IntendedEnd
        (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory alternative)
      (fiveProjectProjectTwoSubjectiveFrame.IntendedEnd
        (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
        fiveProjectProjectTwoAcceptanceAction) at hbetter
    rcases hmenu with hidle | haccept
    · subst alternative
      exact (fiveProjectProjectTwoAcceptanceFrame.pref_asymm
        (fiveProjectPhysicalBorrower 2)
        FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
        fiveProjectProjectTwoForecast_accept_improves_on_idle) hbetter
    · subst alternative
      exact fiveProjectProjectTwoAcceptanceFrame.pref_asymm
        (fiveProjectPhysicalBorrower 2)
        FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory hbetter hbetter

end Praxeology

end
