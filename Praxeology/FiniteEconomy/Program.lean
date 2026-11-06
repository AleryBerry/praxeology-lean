/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Compiler

/-!
# Finite economy branching programs

A program node carries a complete finite-choice stage. Its continuation is a
function over every generated profile, so a branch cannot be silently omitted.
`continueOn` is the spine convenience constructor: only named feasible
profiles continue, while every other feasible profile receives a terminal
child.
-/

@[expose] public section

namespace Praxeology

/-- A finite scenario program indexed by its current economic state. A
decision node provides one continuation for every complete profile. -/
inductive FiniteEconomyProgram (State Agent Means Operation : Type)
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation] : ℕ → State → Type where
  | halt {fuel : ℕ} {state : State} :
      FiniteEconomyProgram State Agent Means Operation fuel state
  | decision {fuel : ℕ} {state : State}
      (stage : FiniteChoiceStage Agent Means Operation)
      (advance : stage.Profile → State)
      (continuation : ∀ profile,
        FiniteEconomyProgram State Agent Means Operation fuel (advance profile)) :
      FiniteEconomyProgram State Agent Means Operation (fuel + 1) state

namespace FiniteEconomyProgram

variable {State Agent Means Operation Service : Type}
variable [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
  [DecidableEq Operation]

/-- A generic branching program is physically interpretable when its listed
actions are funded before each transition and every branch obeys the same
additive stock ledger. The recursive clause checks every continuation. -/
def PhysicalAccounting (stock : State → Agent → Means → ℕ)
    (operations : OperationSemantics Operation Means Service) :
    {fuel : ℕ} → {state : State} →
      (program : FiniteEconomyProgram State Agent Means Operation fuel state) → Prop
  | _, _, .halt => True
  | _, state, .decision stage advance continuation =>
      (∀ actor action, action ∈ stage.menu actor → ∀ m,
        rawActionUse operations action m ≤ stock state actor m) ∧
      (∀ profile actor m,
        stock (advance profile) actor m +
            effectiveUse operations profile.1 actor m =
          stock state actor m + effectiveYield operations profile.1 actor m) ∧
      (∀ profile, PhysicalAccounting stock operations (continuation profile))

/-- One terminal history through a finite program. At each decision node the
history records a complete profile from that stage's generated profile set,
then continues in exactly the state selected by the program's existing
`advance` function. This is path data, not an extra behavioral rule. -/
inductive ProgramHistory : {fuel : ℕ} → {state : State} →
    FiniteEconomyProgram State Agent Means Operation fuel state → Type where
  | halt {fuel : ℕ} {state : State} :
      ProgramHistory
        (FiniteEconomyProgram.halt :
          FiniteEconomyProgram State Agent Means Operation fuel state)
  | decision {fuel : ℕ} {state : State}
      {stage : FiniteChoiceStage Agent Means Operation}
      {advance : stage.Profile → State}
      {continuation : ∀ profile,
        FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
      (profile : stage.Profile)
      (tail : ProgramHistory (continuation profile)) :
      ProgramHistory (state := state)
        (.decision (state := state) stage advance continuation)

/-- A moment in a finite program is either its current node or a moment in a
continuation selected by one complete profile. Shared prefixes use a common
value, so the program supplies the temporal branching structure. -/
inductive ProgramMoment : {fuel : ℕ} → {state : State} →
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) → Type where
  | root {fuel : ℕ} {state : State}
      {program : FiniteEconomyProgram State Agent Means Operation fuel state} :
      ProgramMoment program
  | afterProfile {fuel : ℕ} {state : State}
      {stage : FiniteChoiceStage Agent Means Operation}
      {advance : stage.Profile → State}
      {continuation : ∀ profile,
        FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
      (profile : stage.Profile)
      (moment : ProgramMoment (continuation profile)) :
      ProgramMoment (state := state)
        (.decision (state := state) stage advance continuation)

/-- State is read from the existing state index at the current program node.
Following a recorded profile moves to the already typed successor program. -/
def ProgramMoment.currentState : {fuel : ℕ} → {state : State} →
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) →
    ProgramMoment program → State
  | _, state, _, .root => state
  | _, _, .decision _ _ continuation, .afterProfile profile moment =>
      ProgramMoment.currentState (continuation profile) moment

/-- The choice stage at a moment, if the indexed program continues there. A
halted node has no decision stage. -/
def ProgramMoment.stage? : {fuel : ℕ} → {state : State} →
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) →
    ProgramMoment program → Option (FiniteChoiceStage Agent Means Operation)
  | _, _, .halt, .root => none
  | _, _, .decision stage _ _, .root => some stage
  | _, _, .decision _ _ continuation, .afterProfile profile moment =>
      ProgramMoment.stage? (continuation profile) moment

/-- A total stage view for every moment. A halted node is represented by the
existing passive-only menu, so it offers no non-idle alternative. -/
def ProgramMoment.currentStage : {fuel : ℕ} → {state : State} →
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) →
    ProgramMoment program → FiniteChoiceStage Agent Means Operation
  | _, _, .halt, .root => FiniteChoiceStage.idleOnly
  | _, _, .decision stage _ _, .root => stage
  | _, _, .decision _ _ continuation, .afterProfile profile moment =>
      ProgramMoment.currentStage (continuation profile) moment

/-- Program points admit equality comparison without adding any economic
assumption; the finite program index itself determines their constructors. -/
noncomputable instance instDecidableEqProgramMoment {fuel : ℕ} {state : State}
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) :
    DecidableEq (ProgramMoment program) := Classical.decEq _

/-- Terminal program paths admit equality comparison for use as finite-frame
histories. -/
noncomputable instance instDecidableEqProgramHistory {fuel : ℕ} {state : State}
    (_program : FiniteEconomyProgram State Agent Means Operation fuel state) :
    DecidableEq (ProgramHistory _program) := Classical.decEq _

/-- A program moment lies on a terminal history when its profile prefix
matches that history. -/
def ProgramMoment.memHist : {fuel : ℕ} → {state : State} →
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) →
    ProgramMoment program → ProgramHistory program → Prop
  | _, _, _, .root, _ => True
  | _, _, _, .afterProfile profile moment, .decision historyProfile tail =>
      ∃ hprofile : profile = historyProfile,
        ProgramMoment.memHist _ moment (hprofile ▸ tail)

/-- The action enacted at a moment is read from the history's selected
complete profile. At a terminal node the passive action is enacted. -/
def ProgramHistory.enactedAt {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state} :
    ProgramHistory program → ProgramMoment program → Agent →
      EconomyAction Agent Means Operation
  | .halt, .root, _ => .idle
  | .decision profile _, .root, actor => profile.1 actor
  | .decision historyProfile tail, .afterProfile profile moment, actor =>
      if hprofile : profile = historyProfile then
        ProgramHistory.enactedAt (hprofile ▸ tail) moment actor
      else .idle

/-- The immediate next program moment on a recorded terminal history. A
decision root advances to the root of its selected continuation; nested
moments lift the continuation's next point through the recorded profile. A
halted terminal point has no successor. -/
def ProgramMoment.nextOnHistory : {fuel : ℕ} → {state : State} →
    {program : FiniteEconomyProgram State Agent Means Operation fuel state} →
    (moment : ProgramMoment program) → ProgramHistory program →
      Option (ProgramMoment program)
  | _, _, .halt, .root, .halt => none
  | _, state, .decision stage advance continuation, .root,
      .decision profile _ =>
        some (ProgramMoment.afterProfile (state := state) (stage := stage)
          (advance := advance) (continuation := continuation) profile
          (ProgramMoment.root (program := continuation profile)
            (state := advance profile)))
  | _, _, .decision _ _ _, .afterProfile profile moment,
      .decision historyProfile tail =>
        if hprofile : profile = historyProfile then
          (ProgramMoment.nextOnHistory moment (hprofile ▸ tail)).map
            (fun next => .afterProfile profile next)
        else none
termination_by moment => moment

/-- The current program node belongs to every terminal history through it. -/
theorem ProgramMoment.root_memHist {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) :
    ProgramMoment.memHist program ProgramMoment.root history := by
  exact True.intro

/-- At the root, the history's enacted action belongs to the root menu. -/
theorem ProgramHistory.enactedAt_root_mem_menu {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) (actor : Agent) :
    ProgramHistory.enactedAt history ProgramMoment.root actor ∈
      (ProgramMoment.currentStage program ProgramMoment.root).menu actor := by
  cases program with
  | halt =>
      cases history with
      | halt => exact FiniteChoiceStage.idleOnly.idle_mem actor
  | decision stage advance continuation =>
      cases history with
      | decision profile tail => exact profile.2 actor

/-- An action read from a history through any generated program moment is in
that moment's choice menu. -/
theorem ProgramHistory.enactedAt_mem_menu {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history) (actor : Agent) :
    ProgramHistory.enactedAt history moment actor ∈ moment.currentStage.menu actor := by
  induction moment with
  | root =>
      exact ProgramHistory.enactedAt_root_mem_menu history actor
  | afterProfile profile childMoment ih =>
      cases history with
      | decision historyProfile tail =>
          have hbranches : ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) := by
            change ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) at hmem
            exact hmem
          let hprofile := Classical.choose hbranches
          have hchild := Classical.choose_spec hbranches
          cases hprofile
          simpa [ProgramHistory.enactedAt, ProgramMoment.currentStage] using
            ih tail hchild

/-- Physical accounting funds every menu action at each generated moment.
At halted moments this uses the already defined passive-only stage. -/
theorem PhysicalAccounting.menu_affordable_at {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    {Service : Type} (stock : State → Agent → Means → ℕ)
    (operations : OperationSemantics Operation Means Service)
    (haccounting : PhysicalAccounting stock operations program)
    (moment : ProgramMoment program) (actor : Agent)
    (action : EconomyAction Agent Means Operation)
    (haction : action ∈ moment.currentStage.menu actor) (m : Means) :
    rawActionUse operations action m ≤ stock moment.currentState actor m := by
  induction program generalizing action with
  | halt =>
      cases moment with
      | root =>
          have haction : action = EconomyAction.idle := by
            simpa [ProgramMoment.currentStage, FiniteChoiceStage.idleOnly] using haction
          subst action
          simp [rawActionUse, ProgramMoment.currentState]
  | @decision fuel state stage advance continuation ih =>
      cases moment with
      | root =>
          exact haccounting.1 actor action
            (by simpa [ProgramMoment.currentStage] using haction) m
      | afterProfile profile childMoment =>
          have hchild := ih profile (haccounting.2.2 profile) childMoment action
            (by simpa [ProgramMoment.currentStage] using haction)
          simpa [ProgramMoment.currentState] using hchild

/-- The action selected by a history is affordable at the state generated at
that moment. This follows from the menu and accounting certificates. -/
theorem ProgramHistory.enactedAt_rawActionUse_le_stock {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    {Service : Type} (stock : State → Agent → Means → ℕ)
    (operations : OperationSemantics Operation Means Service)
    (haccounting : PhysicalAccounting stock operations program)
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history) (actor : Agent)
    (m : Means) :
    rawActionUse operations (ProgramHistory.enactedAt history moment actor) m ≤
      stock moment.currentState actor m := by
  exact FiniteEconomyProgram.PhysicalAccounting.menu_affordable_at
    stock operations haccounting moment actor
    (ProgramHistory.enactedAt history moment actor)
    (ProgramHistory.enactedAt_mem_menu moment history hmem actor) m

/-- Strict temporal precedence is strict prefix inclusion in the generated
program tree. -/
def ProgramMoment.Precedence : {fuel : ℕ} → {state : State} →
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) →
    ProgramMoment program → ProgramMoment program → Prop
  | _, _, _, .root, .root => False
  | _, _, _, .root, .afterProfile _ _ => True
  | _, _, _, .afterProfile _ _, .root => False
  | _, _, _, .afterProfile profile₁ t₁, .afterProfile profile₂ t₂ =>
      ∃ hprofile : profile₁ = profile₂,
        ProgramMoment.Precedence _ t₁ (hprofile ▸ t₂)

/-- The selected history's next moment, when present, is an immediate future
on that same history. -/
theorem ProgramMoment.nextOnHistory_memHist_future {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history) :
    match moment.nextOnHistory history with
    | none => True
    | some next => ProgramMoment.memHist program next history ∧
        (moment = next ∨ ProgramMoment.Precedence program moment next) := by
  induction program with
  | halt =>
      cases moment with
      | root => cases history; simp [ProgramMoment.nextOnHistory]
  | @decision fuel state stage advance continuation ih =>
      cases moment with
      | root =>
          cases history with
          | decision profile tail =>
              simp [ProgramMoment.nextOnHistory, ProgramMoment.memHist,
                ProgramMoment.Precedence]
      | afterProfile profile childMoment =>
          cases history with
          | decision historyProfile tail =>
              change (∃ hprofile : profile = historyProfile,
                ProgramMoment.memHist _ childMoment (hprofile ▸ tail)) at hmem
              rcases hmem with ⟨hprofile, hchild⟩
              cases hprofile
              cases hnext : childMoment.nextOnHistory tail with
              | none => simp [ProgramMoment.nextOnHistory, hnext]
              | some next =>
                  simp only [ProgramMoment.nextOnHistory, hnext, Option.map_some]
                  have hchildFuture := ih profile childMoment tail hchild
                  rw [hnext] at hchildFuture
                  rcases hchildFuture with ⟨hnextMem, hfuture⟩
                  have hnextMemOuter : ProgramMoment.memHist
                      (FiniteEconomyProgram.decision (state := state) stage advance
                        continuation)
                      (ProgramMoment.afterProfile (state := state) (stage := stage)
                        (advance := advance) (continuation := continuation)
                        profile next)
                      (ProgramHistory.decision (state := state) profile tail) :=
                    ⟨rfl, hnextMem⟩
                  have hfutureOuter :
                      (ProgramMoment.afterProfile (state := state) (stage := stage)
                        (advance := advance) (continuation := continuation)
                        profile childMoment =
                          ProgramMoment.afterProfile (state := state) (stage := stage)
                            (advance := advance) (continuation := continuation)
                            profile next) ∨
                      ProgramMoment.Precedence
                        (FiniteEconomyProgram.decision (state := state) stage advance
                          continuation)
                        (ProgramMoment.afterProfile (state := state) (stage := stage)
                          (advance := advance) (continuation := continuation)
                          profile childMoment)
                        (ProgramMoment.afterProfile (state := state) (stage := stage)
                          (advance := advance) (continuation := continuation)
                          profile next) := by
                    rcases hfuture with heq | hlt
                    · exact Or.inl (congrArg (fun m :
                        ProgramMoment (continuation profile) =>
                          ProgramMoment.afterProfile (state := state) (stage := stage)
                            (advance := advance) (continuation := continuation)
                            profile m) heq)
                    · exact Or.inr ⟨rfl, hlt⟩
                  exact ⟨hnextMemOuter, hfutureOuter⟩

/-- Every immediate successor along a recorded history uses the transition
equation certified at that exact program node. The recursive case follows the
recorded profile into its existing continuation; no second inventory update
rule is introduced. -/
theorem PhysicalAccounting.nextOnHistory_stock_balance
    {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (stock : State → Agent → Means → ℕ)
    (operations : OperationSemantics Operation Means Service)
    (haccounting : PhysicalAccounting stock operations program)
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history)
    (actor : Agent) (m : Means) :
    match moment.nextOnHistory history with
    | none => True
    | some next =>
        stock next.currentState actor m +
            effectiveUse operations (fun i => ProgramHistory.enactedAt history moment i)
              actor m =
          stock moment.currentState actor m +
            effectiveYield operations (fun i => ProgramHistory.enactedAt history moment i)
              actor m := by
  induction program with
  | halt =>
      cases moment
      cases history
      simp [ProgramMoment.nextOnHistory]
  | @decision fuel state stage advance continuation ih =>
      cases moment with
      | root =>
          cases history with
          | decision profile tail =>
              simpa [ProgramMoment.nextOnHistory, ProgramMoment.currentState,
                ProgramHistory.enactedAt] using
                haccounting.2.1 profile actor m
      | afterProfile profile childMoment =>
          cases history with
          | decision historyProfile tail =>
              have hbranches : ∃ hprofile : profile = historyProfile,
                  ProgramMoment.memHist (continuation profile) childMoment
                    (hprofile ▸ tail) := by
                change ∃ hprofile : profile = historyProfile,
                  ProgramMoment.memHist (continuation profile) childMoment
                    (hprofile ▸ tail) at hmem
                exact hmem
              rcases hbranches with ⟨hprofile, hchild⟩
              cases hprofile
              have hchildBalance :=
                ih profile (haccounting.2.2 profile) childMoment tail hchild
              cases hnext : childMoment.nextOnHistory tail with
              | none =>
                  simp [ProgramMoment.nextOnHistory, hnext]
              | some childNext =>
                  rw [hnext] at hchildBalance
                  simpa [ProgramMoment.nextOnHistory, hnext,
                    ProgramMoment.currentState, ProgramHistory.enactedAt]
                    using hchildBalance

/-- The root strictly precedes every non-root program moment. -/
theorem ProgramMoment.root_precedes_of_ne_root {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (hne : moment ≠ ProgramMoment.root) :
    ProgramMoment.Precedence program ProgramMoment.root moment := by
  cases moment with
  | root => exact (hne rfl).elim
  | afterProfile profile child => exact True.intro

/-- The immediate-successor predicate on a program history identifies the
unique successor generated by its recorded profile. -/
theorem ProgramMoment.nextOnHistory_eq_of_isNext {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history) (next : ProgramMoment program)
    (hnext : IsNextMoment (ProgramMoment.Precedence program)
      (ProgramMoment.memHist program) moment next history) :
    moment.nextOnHistory history = some next := by
  induction program with
  | halt =>
      cases moment
      cases history
      cases next
      simp [IsNextMoment, ProgramMoment.Precedence] at hnext
  | @decision fuel state stage advance continuation ih =>
      cases moment with
      | root =>
          cases history with
          | decision profile tail =>
              cases next with
              | root =>
                  simp [IsNextMoment, ProgramMoment.Precedence] at hnext
              | afterProfile nextProfile nextMoment =>
                  have hnextMem :
                      ∃ hprofile : nextProfile = profile,
                        ProgramMoment.memHist _ nextMoment (hprofile ▸ tail) := by
                    change ∃ hprofile : nextProfile = profile,
                      ProgramMoment.memHist _ nextMoment (hprofile ▸ tail)
                    exact hnext.2.1
                  rcases hnextMem with ⟨hprofile, hchild⟩
                  cases hprofile
                  by_cases hnextRoot : nextMoment = ProgramMoment.root
                  · cases hnextRoot
                    simp [ProgramMoment.nextOnHistory]
                  · let intermediate : ProgramMoment
                        (.decision (state := state) stage advance continuation) :=
                      .afterProfile (state := state) (stage := stage)
                        (advance := advance) (continuation := continuation) profile
                        (ProgramMoment.root (program := continuation profile)
                          (state := advance profile))
                    have hintermediateMem :
                        ProgramMoment.memHist
                          (.decision (state := state) stage advance continuation)
                          intermediate (.decision (state := state) profile tail) := by
                      change ∃ hprofile : profile = profile,
                        ProgramMoment.memHist _ ProgramMoment.root tail
                      exact ⟨rfl, ProgramMoment.root_memHist tail⟩
                    have hrootIntermediate :
                        ProgramMoment.Precedence
                          (.decision (state := state) stage advance continuation)
                          ProgramMoment.root intermediate := by
                      simp [intermediate, ProgramMoment.Precedence]
                    have hintermediateNext :
                        ProgramMoment.Precedence
                          (.decision (state := state) stage advance continuation)
                          intermediate (.afterProfile profile nextMoment) := by
                      change ∃ hprofile : profile = profile,
                        ProgramMoment.Precedence (continuation profile)
                          (ProgramMoment.root (program := continuation profile)) nextMoment
                      exact ⟨rfl, ProgramMoment.root_precedes_of_ne_root
                        nextMoment hnextRoot⟩
                    exact (hnext.2.2.2 intermediate hintermediateMem
                      ⟨hrootIntermediate, hintermediateNext⟩).elim
      | afterProfile profile childMoment =>
          cases history with
          | decision historyProfile tail =>
              change ∃ hprofile : profile = historyProfile,
                ProgramMoment.memHist _ childMoment (hprofile ▸ tail) at hmem
              rcases hmem with ⟨hprofile, hchild⟩
              cases hprofile
              cases next with
              | root =>
                  simp [IsNextMoment, ProgramMoment.Precedence] at hnext
              | afterProfile nextProfile nextMoment =>
                  have hnextProfile : nextProfile = profile := by
                    rcases hnext.2.2.1 with ⟨hprofile, _⟩
                    exact hprofile.symm
                  cases hnextProfile
                  have hnextMem :
                      ProgramMoment.memHist (continuation profile) nextMoment tail := by
                    rcases hnext.2.1 with ⟨hprofile, hnextMem⟩
                    cases hprofile
                    exact hnextMem
                  have hchildNext : IsNextMoment
                      (ProgramMoment.Precedence (continuation profile))
                      (ProgramMoment.memHist (continuation profile))
                      childMoment nextMoment tail := by
                    refine ⟨hchild, hnextMem, ?_, ?_⟩
                    · exact hnext.2.2.1.2
                    · intro between hbetweenMem hbetween
                      let lifted := ProgramMoment.afterProfile
                        (state := state) (stage := stage) (advance := advance)
                        (continuation := continuation) profile between
                      have hliftedMem : ProgramMoment.memHist
                          (.decision (state := state) stage advance continuation)
                          lifted (.decision (state := state) profile tail) := by
                        change ∃ hprofile : profile = profile,
                          ProgramMoment.memHist _ between tail
                        exact ⟨rfl, hbetweenMem⟩
                      have hbefore : ProgramMoment.Precedence
                          (.decision (state := state) stage advance continuation)
                          (ProgramMoment.afterProfile profile childMoment) lifted :=
                        ⟨rfl, hbetween.1⟩
                      have hafter : ProgramMoment.Precedence
                          (.decision (state := state) stage advance continuation)
                          lifted (ProgramMoment.afterProfile profile nextMoment) :=
                        ⟨rfl, hbetween.2⟩
                      exact hnext.2.2.2 lifted hliftedMem ⟨hbefore, hafter⟩
                  have hchildEq := ih profile childMoment tail hchild nextMoment hchildNext
                  simp [ProgramMoment.nextOnHistory, hchildEq]

/-- Maturation for a selected program history is the next program point, or
the current point if that history is already terminal. -/
def ProgramMoment.maturationAt {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program) :
    ProgramMoment program :=
  (moment.nextOnHistory history).getD moment

/-- The maturity point is on the selected history and is either the current
point or a strict future point. -/
theorem ProgramMoment.maturationAt_memHist_future {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history) :
    ProgramMoment.memHist program (moment.maturationAt history) history ∧
      (moment = moment.maturationAt history ∨
        ProgramMoment.Precedence program moment (moment.maturationAt history)) := by
  cases hnext : moment.nextOnHistory history with
  | none =>
      simp [ProgramMoment.maturationAt, hnext, hmem]
  | some next =>
      have hfuture := ProgramMoment.nextOnHistory_memHist_future moment history hmem
      rw [hnext] at hfuture
      simpa [ProgramMoment.maturationAt, hnext] using hfuture

theorem ProgramMoment.precedence_irrefl {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) :
    ¬ ProgramMoment.Precedence program moment moment := by
  induction moment with
  | root => simp [ProgramMoment.Precedence]
  | afterProfile profile tailMoment ih =>
      intro hprec
      rcases hprec with ⟨hprofile, htail⟩
      cases hprofile
      exact ih htail

/-- The generated prefix relation is transitive. -/
theorem ProgramMoment.precedence_trans {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (a b c : ProgramMoment program)
    (hab : ProgramMoment.Precedence program a b)
    (hbc : ProgramMoment.Precedence program b c) :
    ProgramMoment.Precedence program a c := by
  cases a with
  | root =>
      cases b with
      | root => simp [ProgramMoment.Precedence] at hab
      | afterProfile pb mb =>
          cases c with
          | root => simp [ProgramMoment.Precedence] at hbc
          | afterProfile pc mc => exact True.intro
  | afterProfile pa ma =>
      cases b with
      | root => simp [ProgramMoment.Precedence] at hab
      | afterProfile pb mb =>
          cases c with
          | root => simp [ProgramMoment.Precedence] at hbc
          | afterProfile pc mc =>
              rcases hab with ⟨habProfile, habTail⟩
              rcases hbc with ⟨hbcProfile, hbcTail⟩
              cases habProfile
              cases hbcProfile
              exact ⟨rfl, ProgramMoment.precedence_trans ma mb mc habTail hbcTail⟩

/-- Any two generated prefixes of a common moment are comparable. -/
theorem ProgramMoment.backward_linearity {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (a b c : ProgramMoment program)
    (hac : ProgramMoment.Precedence program a c)
    (hbc : ProgramMoment.Precedence program b c) :
    ProgramMoment.Precedence program a b ∨ a = b ∨
      ProgramMoment.Precedence program b a := by
  cases c with
  | root => cases a <;> simp [ProgramMoment.Precedence] at hac
  | afterProfile pc mc =>
      cases a with
      | root =>
          cases b with
          | root => exact Or.inr (Or.inl rfl)
          | afterProfile pb mb => exact Or.inl True.intro
      | afterProfile pa ma =>
          cases b with
          | root => exact Or.inr (Or.inr True.intro)
          | afterProfile pb mb =>
              rcases hac with ⟨hap, hapTail⟩
              rcases hbc with ⟨hbp, hbpTail⟩
              cases hap
              cases hbp
              rcases ProgramMoment.backward_linearity ma mb mc hapTail hbpTail with
                h | h | h
              · exact Or.inl ⟨rfl, h⟩
              · cases h
                right
                left
                rfl
              · exact Or.inr (Or.inr ⟨rfl, h⟩)

/-- Different profiles yield distinct, incomparable immediate continuation
points in the generated program tree. -/
def ProgramMoment.branchRoot {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (profile : stage.Profile) :
    ProgramMoment (state := state) (.decision stage advance continuation) :=
  .afterProfile (state := state) profile
    (ProgramMoment.root (program := continuation profile)
      (state := advance profile))

/-- A decision's recorded profile advances to the root of exactly its stored
continuation, whose state index is the program's `advance` result. -/
@[simp] theorem ProgramMoment.nextOnHistory_root {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (profile : stage.Profile) (tail : ProgramHistory (continuation profile)) :
    ProgramMoment.nextOnHistory
        (ProgramMoment.root
          (program := FiniteEconomyProgram.decision (state := state) stage advance
            continuation))
        (ProgramHistory.decision (state := state) profile tail) =
      some (ProgramMoment.branchRoot (state := state) (stage := stage)
        (advance := advance) (continuation := continuation) profile) := by
  simp [ProgramMoment.nextOnHistory, ProgramMoment.branchRoot]

/-- The state at the generated branch root is the state selected by the
program's existing transition function. -/
@[simp] theorem ProgramMoment.branchRoot_currentState {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (profile : stage.Profile) :
    (ProgramMoment.branchRoot (state := state) (stage := stage)
      (advance := advance) (continuation := continuation) profile).currentState =
        advance profile := rfl

/-- The first successor's stock balance is the balance certified for the
selected profile by `PhysicalAccounting`. This connects the program's
generated temporal edge to its existing physical transition equation. -/
theorem PhysicalAccounting.root_successor_stock_balance
    {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation (fuel + 1) state}
    (stock : State → Agent → Means → ℕ)
    (operations : OperationSemantics Operation Means Service)
    (haccounting : PhysicalAccounting stock operations program)
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (profile : stage.Profile) (actor : Agent) (m : Means)
    (hprogram : program = .decision stage advance continuation) :
    stock (ProgramMoment.branchRoot (state := state) (stage := stage)
      (advance := advance) (continuation := continuation) profile).currentState
        actor m + effectiveUse operations profile.1 actor m =
      stock (ProgramMoment.root (program := program)).currentState actor m +
        effectiveYield operations profile.1 actor m := by
  subst program
  exact haccounting.2.1 profile actor m

/-- Every action in a program's root menu is funded from the root state by
the same recursive physical-accounting certificate. -/
theorem PhysicalAccounting.root_menu_action_affordable
    {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation (fuel + 1) state}
    (stock : State → Agent → Means → ℕ)
    (operations : OperationSemantics Operation Means Service)
    (haccounting : PhysicalAccounting stock operations program)
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (hprogram : program = .decision stage advance continuation)
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (haction : action ∈ stage.menu actor) (m : Means) :
    rawActionUse operations action m ≤
      stock (ProgramMoment.root (program := program)).currentState actor m := by
  subst program
  exact haccounting.1 actor action haction m

theorem ProgramMoment.afterProfile_roots_incomparable {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    {profile₁ profile₂ : stage.Profile} (hne : profile₁ ≠ profile₂) :
    ¬ ProgramMoment.Precedence
        (.decision (state := state) stage advance continuation)
        (ProgramMoment.branchRoot (state := state) (stage := stage)
          (advance := advance) (continuation := continuation) profile₁)
        (ProgramMoment.branchRoot (state := state) (stage := stage)
          (advance := advance) (continuation := continuation) profile₂) ∧
    (ProgramMoment.branchRoot (state := state) (stage := stage)
        (advance := advance) (continuation := continuation) profile₁ ≠
      ProgramMoment.branchRoot (state := state) (stage := stage)
        (advance := advance) (continuation := continuation) profile₂) ∧
    ¬ ProgramMoment.Precedence
        (.decision (state := state) stage advance continuation)
        (ProgramMoment.branchRoot (state := state) (stage := stage)
          (advance := advance) (continuation := continuation) profile₂)
        (ProgramMoment.branchRoot (state := state) (stage := stage)
          (advance := advance) (continuation := continuation) profile₁) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hprofile, _⟩
    exact hne hprofile
  · intro heq
    have hprofile : profile₁ = profile₂ := by
      injection heq
    exact hne hprofile
  · rintro ⟨hprofile, _⟩
    exact hne hprofile.symm

/-- Histories that share a strict future moment agree on every action at its
generated past. -/
theorem ProgramHistory.enactedAt_eq_of_shared_future {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (first second : ProgramHistory program) (moment future : ProgramMoment program)
    (hprecedence : ProgramMoment.Precedence program moment future)
    (hfirst : ProgramMoment.memHist program future first)
    (hsecond : ProgramMoment.memHist program future second) (actor : Agent) :
    ProgramHistory.enactedAt first moment actor =
      ProgramHistory.enactedAt second moment actor := by
  induction future with
  | root =>
      cases moment <;> simp [ProgramMoment.Precedence] at hprecedence
  | afterProfile profile futureTail ih =>
      cases moment with
      | root =>
          cases first with
          | decision profile₁ tail₁ =>
              cases second with
              | decision profile₂ tail₂ =>
                  rcases hfirst with ⟨hprofile₁, _⟩
                  rcases hsecond with ⟨hprofile₂, _⟩
                  cases hprofile₁
                  cases hprofile₂
                  rfl
      | afterProfile momentProfile momentTail =>
          cases first with
          | decision historyProfile₁ tail₁ =>
              cases second with
              | decision historyProfile₂ tail₂ =>
                  rcases hprecedence with ⟨hfutureProfile, hchildPrecedence⟩
                  rcases hfirst with ⟨hfirstProfile, hchildFirst⟩
                  rcases hsecond with ⟨hsecondProfile, hchildSecond⟩
                  cases hfutureProfile
                  cases hfirstProfile
                  cases hsecondProfile
                  simpa [ProgramHistory.enactedAt] using
                    ih tail₁ tail₂ momentTail hchildPrecedence
                      hchildFirst hchildSecond

/-- The final point on a history is obtained by following its recorded profile
choices to the terminal program node. -/
def ProgramHistory.terminalMoment : {fuel : ℕ} → {state : State} →
    {program : FiniteEconomyProgram State Agent Means Operation fuel state} →
    ProgramHistory program → ProgramMoment program
  | _, _, .halt, .halt => .root
  | _, _, .decision _ _ _, .decision profile tail =>
      .afterProfile profile tail.terminalMoment

/-- Every moment on a history is its terminal moment or strictly precedes it. -/
theorem ProgramMoment.memHist_precedes_terminal {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history) :
    moment = history.terminalMoment ∨
      ProgramMoment.Precedence program moment history.terminalMoment := by
  induction history with
  | halt =>
      cases moment with
      | root => exact Or.inl rfl
  | decision profile tail ih =>
      cases moment with
      | root =>
          right
          simp [ProgramHistory.terminalMoment, ProgramMoment.Precedence]
      | afterProfile momentProfile childMoment =>
          rcases hmem with ⟨hprofile, hchild⟩
          cases hprofile
          rcases ih childMoment hchild with heq | hlt
          · subst childMoment
            exact Or.inl rfl
          · exact Or.inr ⟨rfl, hlt⟩

/-- The moments of each complete profile history form a linear chain. -/
theorem ProgramHistory.moments_linear {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) :
    IsLinearChain (ProgramMoment.Precedence program)
      {moment | ProgramMoment.memHist program moment history} := by
  intro first second hfirst hsecond
  obtain hfirst_terminal := ProgramMoment.memHist_precedes_terminal first history hfirst
  obtain hsecond_terminal := ProgramMoment.memHist_precedes_terminal second history hsecond
  rcases hfirst_terminal with hfirst_eq | hfirst_lt
  · rcases hsecond_terminal with hsecond_eq | hsecond_lt
    · exact Or.inr (Or.inl (hfirst_eq.trans hsecond_eq.symm))
    · exact Or.inr (Or.inr (by simpa [hfirst_eq] using hsecond_lt))
  · rcases hsecond_terminal with hsecond_eq | hsecond_lt
    · exact Or.inl (by simpa [hsecond_eq] using hfirst_lt)
    · exact ProgramMoment.backward_linearity first second history.terminalMoment
        hfirst_lt hsecond_lt

/-- The terminal moment belongs to the history that constructs it. -/
theorem ProgramHistory.terminalMoment_memHist {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) :
    ProgramMoment.memHist program history.terminalMoment history := by
  induction history with
  | halt => exact True.intro
  | decision profile tail ih =>
      change ∃ hprofile : profile = profile,
        ProgramMoment.memHist _ tail.terminalMoment tail
      exact ⟨rfl, ih⟩

/-- A terminal history has no strict future in the generated program tree. -/
theorem ProgramHistory.terminalMoment_is_last {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) (moment : ProgramMoment program) :
    ¬ ProgramMoment.Precedence program history.terminalMoment moment := by
  induction history with
  | halt =>
      cases moment with
      | root => simp [ProgramHistory.terminalMoment, ProgramMoment.Precedence]
  | decision profile tail ih =>
      cases moment with
      | root => simp [ProgramHistory.terminalMoment, ProgramMoment.Precedence]
      | afterProfile otherProfile childMoment =>
          intro hprecedence
          rcases hprecedence with ⟨hprofile, hchild⟩
          cases hprofile
          exact ih childMoment hchild

/-- Every generated predecessor of a history's terminal moment belongs to
that same history. -/
theorem ProgramMoment.precedes_terminal_memHist {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hprecedence : ProgramMoment.Precedence program moment history.terminalMoment) :
    ProgramMoment.memHist program moment history := by
  induction history with
  | halt =>
      cases moment with
      | root => simp [ProgramHistory.terminalMoment, ProgramMoment.Precedence] at hprecedence
  | decision profile tail ih =>
      cases moment with
      | root => exact True.intro
      | afterProfile momentProfile childMoment =>
          rcases hprecedence with ⟨hprofile, hchild⟩
          cases hprofile
          have hchildMem := ih childMoment hchild
          change ∃ hprofile : profile = profile,
            ProgramMoment.memHist _ childMoment tail
          exact ⟨rfl, hchildMem⟩

/-- The moments of each complete profile history form a maximal linear chain
in the program's generated temporal order. -/
theorem ProgramHistory.moments_maximal_linear {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) :
    IsMaximalLinearChain (ProgramMoment.Precedence program)
      {moment | ProgramMoment.memHist program moment history} := by
  refine ⟨history.moments_linear, ?_⟩
  intro larger hlinear hsubset moment hmoment
  have hterminal := hlinear hmoment (hsubset history.terminalMoment_memHist)
  rcases hterminal with hbefore | heq | hafter
  · exact ProgramMoment.precedes_terminal_memHist moment history hbefore
  · simpa [heq] using history.terminalMoment_memHist
  · exact (history.terminalMoment_is_last moment hafter).elim

/-- Record the complete stage/profile choices along a terminal program
history. The sigma type retains each stage's own menu and profile type. -/
def ProgramHistory.choices : {fuel : ℕ} → {state : State} →
    {program : FiniteEconomyProgram State Agent Means Operation fuel state} →
    ProgramHistory program →
      List (Σ stage : FiniteChoiceStage Agent Means Operation, stage.Profile)
  | _, _, _, .halt => []
  | _, _, _, .decision profile tail =>
      ⟨_, profile⟩ :: ProgramHistory.choices tail

/-- The terminal state reached along a program history. Every decision uses
the `advance` function already stored in the program; the terminal case
returns the state indexing that continuation. -/
def ProgramHistory.terminalState : {fuel : ℕ} → {state : State} →
    {program : FiniteEconomyProgram State Agent Means Operation fuel state} →
    ProgramHistory program → State
  | _, state, _, .halt => state
  | _, _, _, .decision _ tail => ProgramHistory.terminalState tail

/-- The state trace along a program history. Each head is the state indexed
by the current program node; in a decision case the tail begins at the
successor state `advance profile`, by the dependent type of that continuation.
-/
def ProgramHistory.stateTrace : {fuel : ℕ} → {state : State} →
    {program : FiniteEconomyProgram State Agent Means Operation fuel state} →
    ProgramHistory program → List State
  | _, state, _, .halt => [state]
  | _, state, _, .decision _ tail => state :: ProgramHistory.stateTrace tail

/-- A finite program history has one more state than decision choices: one
initial state and one successor state per selected stage profile. -/
theorem ProgramHistory.stateTrace_length {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) :
    history.stateTrace.length = history.choices.length + 1 := by
  induction history with
  | halt => simp [ProgramHistory.stateTrace, ProgramHistory.choices]
  | decision profile tail ih =>
      simp [ProgramHistory.stateTrace, ProgramHistory.choices, ih]

/-- The first state in a history is the state indexing its program. -/
theorem ProgramHistory.stateTrace_head {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) :
    history.stateTrace.head? = some state := by
  cases history <;> rfl

/-- After choosing profile `p`, the continuation trace starts at exactly the
successor state assigned by the program's existing transition function. -/
theorem ProgramHistory.continuation_trace_starts_at_advance
    {fuel : ℕ}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (profile : stage.Profile) (tail : ProgramHistory (continuation profile)) :
    tail.stateTrace.head? = some (advance profile) := by
  exact ProgramHistory.stateTrace_head tail

/-- The all-idle profile belongs to every stage's complete profile set. This
follows from the already required idle membership in each menu. -/
def ProgramHistory.idleProfile (stage : FiniteChoiceStage Agent Means Operation) :
    stage.Profile := ⟨fun _ => EconomyAction.idle, stage.idle_mem⟩

/-- Every program has a terminal history, obtained by selecting the existing
idle action at each decision and following that profile's stored
continuation. This witness uses no choice principle and adds no policy premise.
-/
def ProgramHistory.allIdle : {fuel : ℕ} → {state : State} →
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) →
    ProgramHistory program
  | _, _, .halt => .halt
  | _, state, .decision stage advance continuation =>
      let profile := ProgramHistory.idleProfile stage
      show ProgramHistory
        (FiniteEconomyProgram.decision (state := state) stage advance continuation) from
        ProgramHistory.decision (state := state) profile
          (ProgramHistory.allIdle (continuation profile))

/-- Every generated program moment lies on at least one terminal history. -/
theorem ProgramMoment.exists_history {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) :
    ∃ history : ProgramHistory program,
      ProgramMoment.memHist program moment history := by
  cases program with
  | halt =>
      cases moment with
      | root => exact ⟨.halt, True.intro⟩
  | decision stage advance continuation =>
      cases moment with
      | root =>
          exact ⟨ProgramHistory.allIdle (.decision stage advance continuation),
            True.intro⟩
      | afterProfile profile childMoment =>
          obtain ⟨tail, htail⟩ := childMoment.exists_history
          refine ⟨.decision (state := state) profile tail, ?_⟩
          change ∃ hprofile : profile = profile,
            ProgramMoment.memHist _ childMoment tail
          exact ⟨rfl, htail⟩

/-- Two terminal paths with the same program moments have the same selected
profile at every decision and are therefore equal. -/
theorem ProgramHistory.extensional {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (first second : ProgramHistory program)
    (hext : ∀ moment, ProgramMoment.memHist program moment first ↔
      ProgramMoment.memHist program moment second) :
    first = second := by
  cases program with
  | halt =>
      cases first
      cases second
      rfl
  | decision stage advance continuation =>
      cases first with
      | decision profile₁ tail₁ =>
          cases second with
          | decision profile₂ tail₂ =>
              have hprofile : profile₁ = profile₂ := by
                have hfirst : ProgramMoment.memHist _
                    (.afterProfile (state := state) profile₁ ProgramMoment.root)
                    (.decision (state := state) profile₁ tail₁) := by
                  change ∃ hprofile : profile₁ = profile₁,
                    ProgramMoment.memHist _ ProgramMoment.root tail₁
                  exact ⟨rfl, ProgramMoment.root_memHist _⟩
                rcases (hext (.afterProfile (state := state) profile₁
                  ProgramMoment.root)).mp hfirst with
                  ⟨hprofile, _⟩
                exact hprofile
              subst profile₂
              have htail_extensional : ∀ moment,
                  ProgramMoment.memHist (continuation profile₁) moment tail₁ ↔
                    ProgramMoment.memHist (continuation profile₁) moment tail₂ := by
                intro moment
                have hparent := hext (.afterProfile (state := state) profile₁ moment)
                have hfirst_iff :
                    ProgramMoment.memHist _ (.afterProfile (state := state) profile₁ moment)
                        (.decision (state := state) profile₁ tail₁) ↔
                      ProgramMoment.memHist (continuation profile₁) moment tail₁ := by
                  constructor
                  · intro hmem
                    change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.memHist _ moment (hprofile ▸ tail₁) at hmem
                    rcases hmem with ⟨hprofile, hmem⟩
                    cases hprofile
                    exact hmem
                  · intro hmem
                    change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.memHist _ moment (hprofile ▸ tail₁)
                    exact ⟨rfl, hmem⟩
                have hsecond_iff :
                    ProgramMoment.memHist _ (.afterProfile (state := state) profile₁ moment)
                        (.decision (state := state) profile₁ tail₂) ↔
                      ProgramMoment.memHist (continuation profile₁) moment tail₂ := by
                  constructor
                  · intro hmem
                    change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.memHist _ moment (hprofile ▸ tail₂) at hmem
                    rcases hmem with ⟨hprofile, hmem⟩
                    cases hprofile
                    exact hmem
                  · intro hmem
                    change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.memHist _ moment (hprofile ▸ tail₂)
                    exact ⟨rfl, hmem⟩
                exact hfirst_iff.symm.trans (hparent.trans hsecond_iff)
              have htail_eq := ProgramHistory.extensional tail₁ tail₂ htail_extensional
              subst tail₂
              rfl

/-- Distinct terminal histories that share a moment split into strictly
later, incomparable moments on their respective paths. -/
theorem ProgramHistory.divergent_futures {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (first second : ProgramHistory program) (moment : ProgramMoment program)
    (hfirst : ProgramMoment.memHist program moment first)
    (hsecond : ProgramMoment.memHist program moment second)
    (hne : first ≠ second) :
    ∃ future₁ future₂,
      ProgramMoment.memHist program future₁ first ∧
      ProgramMoment.memHist program future₂ second ∧
      ProgramMoment.Precedence program moment future₁ ∧
      ProgramMoment.Precedence program moment future₂ ∧
      ¬ ProgramMoment.Precedence program future₁ future₂ ∧
      future₁ ≠ future₂ ∧
      ¬ ProgramMoment.Precedence program future₂ future₁ := by
  cases program with
  | halt =>
      cases first
      cases second
      exact (hne rfl).elim
  | decision stage advance continuation =>
      cases first with
      | decision profile₁ tail₁ =>
          cases second with
          | decision profile₂ tail₂ =>
              cases moment with
              | root =>
                  by_cases hprofile : profile₁ = profile₂
                  · subst profile₂
                    have htails : tail₁ ≠ tail₂ := by
                      intro htail
                      apply hne
                      cases htail
                      rfl
                    obtain ⟨future₁, future₂, hfuture₁, hfuture₂,
                      hbefore₁, hbefore₂, hnot₁₂, hneq, hnot₂₁⟩ :=
                      ProgramHistory.divergent_futures tail₁ tail₂ ProgramMoment.root
                        (ProgramMoment.root_memHist tail₁)
                        (ProgramMoment.root_memHist tail₂) htails
                    refine ⟨.afterProfile (state := state) profile₁ future₁,
                      .afterProfile (state := state) profile₁ future₂,
                      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · change ∃ hprofile : profile₁ = profile₁,
                        ProgramMoment.memHist _ future₁ tail₁
                      exact ⟨rfl, hfuture₁⟩
                    · change ∃ hprofile : profile₁ = profile₁,
                        ProgramMoment.memHist _ future₂ tail₂
                      exact ⟨rfl, hfuture₂⟩
                    · simp [ProgramMoment.Precedence]
                    · simp [ProgramMoment.Precedence]
                    · intro h
                      change ∃ hprofile : profile₁ = profile₁,
                        ProgramMoment.Precedence _ future₁ (hprofile ▸ future₂) at h
                      rcases h with ⟨_, hchild⟩
                      exact hnot₁₂ hchild
                    · intro h
                      have hchild : future₁ = future₂ := by
                        cases h
                        rfl
                      exact hneq hchild
                    · intro h
                      change ∃ hprofile : profile₁ = profile₁,
                        ProgramMoment.Precedence _ future₂ (hprofile ▸ future₁) at h
                      rcases h with ⟨_, hchild⟩
                      exact hnot₂₁ hchild
                  · let future₁ :=
                      ProgramMoment.branchRoot (state := state) (stage := stage)
                        (advance := advance) (continuation := continuation) profile₁
                    let future₂ :=
                      ProgramMoment.branchRoot (state := state) (stage := stage)
                        (advance := advance) (continuation := continuation) profile₂
                    have hbranch := ProgramMoment.afterProfile_roots_incomparable
                      (state := state) (stage := stage) (advance := advance)
                      (continuation := continuation) hprofile
                    refine ⟨future₁, future₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · change ∃ hprofile : profile₁ = profile₁,
                        ProgramMoment.memHist _ ProgramMoment.root tail₁
                      exact ⟨rfl, ProgramMoment.root_memHist tail₁⟩
                    · change ∃ hprofile : profile₂ = profile₂,
                        ProgramMoment.memHist _ ProgramMoment.root tail₂
                      exact ⟨rfl, ProgramMoment.root_memHist tail₂⟩
                    · simp [future₁, ProgramMoment.branchRoot, ProgramMoment.Precedence]
                    · simp [future₂, ProgramMoment.branchRoot, ProgramMoment.Precedence]
                    · exact hbranch.1
                    · exact hbranch.2.1
                    · exact hbranch.2.2
              | afterProfile profile currentMoment =>
                  rcases hfirst with ⟨hprofile₁, htail₁⟩
                  rcases hsecond with ⟨hprofile₂, htail₂⟩
                  cases hprofile₁
                  cases hprofile₂
                  have htails : tail₁ ≠ tail₂ := by
                    intro htail
                    apply hne
                    cases htail
                    rfl
                  obtain ⟨future₁, future₂, hfuture₁, hfuture₂,
                    hbefore₁, hbefore₂, hnot₁₂, hneq, hnot₂₁⟩ :=
                    ProgramHistory.divergent_futures tail₁ tail₂ currentMoment
                      htail₁ htail₂ htails
                  let lifted₁ := ProgramMoment.afterProfile (state := state) profile₁ future₁
                  let lifted₂ := ProgramMoment.afterProfile (state := state) profile₁ future₂
                  refine ⟨lifted₁, lifted₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.memHist _ future₁ tail₁
                    exact ⟨rfl, hfuture₁⟩
                  · change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.memHist _ future₂ tail₂
                    exact ⟨rfl, hfuture₂⟩
                  · change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.Precedence _ currentMoment future₁
                    exact ⟨rfl, hbefore₁⟩
                  · change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.Precedence _ currentMoment future₂
                    exact ⟨rfl, hbefore₂⟩
                  · intro h
                    change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.Precedence _ future₁ (hprofile ▸ future₂) at h
                    rcases h with ⟨_, hchild⟩
                    exact hnot₁₂ hchild
                  · intro h
                    have hchild : future₁ = future₂ := by
                      injection h
                    exact hneq hchild
                  · intro h
                    change ∃ hprofile : profile₁ = profile₁,
                      ProgramMoment.Precedence _ future₂ (hprofile ▸ future₁) at h
                    rcases h with ⟨_, hchild⟩
                    exact hnot₂₁ hchild

/-- Every selected complete profile has a terminal continuation: select that
profile first, then follow the recursively constructed all-idle continuation.
This supplies a witness for a branch without imposing a result on its state.
-/
def ProgramHistory.afterProfile {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (profile : stage.Profile) :
    ProgramHistory
      (FiniteEconomyProgram.decision (state := state) stage advance continuation) :=
  ProgramHistory.decision (state := state) profile
    (ProgramHistory.allIdle (continuation profile))

/-- The constructed branch records the requested first-stage profile. -/
@[simp] theorem ProgramHistory.afterProfile_choices_head
    {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (profile : stage.Profile) :
    (ProgramHistory.afterProfile (fuel := fuel) (state := state)
      (stage := stage) (advance := advance) (continuation := continuation)
      profile).choices.head? = some ⟨stage, profile⟩ := by
  rfl

/-- Select one agent's alternative at the root decision while preserving the
other agents' simultaneous choices. If the requested action is already
selected, retain the original continuation; otherwise follow the program's
existing continuation for the replaced profile, using the existing all-idle
history there. This is a branch construction from the finite menu, not a
claim about preference or purposeful choice. -/
def ProgramHistory.selectActorAtRoot {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (history : ProgramHistory
      (FiniteEconomyProgram.decision (state := state) stage advance continuation))
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ stage.menu actor) :
    ProgramHistory
      (FiniteEconomyProgram.decision (state := state) stage advance continuation) :=
  match history with
  | .decision profile tail =>
      if action = profile.1 actor then
        .decision (state := state) profile tail
      else
        let replaced := stage.replaceProfile profile actor action action_mem
        .decision (state := state) replaced
          (ProgramHistory.allIdle (continuation replaced))

/-- Select one agent's feasible action at any generated moment, keeping the
existing prefix and the peers' action profile intact. Only the continuation
below a changed profile is replaced by the program's existing all-idle path.
-/
noncomputable def ProgramHistory.selectActorAtMoment {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history)
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ moment.currentStage.menu actor) :
    ProgramHistory program :=
  match moment with
  | .root =>
      match program with
      | .halt => history
      | .decision stage _ _ =>
          history.selectActorAtRoot actor action
            (by simpa [ProgramMoment.currentStage] using action_mem)
  | .afterProfile profile childMoment =>
      match history with
      | .decision historyProfile tail =>
          let hbranches : ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) := by
            change ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) at hmem
            exact hmem
          let hprofile := Classical.choose hbranches
          let hchild := Classical.choose_spec hbranches
          .decision (state := state) profile
            (ProgramHistory.selectActorAtMoment childMoment (hprofile ▸ tail) hchild
              actor action (by simpa [ProgramMoment.currentStage] using action_mem))

/-- Moment-level selection keeps the resulting history through the selected
moment. -/
theorem ProgramHistory.selectActorAtMoment_memHist {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history)
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ moment.currentStage.menu actor) :
    ProgramMoment.memHist program moment
      (ProgramHistory.selectActorAtMoment moment history hmem actor action action_mem) := by
  cases program with
  | halt =>
      cases moment
      exact True.intro
  | decision stage advance continuation =>
      cases moment with
      | root => exact True.intro
      | afterProfile profile childMoment =>
          cases history with
          | decision historyProfile tail =>
              have hbranches : ∃ hprofile : profile = historyProfile,
                  ProgramMoment.memHist (continuation profile) childMoment
                    (hprofile ▸ tail) := by
                change ∃ hprofile : profile = historyProfile,
                  ProgramMoment.memHist (continuation profile) childMoment
                    (hprofile ▸ tail) at hmem
                exact hmem
              let hprofile := Classical.choose hbranches
              have hchild := Classical.choose_spec hbranches
              cases hprofile
              change ∃ hprofile : profile = profile,
                ProgramMoment.memHist (continuation profile) childMoment
                  (ProgramHistory.selectActorAtMoment childMoment tail hchild actor action
                    (by simpa [ProgramMoment.currentStage] using action_mem))
              exact ⟨rfl,
                ProgramHistory.selectActorAtMoment_memHist childMoment tail hchild
                  actor action (by simpa [ProgramMoment.currentStage] using action_mem)⟩

/-- The first complete profile recorded by a decision history. -/
def ProgramHistory.rootProfile {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (history : ProgramHistory
      (FiniteEconomyProgram.decision (state := state) stage advance continuation)) :
    stage.Profile :=
  match history with
  | .decision profile _ => profile

/-- The root profile of a history returned by `selectActorAtRoot` enacts the
requested action for that agent. -/
theorem ProgramHistory.selectActorAtRoot_self {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (history : ProgramHistory
      (FiniteEconomyProgram.decision (state := state) stage advance continuation))
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ stage.menu actor) :
    (ProgramHistory.selectActorAtRoot history actor action action_mem).rootProfile.1 actor =
      action := by
  cases history with
  | decision profile tail =>
      by_cases already_selected : action = profile.1 actor
      · simp [ProgramHistory.selectActorAtRoot, ProgramHistory.rootProfile,
          already_selected]
      · simp [ProgramHistory.selectActorAtRoot, ProgramHistory.rootProfile,
          already_selected, FiniteChoiceStage.replaceProfile_self]

/-- At the root, moment-level selection enacts the requested action. -/
theorem ProgramHistory.selectActorAtMoment_root_enacted {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) (actor : Agent)
    (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈
      (ProgramMoment.currentStage program ProgramMoment.root).menu actor) :
    ProgramHistory.enactedAt
      (ProgramHistory.selectActorAtMoment ProgramMoment.root history
        (ProgramMoment.root_memHist history) actor action action_mem)
      ProgramMoment.root actor = action := by
  cases program with
  | halt =>
      cases history with
      | halt =>
          have haction : action = EconomyAction.idle := by
            simpa [ProgramMoment.currentStage, FiniteChoiceStage.idleOnly] using action_mem
          subst action
          simp [ProgramHistory.selectActorAtMoment, ProgramHistory.enactedAt]
  | decision stage advance continuation =>
      cases history with
      | decision profile tail =>
          have haction_mem : action ∈ stage.menu actor := by
            simpa [ProgramMoment.currentStage] using action_mem
          by_cases hselected : action = profile.1 actor
          · simp [ProgramHistory.selectActorAtMoment, ProgramHistory.selectActorAtRoot,
              ProgramHistory.enactedAt, hselected]
          · simp only [ProgramHistory.selectActorAtMoment, ProgramHistory.selectActorAtRoot,
              hselected]
            exact stage.replaceProfile_self profile actor action haction_mem

/-- Moment-level selection enacts the requested action on any history through
that program moment. -/
theorem ProgramHistory.selectActorAtMoment_enacted {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history)
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ moment.currentStage.menu actor) :
    ProgramHistory.enactedAt
      (ProgramHistory.selectActorAtMoment moment history hmem actor action action_mem)
      moment actor = action := by
  induction moment with
  | root =>
      exact ProgramHistory.selectActorAtMoment_root_enacted history actor action action_mem
  | afterProfile profile childMoment ih =>
      cases history with
      | decision historyProfile tail =>
          have hbranches : ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) := by
            change ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) at hmem
            exact hmem
          let hprofile := Classical.choose hbranches
          have hchild := Classical.choose_spec hbranches
          cases hprofile
          have hchildAction := ih tail hchild
            (by simpa [ProgramMoment.currentStage] using action_mem)
          simpa [ProgramHistory.selectActorAtMoment, ProgramHistory.enactedAt,
            ProgramMoment.currentStage] using hchildAction

/-- Changing one agent's root action preserves each peer's root action. -/
theorem ProgramHistory.selectActorAtMoment_root_other {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) (actor other : Agent)
    (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈
      (ProgramMoment.currentStage program ProgramMoment.root).menu actor)
    (h_other : other ≠ actor) :
    ProgramHistory.enactedAt
      (ProgramHistory.selectActorAtMoment ProgramMoment.root history
        (ProgramMoment.root_memHist history) actor action action_mem)
      ProgramMoment.root other = ProgramHistory.enactedAt history ProgramMoment.root other := by
  cases program with
  | halt =>
      cases history with
      | halt => rfl
  | decision stage advance continuation =>
      cases history with
      | decision profile tail =>
          have haction_mem : action ∈ stage.menu actor := by
            simpa [ProgramMoment.currentStage] using action_mem
          by_cases hselected : action = profile.1 actor
          · simp [ProgramHistory.selectActorAtMoment, ProgramHistory.selectActorAtRoot,
              ProgramHistory.enactedAt, hselected]
          · simp only [ProgramHistory.selectActorAtMoment, ProgramHistory.selectActorAtRoot,
              hselected, ProgramHistory.enactedAt]
            exact stage.replaceProfile_other profile (i := actor) (j := other)
              action haction_mem h_other

/-- Changing one agent's action at any generated moment preserves each peer's
action there. -/
theorem ProgramHistory.selectActorAtMoment_other {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history)
    (actor other : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ moment.currentStage.menu actor)
    (h_other : other ≠ actor) :
    ProgramHistory.enactedAt
      (ProgramHistory.selectActorAtMoment moment history hmem actor action action_mem)
      moment other = ProgramHistory.enactedAt history moment other := by
  induction moment with
  | root =>
      exact ProgramHistory.selectActorAtMoment_root_other history actor other action
        action_mem h_other
  | afterProfile profile childMoment ih =>
      cases history with
      | decision historyProfile tail =>
          have hbranches : ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) := by
            change ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) at hmem
            exact hmem
          let hprofile := Classical.choose hbranches
          have hchild := Classical.choose_spec hbranches
          cases hprofile
          have hchildOther := ih tail hchild
            (by simpa [ProgramMoment.currentStage] using action_mem)
          simpa [ProgramHistory.selectActorAtMoment, ProgramHistory.enactedAt,
            ProgramMoment.currentStage] using hchildOther

/-- If the history already enacts the requested action, moment-level
selection leaves that history unchanged. -/
theorem ProgramHistory.selectActorAtMoment_root_centered {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (history : ProgramHistory program) (actor : Agent)
    (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈
      (ProgramMoment.currentStage program ProgramMoment.root).menu actor)
    (h_enacted : ProgramHistory.enactedAt history ProgramMoment.root actor = action) :
    ProgramHistory.selectActorAtMoment ProgramMoment.root history
      (ProgramMoment.root_memHist history) actor action action_mem = history := by
  cases program with
  | halt =>
      cases history with
      | halt => rfl
  | decision stage advance continuation =>
      cases history with
      | decision profile tail =>
          have hselected : action = profile.1 actor := by
            simpa [ProgramHistory.enactedAt] using h_enacted.symm
          simp [ProgramHistory.selectActorAtMoment, ProgramHistory.selectActorAtRoot, hselected]

/-- Branch selection is centered at every generated program moment. -/
theorem ProgramHistory.selectActorAtMoment_centered {fuel : ℕ} {state : State}
    {program : FiniteEconomyProgram State Agent Means Operation fuel state}
    (moment : ProgramMoment program) (history : ProgramHistory program)
    (hmem : ProgramMoment.memHist program moment history)
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ moment.currentStage.menu actor)
    (h_enacted : ProgramHistory.enactedAt history moment actor = action) :
    ProgramHistory.selectActorAtMoment moment history hmem actor action action_mem = history := by
  induction moment with
  | root =>
      exact ProgramHistory.selectActorAtMoment_root_centered
        history actor action action_mem h_enacted
  | afterProfile profile childMoment ih =>
      cases history with
      | decision historyProfile tail =>
          have hbranches : ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) := by
            change ∃ hprofile : profile = historyProfile,
              ProgramMoment.memHist _ childMoment (hprofile ▸ tail) at hmem
            exact hmem
          let hprofile := Classical.choose hbranches
          have hchild := Classical.choose_spec hbranches
          cases hprofile
          have hchildEnacted : ProgramHistory.enactedAt tail childMoment actor = action := by
            simpa [ProgramHistory.enactedAt] using h_enacted
          have hchildCentered := ih tail hchild
            (by simpa [ProgramMoment.currentStage] using action_mem) hchildEnacted
          simpa [ProgramHistory.selectActorAtMoment] using hchildCentered

/-- Selecting an agent's root alternative preserves every other agent's
simultaneous root action. -/
theorem ProgramHistory.selectActorAtRoot_other {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (history : ProgramHistory
      (FiniteEconomyProgram.decision (state := state) stage advance continuation))
    (actor other : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ stage.menu actor) (h_other : other ≠ actor) :
    (ProgramHistory.selectActorAtRoot history actor action action_mem).rootProfile.1 other =
      history.rootProfile.1 other := by
  cases history with
  | decision profile tail =>
      by_cases already_selected : action = profile.1 actor
      · simp [ProgramHistory.selectActorAtRoot, ProgramHistory.rootProfile,
          already_selected]
      · simp [ProgramHistory.selectActorAtRoot, ProgramHistory.rootProfile,
          already_selected, FiniteChoiceStage.replaceProfile_other, h_other]

/-- The branch selected for an agent's root alternative continues from the
state assigned by the program to the resulting complete profile. -/
theorem ProgramHistory.selectActorAtRoot_successor_state {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (history : ProgramHistory
      (FiniteEconomyProgram.decision (state := state) stage advance continuation))
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ stage.menu actor) :
    ((ProgramHistory.selectActorAtRoot history actor action action_mem).stateTrace.drop 1).head? =
      some (advance
        (ProgramHistory.selectActorAtRoot history actor action action_mem).rootProfile) := by
  cases history with
  | decision profile tail =>
      by_cases already_selected : action = profile.1 actor
      · simp [ProgramHistory.selectActorAtRoot, ProgramHistory.rootProfile,
          ProgramHistory.stateTrace, already_selected,
          ProgramHistory.continuation_trace_starts_at_advance]
      · simp [ProgramHistory.selectActorAtRoot, ProgramHistory.rootProfile,
          ProgramHistory.stateTrace, already_selected,
          ProgramHistory.continuation_trace_starts_at_advance]

/-- Every menu action has an explicit root branch where that agent selects it
and every other agent uses the existing idle action. The branch continues
from the state assigned to that complete profile. -/
theorem ProgramHistory.exists_unilateral_root_branch {fuel : ℕ} {state : State}
    {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ stage.menu actor) :
    ∃ history : ProgramHistory
        (FiniteEconomyProgram.decision (state := state) stage advance continuation),
      history.rootProfile.1 actor = action ∧
      (∀ other, other ≠ actor →
        history.rootProfile.1 other = EconomyAction.idle) ∧
      (history.stateTrace.drop 1).head? = some (advance history.rootProfile) := by
  let profile := stage.unilateralProfile actor action action_mem
  let history := ProgramHistory.afterProfile (state := state)
    (stage := stage) (advance := advance) (continuation := continuation) profile
  refine ⟨history, ?_, ?_, ?_⟩
  · change profile.1 actor = action
    exact stage.unilateralProfile_self actor action action_mem
  · intro other hother
    change profile.1 other = EconomyAction.idle
    exact stage.unilateralProfile_other actor other action action_mem hother
  · change ((ProgramHistory.afterProfile (state := state) (stage := stage)
      (advance := advance) (continuation := continuation) profile).stateTrace.drop 1).head? =
      some (advance
        (ProgramHistory.afterProfile (state := state) (stage := stage)
          (advance := advance) (continuation := continuation) profile).rootProfile)
    simp only [ProgramHistory.afterProfile, ProgramHistory.rootProfile,
      ProgramHistory.stateTrace, List.drop_one]
    exact ProgramHistory.stateTrace_head
      (ProgramHistory.allIdle (continuation profile))

/-- Count program moments by summing the finite child programs. The explicit
fuel index is the structural recursion measure, independent of branch count. -/
def nodeCount {State Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation] :
    (fuel : ℕ) → (state : State) →
      FiniteEconomyProgram State Agent Means Operation fuel state → ℕ
  | 0, _, .halt => 1
  | Nat.succ _, _, .halt => 1
  | Nat.succ fuel, _, .decision stage advance continuation =>
      1 + ∑ profile ∈ stage.profiles,
        nodeCount fuel (advance profile) (continuation profile)

/-- Count terminal histories by summing the terminal histories in every
profile continuation. -/
def historyCount {State Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation] :
    (fuel : ℕ) → (state : State) →
      FiniteEconomyProgram State Agent Means Operation fuel state → ℕ
  | 0, _, .halt => 1
  | Nat.succ _, _, .halt => 1
  | Nat.succ fuel, _, .decision stage advance continuation =>
      ∑ profile ∈ stage.profiles,
        historyCount fuel (advance profile) (continuation profile)

@[simp]
theorem nodeCount_halt {State Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation] (fuel : ℕ) (state : State) :
    nodeCount fuel state
      (FiniteEconomyProgram.halt :
        FiniteEconomyProgram State Agent Means Operation fuel state) = 1 := by
  cases fuel <;> rfl

@[simp]
theorem historyCount_halt {State Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation] (fuel : ℕ) (state : State) :
    historyCount fuel state
      (FiniteEconomyProgram.halt :
        FiniteEconomyProgram State Agent Means Operation fuel state) = 1 := by
  cases fuel <;> rfl

/-- A state transition after a complete profile. Its proof obligations are
kept separate from profile enumeration, allowing the physical interpreter to
provide the advancing function. -/
def continuationFor (fuel : ℕ) (stage : FiniteChoiceStage Agent Means Operation)
    (advance : stage.Profile → State)
    (keys : Finset stage.Profile)
    (continuations : ∀ profile, profile ∈ keys →
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile))
    (profile : stage.Profile) :
    FiniteEconomyProgram State Agent Means Operation fuel (advance profile) :=
  if hprofile : profile ∈ keys then
    continuations profile hprofile
  else
    .halt

/-- Unlisted profiles terminate rather than disappearing from the scenario
tree. -/
theorem continuationFor_unlisted_is_halt
    (fuel : ℕ) (stage : FiniteChoiceStage Agent Means Operation)
    (advance : stage.Profile → State)
    (keys : Finset stage.Profile)
    (continuations : ∀ profile, profile ∈ keys →
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile))
    (profile : stage.Profile) (hprofile : profile ∉ keys) :
    continuationFor fuel stage advance keys continuations profile = .halt := by
  simp [continuationFor, hprofile]

/-- Continue only the supplied profile keys. Every other member of the full
finite profile product becomes an explicit terminal continuation. -/
def continueOn {state : State}
    (fuel : ℕ)
    (stage : FiniteChoiceStage Agent Means Operation)
    (advance : stage.Profile → State)
    (keys : Finset stage.Profile)
    (continuations : ∀ profile, profile ∈ keys →
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)) :
    FiniteEconomyProgram State Agent Means Operation (fuel + 1) state :=
  .decision stage advance (continuationFor fuel stage advance keys continuations)

/-- If a supplied key is in the menu product, its continuation is preserved. -/
theorem continuationFor_listed
    (fuel : ℕ) (stage : FiniteChoiceStage Agent Means Operation)
    (advance : stage.Profile → State)
    (keys : Finset stage.Profile)
    (continuations : ∀ profile, profile ∈ keys →
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile))
    (profile : stage.Profile) (hprofile : profile ∈ keys) :
    continuationFor fuel stage advance keys continuations profile =
      continuations profile hprofile := by
  simp [continuationFor, hprofile]

/-- A physical stage becomes a program node whose child states are computed
by the shared exact inventory interpreter. -/
def physicalDecision {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (fuel : ℕ)
    (stage : FinitePhysicalChoiceStage Agent Means Operation Service)
    (continuation : ∀ profile,
      FiniteEconomyProgram (PhysicalState Agent Means Service)
        Agent Means Operation fuel (stage.advance profile)) :
    FiniteEconomyProgram (PhysicalState Agent Means Service)
      Agent Means Operation (fuel + 1) stage.before :=
  .decision stage.choices stage.advance continuation

/-- The state immediately after a physical program's selected stage profile
is the exact output of the shared physical interpreter. -/
theorem physicalDecision_branch_successor
    {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (fuel : ℕ)
    (stage : FinitePhysicalChoiceStage Agent Means Operation Service)
    (continuation : ∀ profile,
      FiniteEconomyProgram (PhysicalState Agent Means Service)
        Agent Means Operation fuel (stage.advance profile))
    (profile : stage.choices.Profile) :
    ((ProgramHistory.afterProfile (fuel := fuel) (state := stage.before)
      (stage := stage.choices) (advance := stage.advance)
      (continuation := continuation) profile).stateTrace.drop 1).head? =
        some (stage.advance profile) := by
  simp [ProgramHistory.afterProfile, ProgramHistory.stateTrace,
    ProgramHistory.stateTrace_head]

/-- Every selected complete profile on that branch obeys the physical stage's
exact additive stock accounting. -/
theorem physicalDecision_branch_balance
    {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (stage : FinitePhysicalChoiceStage Agent Means Operation Service)
    (profile : stage.choices.Profile) (actor : Agent) (m : Means) :
    (stage.advance profile).stock actor m +
        effectiveUse stage.operations profile.1 actor m =
      stage.before.stock actor m +
        effectiveYield stage.operations profile.1 actor m :=
  stage.advance_balance profile actor m

/-- Replacing one agent's root choice in a physical program still uses the
stage's shared physical transition, so the selected branch's immediate state
satisfies the same exact inventory balance. -/
theorem physicalDecision_selectActorAtRoot_balance
    {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    {fuel : ℕ} (stage : FinitePhysicalChoiceStage Agent Means Operation Service)
    (continuation : ∀ profile,
      FiniteEconomyProgram (PhysicalState Agent Means Service)
        Agent Means Operation fuel (stage.advance profile))
    (history : ProgramHistory
      (FiniteEconomyProgram.physicalDecision fuel stage continuation))
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ stage.choices.menu actor)
    (other : Agent) (m : Means) :
    (stage.advance
      (ProgramHistory.selectActorAtRoot history actor action action_mem).rootProfile).stock
        other m +
        effectiveUse stage.operations
          (ProgramHistory.selectActorAtRoot history actor action action_mem).rootProfile.1
          other m =
      stage.before.stock other m +
        effectiveYield stage.operations
          (ProgramHistory.selectActorAtRoot history actor action action_mem).rootProfile.1
          other m := by
  exact stage.advance_balance
    (ProgramHistory.selectActorAtRoot history actor action action_mem).rootProfile
    other m

/-- Every physically affordable menu alternative has an executed branch where
the selected agent enacts it and all peers idle; the branch's successor state
obeys the shared transition's exact accounting for every inventory. -/
theorem physicalDecision_exists_unilateral_branch
    {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    {fuel : ℕ} (stage : FinitePhysicalChoiceStage Agent Means Operation Service)
    (continuation : ∀ profile,
      FiniteEconomyProgram (PhysicalState Agent Means Service)
        Agent Means Operation fuel (stage.advance profile))
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (action_mem : action ∈ stage.choices.menu actor) :
    ∃ history : ProgramHistory
        (FiniteEconomyProgram.physicalDecision fuel stage continuation),
      history.rootProfile.1 actor = action ∧
      (∀ peer, peer ≠ actor →
        history.rootProfile.1 peer = EconomyAction.idle) ∧
      (∀ peer m,
        (stage.advance history.rootProfile).stock peer m +
            effectiveUse stage.operations history.rootProfile.1 peer m =
          stage.before.stock peer m +
            effectiveYield stage.operations history.rootProfile.1 peer m) := by
  obtain ⟨history, hactor, hpeers, _hnext⟩ :=
    ProgramHistory.exists_unilateral_root_branch
      (stage := stage.choices) (advance := stage.advance)
      (continuation := continuation) actor action action_mem
  refine ⟨history, hactor, hpeers, ?_⟩
  intro peer m
  exact stage.advance_balance history.rootProfile peer m

/-- A physical spine helper uses explicit continuation keys and terminates
every other affordable profile. -/
def physicalContinueOn {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (fuel : ℕ)
    (stage : FinitePhysicalChoiceStage Agent Means Operation Service)
    (keys : Finset stage.choices.Profile)
    (continuations : ∀ profile, profile ∈ keys →
      FiniteEconomyProgram (PhysicalState Agent Means Service)
        Agent Means Operation fuel (stage.advance profile)) :
    FiniteEconomyProgram (PhysicalState Agent Means Service)
      Agent Means Operation (fuel + 1) stage.before :=
  FiniteEconomyProgram.continueOn fuel stage.choices stage.advance keys continuations

end FiniteEconomyProgram

/-- A branching program restricted to the shared physical interpreter. Each
decision stage receives its successor states from
`FinitePhysicalChoiceStage.advance`; callers cannot provide an unrelated
state-update function in this physical layer. -/
inductive FinitePhysicalEconomyProgram (Agent Means Operation Service : Type)
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation] :
    ℕ → PhysicalState Agent Means Service → Type where
  | halt {fuel : ℕ} {state : PhysicalState Agent Means Service} :
      FinitePhysicalEconomyProgram Agent Means Operation Service fuel state
  | decision {fuel : ℕ} {state : PhysicalState Agent Means Service}
      (stage : FinitePhysicalChoiceStage Agent Means Operation Service)
      (continuation : ∀ profile,
        FinitePhysicalEconomyProgram Agent Means Operation Service
          fuel (stage.advance profile)) :
      FinitePhysicalEconomyProgram Agent Means Operation Service
        (fuel + 1) stage.before

namespace FinitePhysicalEconomyProgram

variable {Agent Means Operation Service : Type}
variable [Fintype Agent] [DecidableEq Agent] [Fintype Means]
  [DecidableEq Means] [DecidableEq Operation]

/-- Lower a physical program to the existing complete-profile program. This
translation preserves each physical stage's interpreter as its state
transition. -/
def toFiniteEconomyProgram : {fuel : ℕ} →
    {state : PhysicalState Agent Means Service} →
    FinitePhysicalEconomyProgram Agent Means Operation Service fuel state →
      FiniteEconomyProgram (PhysicalState Agent Means Service)
        Agent Means Operation fuel state
  | _, _, .halt => .halt
  | fuel + 1, _, .decision stage continuation =>
      FiniteEconomyProgram.physicalDecision fuel stage fun profile =>
        toFiniteEconomyProgram (continuation profile)

/-- The legacy `ActionFrame` interface gives every action one time-invariant
use and yield schedule. A physical program can supply that field directly
when the stage-level operation semantics agree with one shared schedule. -/
def HasStableOperationSemantics : {fuel : ℕ} →
    {state : PhysicalState Agent Means Service} →
    FinitePhysicalEconomyProgram Agent Means Operation Service fuel state →
    OperationSemantics Operation Means Service → Prop
  | _, _, .halt, _ => True
  | _, _, .decision stage continuation, operations =>
      stage.operations = operations ∧
        ∀ profile, HasStableOperationSemantics (continuation profile) operations

/-- Stability at a program root is the stage's explicit operation schedule. -/
theorem HasStableOperationSemantics.root {fuel : ℕ}
    {stage : FinitePhysicalChoiceStage Agent Means Operation Service}
    {continuation : ∀ profile,
      FinitePhysicalEconomyProgram Agent Means Operation Service fuel
        (stage.advance profile)}
    {operations : OperationSemantics Operation Means Service}
    (hstable : HasStableOperationSemantics
      (.decision (state := stage.before) stage continuation :
        FinitePhysicalEconomyProgram Agent Means Operation Service
          (fuel + 1) stage.before) operations) :
    stage.operations = operations :=
  hstable.1

/-- Stability propagates into every profile continuation. -/
theorem HasStableOperationSemantics.continuation {fuel : ℕ}
    {stage : FinitePhysicalChoiceStage Agent Means Operation Service}
    {continuation : ∀ profile,
      FinitePhysicalEconomyProgram Agent Means Operation Service fuel
        (stage.advance profile)}
    {operations : OperationSemantics Operation Means Service}
    (hstable : HasStableOperationSemantics
      (.decision (state := stage.before) stage continuation :
        FinitePhysicalEconomyProgram Agent Means Operation Service
          (fuel + 1) stage.before) operations)
    (profile : stage.choices.Profile) :
    HasStableOperationSemantics (continuation profile) operations :=
  hstable.2 profile

/-- A stage-stable physical program supplies the generic program's complete
pre-transition affordability and exact stock-accounting certificate. -/
theorem physicalAccounting_of_stableOperations {fuel : ℕ}
    {state : PhysicalState Agent Means Service}
    (program : FinitePhysicalEconomyProgram Agent Means Operation Service fuel state)
    (operations : OperationSemantics Operation Means Service)
    (hstable : program.HasStableOperationSemantics operations) :
    FiniteEconomyProgram.PhysicalAccounting
      (fun current actor m => current.stock actor m) operations
      program.toFiniteEconomyProgram := by
  induction program with
  | halt => trivial
  | @decision fuel state stage continuation ih =>
      rcases hstable with ⟨hoperations, hcontinuations⟩
      refine ⟨?_, ?_, ?_⟩
      · intro actor action haction m
        have hraw := stage.menu_affordable actor action haction m
        simpa [actionAffordable, hoperations] using hraw
      · intro profile actor m
        simpa [hoperations] using stage.advance_balance profile actor m
      · intro profile
        exact ih profile (hcontinuations profile)

/-- Histories of a physical program use the generic complete-profile path
representation after lowering the physical transitions. -/
abbrev History {fuel : ℕ} {state : PhysicalState Agent Means Service}
    (program : FinitePhysicalEconomyProgram Agent Means Operation Service fuel state) :=
  FiniteEconomyProgram.ProgramHistory program.toFiniteEconomyProgram

/-- Every physical program has a typed all-idle history, using the baseline
action already required by each stage's menus. -/
def allIdleHistory {fuel : ℕ} {state : PhysicalState Agent Means Service}
    (program : FinitePhysicalEconomyProgram Agent Means Operation Service fuel state) :
    History program :=
  FiniteEconomyProgram.ProgramHistory.allIdle program.toFiniteEconomyProgram

/-- Every action enacted along a physical-program history is funded at the
state generated at that moment, provided the stage interpreters use one shared
operation schedule. -/
theorem enactedAt_affordable {fuel : ℕ} {state : PhysicalState Agent Means Service}
    (program : FinitePhysicalEconomyProgram Agent Means Operation Service fuel state)
    (operations : OperationSemantics Operation Means Service)
    (hstable : program.HasStableOperationSemantics operations)
    (history : History program)
    (moment : FiniteEconomyProgram.ProgramMoment program.toFiniteEconomyProgram)
    (hmem : FiniteEconomyProgram.ProgramMoment.memHist
      program.toFiniteEconomyProgram moment history)
    (actor : Agent) (m : Means) :
    rawActionUse operations
        (FiniteEconomyProgram.ProgramHistory.enactedAt history moment actor) m ≤
      (moment.currentState).stock actor m := by
  exact FiniteEconomyProgram.ProgramHistory.enactedAt_rawActionUse_le_stock
    (fun current actor m => current.stock actor m) operations
    (physicalAccounting_of_stableOperations program operations hstable)
    moment history hmem actor m

/-- Every stage/profile branch in a physical program satisfies the exact stock
and service accounting laws from its `FinitePhysicalChoiceStage` interpreter.
-/
def allBranchesAccounted : {fuel : ℕ} →
    {state : PhysicalState Agent Means Service} →
    FinitePhysicalEconomyProgram Agent Means Operation Service fuel state → Prop
  | _, _, .halt => True
  | Nat.succ _, _, .decision stage continuation =>
      (∀ profile actor m,
        (stage.advance profile).stock actor m +
            effectiveUse stage.operations profile.1 actor m =
          stage.before.stock actor m +
            effectiveYield stage.operations profile.1 actor m) ∧
      (∀ profile actor service,
        (stage.advance profile).services actor service =
          stage.before.services actor service +
            effectiveServiceYield stage.operations profile.1 actor service) ∧
      (∀ profile, allBranchesAccounted (continuation profile))

/-- The accounting certificate for every branch is constructed recursively
from the physical stage interpreter; it adds no separate inventory rule. -/
theorem allBranchesAccountedWitness : {fuel : ℕ} →
    {state : PhysicalState Agent Means Service} →
    (program : FinitePhysicalEconomyProgram Agent Means Operation Service fuel state) →
    program.allBranchesAccounted
  | _, _, .halt => trivial
  | Nat.succ _, _, .decision stage continuation =>
      ⟨fun profile actor m => stage.advance_balance profile actor m,
        fun profile actor service =>
          stage.advance_service_balance profile actor service,
        fun profile => allBranchesAccountedWitness (continuation profile)⟩

end FinitePhysicalEconomyProgram

/-- Flatten a finite branching program to a parent-pointer tree. The full
profile product is retained: one child subtree is assembled for every
feasible profile, including branches whose program immediately halts. The
tree compiler carries no preference or doxastic semantics; those remain
fields and laws of any `ActionFrame` used to interpret the program. -/
noncomputable def compileFiniteProgramTree {State Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation] :
    (fuel : ℕ) → {state : State} →
      FiniteEconomyProgram State Agent Means Operation fuel state → FiniteTreeSpec
  | 0, _, .halt => FiniteTreeSpec.rootOnly
  | Nat.succ _, _, .halt => FiniteTreeSpec.rootOnly
  | Nat.succ fuel, _, .decision stage _ continuation =>
      FiniteTreeSpec.assembleChildren
        (stage.profiles.toList.map fun profile =>
          compileFiniteProgramTree fuel (continuation profile))

/-- The parent-pointer flattening preserves the exact number of program
moments: one decision moment plus every profile continuation's complete
subtree. -/
theorem compileFiniteProgramTree_nodeCount {State Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation]
    (fuel : ℕ) (state : State)
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) :
    (compileFiniteProgramTree fuel program).extraNodes + 1 =
      FiniteEconomyProgram.nodeCount fuel state program := by
  induction fuel generalizing state with
  | zero =>
      cases program
      rfl
  | succ fuel ih =>
      cases program with
      | halt => rfl
      | decision stage advance continuation =>
          simp only [compileFiniteProgramTree, FiniteEconomyProgram.nodeCount,
            FiniteTreeSpec.assembleChildren_size]
          simp only [List.map_map]
          rw [Finset.sum_map_toList]
          apply congrArg (fun n : ℕ => 1 + n)
          apply Finset.sum_congr rfl
          intro profile hprofile
          exact ih (advance profile) (continuation profile)

/-- The compiled tree and the branching program agree on total moment
counting, independently of how many agents are represented in each profile. -/
theorem compileFiniteProgramTree_size_eq_nodeCount {State Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation]
    (fuel : ℕ) (state : State)
    (program : FiniteEconomyProgram State Agent Means Operation fuel state) :
    (compileFiniteProgramTree fuel program).extraNodes + 1 =
      FiniteEconomyProgram.nodeCount fuel state program :=
  compileFiniteProgramTree_nodeCount fuel state program

namespace FinitePhysicalEconomyProgram

variable {Agent Means Operation Service : Type}
variable [Fintype Agent] [DecidableEq Agent] [Fintype Means]
  [DecidableEq Means] [DecidableEq Operation]

/-- Compile a physical scenario program through the existing finite branching
tree compiler after lowering each stage to its interpreter-defined successor
states. -/
noncomputable def compileTree {fuel : ℕ} {state : PhysicalState Agent Means Service}
    (program : FinitePhysicalEconomyProgram Agent Means Operation Service fuel state) :
    FiniteTreeSpec :=
  compileFiniteProgramTree fuel program.toFiniteEconomyProgram

/-- The physical tree retains the generic compiler's exact node count. -/
theorem compileTree_size_eq_nodeCount {fuel : ℕ}
    {state : PhysicalState Agent Means Service}
    (program : FinitePhysicalEconomyProgram Agent Means Operation Service fuel state) :
    program.compileTree.extraNodes + 1 =
      FiniteEconomyProgram.nodeCount fuel state program.toFiniteEconomyProgram :=
  compileFiniteProgramTree_nodeCount fuel state program.toFiniteEconomyProgram

end FinitePhysicalEconomyProgram

/-- A compact single-continuation recipe. At each stage one complete profile
continues to the next stage; all other profiles are later compiled as
terminal children. -/
inductive FiniteEconomySpineRecipe (State Agent Means Operation : Type)
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation] : State → Type where
  | halt {state : State} : FiniteEconomySpineRecipe State Agent Means Operation state
  | step {state : State}
      (stage : FiniteChoiceStage Agent Means Operation)
      (advance : stage.Profile → State)
      (selected : stage.Profile)
      (tail : FiniteEconomySpineRecipe State Agent Means Operation
        (advance selected)) :
      FiniteEconomySpineRecipe State Agent Means Operation state

namespace FiniteEconomySpineRecipe

variable {State Agent Means Operation : Type}
variable [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
  [DecidableEq Operation]

/-- Maximum number of decision nodes on a continuation path. -/
def depth {state : State} :
    FiniteEconomySpineRecipe State Agent Means Operation state → ℕ
  | .halt => 0
  | .step _ _ _ tail => Nat.succ tail.depth

/-- The spine recipe's expected moment count. Each stage creates one child
for every complete profile, with exactly one child continuing the spine. -/
def expectedNodeCount {state : State} :
    FiniteEconomySpineRecipe State Agent Means Operation state → ℕ
  | .halt => 1
  | .step stage _ _ tail => stage.profiles.card + tail.expectedNodeCount

/-- The spine recipe's expected terminal-history count. All profiles except
the designated continuation terminate at the current stage. -/
def expectedHistoryCount {state : State} :
    FiniteEconomySpineRecipe State Agent Means Operation state → ℕ
  | .halt => 1
  | .step stage _ _ tail =>
      (stage.profiles.card - 1) + tail.expectedHistoryCount

/-- Profile-count blocks in preorder. In a spine, one stage contributes one
child moment for each complete profile; the selected profile's child is the
root of the remaining recipe. -/
def stageProfileCounts {state : State} :
    FiniteEconomySpineRecipe State Agent Means Operation state → List ℕ
  | .halt => []
  | .step stage _ _ tail => stage.profiles.card :: tail.stageProfileCounts

/-- Parent offset for a flattened spine. `n` is measured from the beginning
of the recipe's block. The first `k` nodes belong to the current root, and
later nodes recurse from the selected child at offset `k`. -/
def parentOffset : List ℕ → ℕ → ℕ
  | [], _ => 0
  | k :: rest, n => if n ≤ k then 0 else k + parentOffset rest (n - k)

theorem parentOffset_zero (counts : List ℕ) : parentOffset counts 0 = 0 := by
  cases counts with
  | nil => rfl
  | cons k rest => simp [parentOffset]

/-- Every non-root parent offset is strictly earlier, provided the node lies
inside the flattened block. -/
theorem parentOffset_lt (counts : List ℕ) {n : ℕ}
    (hn : 0 < n) (hbound : n ≤ counts.sum) :
    parentOffset counts n < n := by
  induction counts generalizing n with
  | nil => simp at hbound; omega
  | cons k rest ih =>
      have hsum : n ≤ k + rest.sum := by simpa using hbound
      by_cases hnk : n ≤ k
      · simp [parentOffset, hnk]
        omega
      · have hkn : k < n := Nat.lt_of_not_ge hnk
        have htailBound : n - k ≤ rest.sum := by omega
        have htailPos : 0 < n - k := Nat.sub_pos_of_lt hkn
        have htail := ih htailPos htailBound
        simp [parentOffset, hnk]
        omega

/-- Convert one natural-number parent offset into the bounded moment index
used by `FiniteTreeSpec`. -/
def parentNode {state : State}
    (R : FiniteEconomySpineRecipe State Agent Means Operation state) :
    Fin (R.stageProfileCounts.sum + 1) → Fin (R.stageProfileCounts.sum + 1) :=
  fun n => ⟨parentOffset R.stageProfileCounts n.val, by
    have hbound : n.val ≤ R.stageProfileCounts.sum := by omega
    have hparent : parentOffset R.stageProfileCounts n.val ≤
        R.stageProfileCounts.sum := by
      by_cases hn : n.val = 0
      · have hnEq : n = 0 := Fin.ext hn
        subst n
        simp [parentOffset_zero]
      · have hnpos : 0 < n.val := by omega
        have hlt := parentOffset_lt R.stageProfileCounts hnpos hbound
        omega
    exact Nat.lt_succ_iff.mpr hparent⟩

/-- Compile a single-continuation recipe to its preorder parent-pointer tree.
At each step the profile children are contiguous; all profile children attach
to the current root, and the final child in that block starts the tail. -/
def compileTree {state : State}
    (R : FiniteEconomySpineRecipe State Agent Means Operation state) :
    FiniteTreeSpec where
  extraNodes := R.stageProfileCounts.sum
  parent := R.parentNode
  parent_root := by
    apply Fin.ext
    simp [parentNode, parentOffset_zero]
  parent_decreases := by
    intro n hn
    change parentOffset R.stageProfileCounts n.val < n.val
    have hnpos : 0 < n.val := by
      by_contra h
      have : n.val = 0 := by omega
      exact hn (Fin.ext this)
    have hbound : n.val ≤ R.stageProfileCounts.sum := by omega
    exact parentOffset_lt R.stageProfileCounts hnpos hbound

/-- The flattened tree has one root plus one child for every profile at every
stage, exactly matching the program's structural node count. -/
theorem compileTree_nodeCount {state : State}
    (R : FiniteEconomySpineRecipe State Agent Means Operation state) :
    R.compileTree.extraNodes + 1 = R.expectedNodeCount := by
  induction R with
  | halt => rfl
  | @step state stage advance selected tail ih =>
      simp only [compileTree, stageProfileCounts, expectedNodeCount, List.sum_cons]
      have htail : tail.stageProfileCounts.sum + 1 = tail.expectedNodeCount := by
        simpa [compileTree] using ih
      omega

/-- Compile a spine recipe into a total profile program. The selected profile
continues; the dependent equality cast aligns its state with that branch. -/
def compile {state : State} :
    (recipe : FiniteEconomySpineRecipe State Agent Means Operation state) →
    FiniteEconomyProgram State Agent Means Operation recipe.depth state
  | .halt => .halt
  | .step stage advance selected tail =>
      .decision stage advance (fun profile =>
        if h : profile = selected then
          cast (by cases h; rfl) tail.compile
        else
          .halt)

/-- The compiled program has the recipe's expected moment count. -/
theorem compile_nodeCount {state : State}
    (recipe : FiniteEconomySpineRecipe State Agent Means Operation state) :
    FiniteEconomyProgram.nodeCount recipe.depth state recipe.compile =
      recipe.expectedNodeCount := by
  induction recipe with
  | halt => rfl
  | @step state stage advance selected tail ih =>
      let branch : (profile : stage.Profile) →
          FiniteEconomyProgram State Agent Means Operation tail.depth
            (advance profile) := fun profile =>
        if h : profile = selected then
          cast (by cases h; rfl) tail.compile
        else
          .halt
      have hselected : selected ∈ stage.profiles := stage.mem_profiles selected
      have hrest : ∀ profile ∈ stage.profiles.erase selected,
          FiniteEconomyProgram.nodeCount tail.depth (advance profile)
            (branch profile) = 1 := by
        intro profile hprofile
        have hne : profile ≠ selected := (Finset.mem_erase.mp hprofile).1
        simp [branch, hne]
      have hrestSum :
          (∑ profile ∈ stage.profiles.erase selected,
            FiniteEconomyProgram.nodeCount tail.depth (advance profile)
              (branch profile)) = stage.profiles.card - 1 := by
        calc
          _ = ∑ profile ∈ stage.profiles.erase selected, (1 : ℕ) :=
            Finset.sum_congr rfl hrest
          _ = (stage.profiles.erase selected).card := by simp
          _ = stage.profiles.card - 1 := by
            simp [Finset.card_erase_of_mem hselected]
      have hselectedCount :
          FiniteEconomyProgram.nodeCount tail.depth (advance selected)
              (branch selected) = tail.expectedNodeCount := by
        simpa [branch] using ih
      calc
        1 + (∑ profile ∈ stage.profiles,
          FiniteEconomyProgram.nodeCount tail.depth (advance profile)
            (branch profile)) =
          1 + ((∑ profile ∈ stage.profiles.erase selected,
            FiniteEconomyProgram.nodeCount tail.depth (advance profile)
              (branch profile)) +
            FiniteEconomyProgram.nodeCount tail.depth (advance selected)
              (branch selected)) := by
                rw [← Finset.sum_erase_add stage.profiles
                  (fun profile => FiniteEconomyProgram.nodeCount tail.depth
                    (advance profile) (branch profile)) hselected]
        _ = 1 + ((stage.profiles.card - 1) + tail.expectedNodeCount) := by
          rw [hrestSum, hselectedCount]
        _ = stage.profiles.card + tail.expectedNodeCount := by
          have hcard : 1 ≤ stage.profiles.card := Finset.card_pos.mpr
            ⟨selected, hselected⟩
          omega

/-- The spine program's recursive branch count and its generated finite tree
use the same number of moments. -/
theorem compileTree_size_eq_program_nodeCount {state : State}
    (R : FiniteEconomySpineRecipe State Agent Means Operation state) :
    R.compileTree.extraNodes + 1 =
      FiniteEconomyProgram.nodeCount R.depth state R.compile := by
  rw [R.compileTree_nodeCount, R.compile_nodeCount]

/-- The compiled spine has exactly the declared number of terminal
histories: one for each nonselected profile, plus the selected tail's
histories. -/
theorem compile_historyCount {state : State}
    (recipe : FiniteEconomySpineRecipe State Agent Means Operation state) :
    FiniteEconomyProgram.historyCount recipe.depth state recipe.compile =
      recipe.expectedHistoryCount := by
  induction recipe with
  | halt => rfl
  | @step state stage advance selected tail ih =>
      let branch : (profile : stage.Profile) →
          FiniteEconomyProgram State Agent Means Operation tail.depth
            (advance profile) := fun profile =>
        if h : profile = selected then
          cast (by cases h; rfl) tail.compile
        else
          .halt
      have hselected : selected ∈ stage.profiles := stage.mem_profiles selected
      have hrest : ∀ profile ∈ stage.profiles.erase selected,
          FiniteEconomyProgram.historyCount tail.depth (advance profile)
            (branch profile) = 1 := by
        intro profile hprofile
        have hne : profile ≠ selected := (Finset.mem_erase.mp hprofile).1
        simp [branch, hne]
      have hrestSum :
          (∑ profile ∈ stage.profiles.erase selected,
            FiniteEconomyProgram.historyCount tail.depth (advance profile)
              (branch profile)) = stage.profiles.card - 1 := by
        calc
          _ = ∑ profile ∈ stage.profiles.erase selected, (1 : ℕ) :=
            Finset.sum_congr rfl hrest
          _ = (stage.profiles.erase selected).card := by simp
          _ = stage.profiles.card - 1 := by
            simp [Finset.card_erase_of_mem hselected]
      have hselectedCount :
          FiniteEconomyProgram.historyCount tail.depth (advance selected)
              (branch selected) = tail.expectedHistoryCount := by
        simpa [branch] using ih
      calc
        (∑ profile ∈ stage.profiles,
          FiniteEconomyProgram.historyCount tail.depth (advance profile)
            (branch profile)) =
          (∑ profile ∈ stage.profiles.erase selected,
            FiniteEconomyProgram.historyCount tail.depth (advance profile)
              (branch profile)) +
            FiniteEconomyProgram.historyCount tail.depth (advance selected)
              (branch selected) := by
                rw [← Finset.sum_erase_add stage.profiles
                  (fun profile => FiniteEconomyProgram.historyCount tail.depth
                    (advance profile) (branch profile)) hselected]
        _ = (stage.profiles.card - 1) + tail.expectedHistoryCount := by
          rw [hrestSum, hselectedCount]

end FiniteEconomySpineRecipe

end Praxeology

end
