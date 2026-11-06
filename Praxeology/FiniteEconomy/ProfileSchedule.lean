/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Program

/-!
# Physical programs from scheduled action profiles

A finite schedule supplies a proposed profile and explicit additional actions
at each stage. At a given pre-state, unaffordable actions are excluded using
the existing affordability relation. Every listed affordable action has a
unilateral branch; the shared physical interpreter decides which bilateral
transfers match. Schedules and menus are scenario inputs, while all state
changes come from the physical program.
-/

@[expose] public section

namespace Praxeology

/-- One well-formed complete profile proposed at a scheduled physical stage. -/
structure PhysicalProfileInstruction (Agent Means Operation : Type)
    [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation] where
  profile : ActionProfile (Agent := Agent) (Means := Means)
    (Operation := Operation)
  wellFormed : ∀ actor, EconomyAction.WellFormed actor (profile actor)
  /-- Additional contemplated actions, independent of the scheduled action.
  This lets a schedule retain an action alternative even when its selected
  profile idles. -/
  alternatives : Agent → Finset (EconomyAction Agent Means Operation)
  alternatives_wellFormed : ∀ actor action, action ∈ alternatives actor →
    EconomyAction.WellFormed actor action

namespace PhysicalProfileInstruction

variable {Agent Means Operation Service : Type}
variable [Fintype Agent] [DecidableEq Agent] [Fintype Means]
  [DecidableEq Means] [DecidableEq Operation]

/-- The proposed action when individually affordable, and idle otherwise. -/
def affordableProfile (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation) :
    ActionProfile (Agent := Agent) (Means := Means) (Operation := Operation) :=
  fun actor =>
    if actionAffordable operations state actor (instruction.profile actor) then
      instruction.profile actor else .idle

omit [Fintype Agent] in
theorem affordableProfile_affordable
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation)
    (actor : Agent) :
    actionAffordable operations state actor
      (instruction.affordableProfile operations state actor) := by
  by_cases h : actionAffordable operations state actor (instruction.profile actor)
  · simp [affordableProfile, h]
  · intro means
    simp [affordableProfile, h, rawActionUse]

omit [Fintype Agent] in
theorem affordableProfile_wellFormed
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation)
    (actor : Agent) :
    EconomyAction.WellFormed actor
      (instruction.affordableProfile operations state actor) := by
  by_cases h : actionAffordable operations state actor (instruction.profile actor)
  · simpa [affordableProfile, h] using instruction.wellFormed actor
  · simp [affordableProfile, h, EconomyAction.WellFormed]

/-- Filter explicitly contemplated actions by affordability at the common
pre-transition state. -/
def affordableAlternatives (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation)
    (actor : Agent) : Finset (EconomyAction Agent Means Operation) :=
  (instruction.alternatives actor).filter fun action =>
    actionAffordable operations state actor action

/-- The stage menu contains idle, the affordable scheduled action, and every
affordable action explicitly listed as an alternative. -/
def stageMenu (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation)
    (actor : Agent) : Finset (EconomyAction Agent Means Operation) :=
  insert EconomyAction.idle <| insert
    (instruction.affordableProfile operations state actor)
    (instruction.affordableAlternatives operations state actor)

/-- A scheduled profile becomes a physical choice stage. Only the listed
alternatives are added; this does not assume a complete menu of every action. -/
def stage (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation) :
    FinitePhysicalChoiceStage Agent Means Operation Service := by
  let menu := instruction.stageMenu operations state
  let active := Finset.univ.filter fun actor =>
    ∃ action ∈ menu actor, action ≠ EconomyAction.idle
  have hwellFormed : ∀ actor action, action ∈ menu actor →
      EconomyAction.WellFormed actor action := by
    intro actor action haction
    change action ∈ instruction.stageMenu operations state actor at haction
    simp only [stageMenu, Finset.mem_insert] at haction
    rcases haction with hidle | haction
    · subst action
      simp [EconomyAction.WellFormed]
    · rcases haction with hprofile | halternative
      · subst action
        exact instruction.affordableProfile_wellFormed operations state actor
      · exact instruction.alternatives_wellFormed actor action
          (Finset.mem_filter.mp halternative).1
  have haffordable : ∀ actor action, action ∈ menu actor →
      actionAffordable operations state actor action := by
    intro actor action haction
    change action ∈ instruction.stageMenu operations state actor at haction
    simp only [stageMenu, Finset.mem_insert] at haction
    rcases haction with hidle | haction
    · subst action
      intro means
      simp [rawActionUse]
    · rcases haction with hprofile | halternative
      · subst action
        exact instruction.affordableProfile_affordable operations state actor
      · exact (Finset.mem_filter.mp halternative).2
  exact
    { choices := {
        menu := menu
        idle_mem := by
          intro actor
          simp [menu, PhysicalProfileInstruction.stageMenu]
        activeAgents := active
        active_iff := by
          intro actor
          simp [active, menu]
        maxActiveAgents := active.card
        activity_bound := le_rfl
        menu_wellFormed := hwellFormed }
      operations := operations
      before := state
      menu_affordable := by
        intro actor action haction
        exact haffordable actor action haction }

/-- The complete profile that enacts every individually affordable scheduled
action. Its membership follows from the stage's generated menus. -/
def selectedProfile (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation) :
    (instruction.stage operations state).choices.Profile := by
  let profile := instruction.affordableProfile operations state
  refine ⟨profile, ?_⟩
  intro actor
  change profile actor ∈ instruction.stageMenu operations state actor
  simp [stageMenu, profile]

/-- Every scheduled action has a generated unilateral branch in which its
actor selects that action and the other agents idle. -/
theorem stage_has_unilateral_branch
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation)
    (actor : Agent) :
    ∃ profile ∈ (instruction.stage operations state).choices.profiles,
      profile.1 actor = instruction.affordableProfile operations state actor ∧
      ∀ other, other ≠ actor → profile.1 other = EconomyAction.idle := by
  have hmem : instruction.affordableProfile operations state actor ∈
      (instruction.stage operations state).choices.menu actor := by
    change instruction.affordableProfile operations state actor ∈
      instruction.stageMenu operations state actor
    simp [stageMenu]
  exact (instruction.stage operations state).choices.exists_unilateral_profile
    actor _ hmem

/-- Every affordable action explicitly listed as an alternative has a branch
where its actor chooses it and all other agents idle. -/
theorem stage_has_unilateral_alternative_branch
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instruction : PhysicalProfileInstruction Agent Means Operation)
    (actor : Agent) (action : EconomyAction Agent Means Operation)
    (halternative : action ∈
      instruction.affordableAlternatives operations state actor) :
    ∃ profile ∈ (instruction.stage operations state).choices.profiles,
      profile.1 actor = action ∧
      ∀ other, other ≠ actor → profile.1 other = EconomyAction.idle := by
  have hmenu : action ∈
      (instruction.stage operations state).choices.menu actor := by
    change action ∈ instruction.stageMenu operations state actor
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem halternative)
  exact (instruction.stage operations state).choices.exists_unilateral_profile
    actor action hmenu

end PhysicalProfileInstruction

/-- A fuel-bounded instruction source. The next instruction can depend on the
finite cursor and the physical state produced so far. The cursor transition
receives the profile actually selected in the generated stage and its
interpreter-derived successor state, so a model can record only transfers
that actually matched while consuming every instruction position. -/
structure PhysicalProfileGenerator (Agent Means Operation Service Cursor : Type)
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation] where
  instruction : Cursor → PhysicalState Agent Means Service →
    PhysicalProfileInstruction Agent Means Operation
  nextCursor : Cursor → PhysicalState Agent Means Service →
    ActionProfile (Agent := Agent) (Means := Means) (Operation := Operation) →
      PhysicalState Agent Means Service → Cursor

/-- Compile a state-dependent instruction generator for a statically bounded
number of stages. Each recursive branch advances the cursor exactly once,
regardless of whether its proposed transfer matched. -/
def compilePhysicalProfileGenerator {Agent Means Operation Service Cursor : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (generator : PhysicalProfileGenerator Agent Means Operation Service Cursor) :
    (fuel : ℕ) → Cursor → (state : PhysicalState Agent Means Service) →
      FinitePhysicalEconomyProgram Agent Means Operation Service fuel state
  | 0, _, _ => .halt
  | fuel + 1, cursor, state =>
      let instruction := generator.instruction cursor state
      let stage := instruction.stage operations state
      .decision (state := state) stage fun profile =>
        compilePhysicalProfileGenerator operations generator fuel
          (generator.nextCursor cursor state profile.1 (stage.advance profile))
          (stage.advance profile)

/-- The state-dependent compiler reuses the instruction's existing physical
stage, so every recursive node has the supplied operation semantics. -/
theorem compilePhysicalProfileGenerator_stable
    {Agent Means Operation Service Cursor : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (generator : PhysicalProfileGenerator Agent Means Operation Service Cursor)
    (fuel : ℕ) (cursor : Cursor)
    (state : PhysicalState Agent Means Service) :
    FinitePhysicalEconomyProgram.HasStableOperationSemantics
      (compilePhysicalProfileGenerator operations generator fuel cursor state)
      operations := by
  induction fuel generalizing cursor state with
  | zero => simp [compilePhysicalProfileGenerator,
      FinitePhysicalEconomyProgram.HasStableOperationSemantics]
  | succ fuel ih =>
      simp only [compilePhysicalProfileGenerator,
        FinitePhysicalEconomyProgram.HasStableOperationSemantics]
      constructor
      · rfl
      · intro profile
        exact ih _ _

/-- Execute the generator's affordable scheduled profile at each stage. -/
def executePhysicalProfileGenerator {Agent Means Operation Service Cursor : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (generator : PhysicalProfileGenerator Agent Means Operation Service Cursor) :
    (fuel : ℕ) → Cursor → PhysicalState Agent Means Service →
      PhysicalState Agent Means Service
  | 0, _, state => state
  | fuel + 1, cursor, state =>
      let instruction := generator.instruction cursor state
      let stage := instruction.stage operations state
      let profile := instruction.selectedProfile operations state
      executePhysicalProfileGenerator operations generator fuel
        (generator.nextCursor cursor state profile.1 (stage.advance profile))
        (stage.advance profile)

/-- The generator's selected profiles form a history of its compiled
branching program. -/
def physicalProfileGeneratorHistory {Agent Means Operation Service Cursor : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (generator : PhysicalProfileGenerator Agent Means Operation Service Cursor) :
    (fuel : ℕ) → (cursor : Cursor) → (state : PhysicalState Agent Means Service) →
      FinitePhysicalEconomyProgram.History
        (compilePhysicalProfileGenerator operations generator fuel cursor state)
  | 0, _, _ => FiniteEconomyProgram.ProgramHistory.halt
  | fuel + 1, cursor, state =>
      let instruction := generator.instruction cursor state
      let stage := instruction.stage operations state
      let profile := instruction.selectedProfile operations state
      FiniteEconomyProgram.ProgramHistory.decision profile
        (physicalProfileGeneratorHistory operations generator fuel
          (generator.nextCursor cursor state profile.1 (stage.advance profile))
          (stage.advance profile))

/-- The generator history's terminal state is the interpreter result of the
same generated profiles. -/
theorem physicalProfileGeneratorHistory_terminalState
    {Agent Means Operation Service Cursor : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (generator : PhysicalProfileGenerator Agent Means Operation Service Cursor)
    (fuel : ℕ) (cursor : Cursor)
    (state : PhysicalState Agent Means Service) :
    (physicalProfileGeneratorHistory operations generator fuel cursor state).terminalState =
      executePhysicalProfileGenerator operations generator fuel cursor state := by
  induction fuel generalizing cursor state with
  | zero => rfl
  | succ fuel ih => exact ih _ _

/-- Idle fallback for the fixed-list generator. With fuel equal to the list
length the fallback is never reached; it only makes the generator total for
arbitrary cursors. -/
def idlePhysicalProfileInstruction {Agent Means Operation : Type}
    [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation] :
    PhysicalProfileInstruction Agent Means Operation where
  profile := fun _ => .idle
  wellFormed := by intro actor; simp [EconomyAction.WellFormed]
  alternatives := fun _ => ∅
  alternatives_wellFormed := by intro actor action h; simp at h

/-- A fixed list is a specialization of the state-dependent generator: its
cursor is the remaining list, and the next instruction ignores state. -/
def fixedPhysicalProfileGenerator {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (_instructions : List (PhysicalProfileInstruction Agent Means Operation)) :
    PhysicalProfileGenerator Agent Means Operation Service
      (List (PhysicalProfileInstruction Agent Means Operation)) where
  instruction := fun remaining _ =>
    (remaining.head?).getD idlePhysicalProfileInstruction
  nextCursor := fun remaining _ _ _ => remaining.drop 1

/-- Compile a finite fixed list through the general fuel-bounded generator.
Fuel equals the list length, so every listed instruction is consumed once. -/
def compilePhysicalProfileSchedule {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instructions : List (PhysicalProfileInstruction Agent Means Operation)) :=
  compilePhysicalProfileGenerator operations
    (fixedPhysicalProfileGenerator instructions) instructions.length instructions state

/-- The compiled schedule uses the supplied operation semantics at every
stage, so it supplies the stable-operation premise needed by the ActionFrame
adapter. -/
theorem compilePhysicalProfileSchedule_stable
    {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instructions : List (PhysicalProfileInstruction Agent Means Operation)) :
    (compilePhysicalProfileSchedule operations state instructions).HasStableOperationSemantics
      operations :=
  compilePhysicalProfileGenerator_stable operations
    (fixedPhysicalProfileGenerator instructions) instructions.length
    instructions state

/-- Execute the scheduled affordable profile at each stage. This selects one
history from the branching program and uses the same `advance` transitions. -/
def executePhysicalProfileSchedule {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instructions : List (PhysicalProfileInstruction Agent Means Operation)) :
    PhysicalState Agent Means Service :=
  executePhysicalProfileGenerator operations
    (fixedPhysicalProfileGenerator instructions) instructions.length instructions state

/-- The selected schedule is a history of the compiled branching program. -/
def physicalProfileScheduleHistory {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instructions : List (PhysicalProfileInstruction Agent Means Operation)) :=
  physicalProfileGeneratorHistory operations
    (fixedPhysicalProfileGenerator instructions) instructions.length instructions state

/-- The selected history's terminal stock is exactly the result of executing
the same scheduled profiles through their physical stages. -/
theorem physicalProfileScheduleHistory_terminalState
    {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (instructions : List (PhysicalProfileInstruction Agent Means Operation)) :
    (physicalProfileScheduleHistory operations state instructions).terminalState =
      executePhysicalProfileSchedule operations state instructions :=
  physicalProfileGeneratorHistory_terminalState operations
    (fixedPhysicalProfileGenerator instructions) instructions.length
    instructions state

end Praxeology
