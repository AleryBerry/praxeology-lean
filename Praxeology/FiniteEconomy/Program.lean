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

variable {State Agent Means Operation : Type}
variable [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
  [DecidableEq Operation]

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
