/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
-/
module

public import Praxeology.EconomicCalculation
public import Praxeology.FiniteEconomy.ActionFrameCompiler
public import Praxeology.Action

/-!
# Flat time-voucher effort incentives and bottleneck starvation

This module constructs a finite worker economy under flat clock-hour vouchers:

* `idle`: 0 certified hours, 0 effort consumed, 0 food redeemed, 2 effort left,
  0 intermediate produced.
* `easy`: 1 certified hour, 1 effort consumed, 1 food redeemed, 1 effort left,
  0 intermediate produced.
* `hard`: 1 certified hour, 2 effort consumed, 1 food redeemed, 0 effort left,
  1 intermediate produced.

Because `easy` and `hard` both certify 1 labor hour and redeem 1 unit from the
public food stock, `easy` preserves both food and rest and strictly dominates
`hard` and `idle` under ordinal `SubjectiveTeleologicalDominates`. Every
purposeful response on the complete menu selects `easy`, leaving zero units of
the bottleneck intermediate input and making downstream finishing infeasible.
A control reducing `hard` effort to 1 restores purposeful `hard` execution and
downstream feasibility.
-/

@[expose] public section

namespace Praxeology
namespace EconomicCalculation
namespace Incentives

/-- Physical goods in the flat time-voucher worker economy. -/
inductive WorkerGood where
  | food
  | effort
  | intermediate
  | final
  deriving DecidableEq, Inhabited, Repr

instance : Fintype WorkerGood where
  elems := {.food, .effort, .intermediate, .final}
  complete := by intro g; cases g <;> decide

/-- Productive tasks in the worker economy. -/
inductive WorkerTask where
  | easy
  | hard
  | downstream
  deriving DecidableEq, Inhabited, Repr

instance : Fintype WorkerTask where
  elems := {.easy, .hard, .downstream}
  complete := by intro t; cases t <;> decide

/-- Contemplated root choices for the worker. -/
inductive WorkerChoice where
  | idle
  | easy
  | hard
  deriving DecidableEq, Inhabited, Repr

/-- Physical task recipes on the public work ledger. -/
@[reducible] def workerLedgerOps : OperationSemantics WorkerTask WorkerGood Unit where
  input t g :=
    match t, g with
    | .easy, .effort => 1
    | .hard, .effort => 2
    | .downstream, .intermediate => 1
    | _, _ => 0
  output t g :=
    match t, g with
    | .hard, .intermediate => 1
    | .downstream, .final => 1
    | _, _ => 0
  service _ _ := 0

/-- Initial public and worker stock on the ledger: 1 public food unit, 2 effort
units, and 0 intermediate or final units. -/
@[reducible] def initialLedgerStock : WorkerGood → ℕ
  | .food => 1
  | .effort => 2
  | .intermediate => 0
  | .final => 0

@[reducible] def initialProduction : PublicProduction Unit WorkerGood WorkerTask where
  publicStock := initialLedgerStock
  capacity _ _ := 1
  input := workerLedgerOps.input
  output := workerLedgerOps.output
  laborHours _ := 1
  authorized _ _ := True

instance (p : Unit) (t : WorkerTask) (r : ℕ) :
    Decidable (initialProduction.CanExecute p t r) := by
  unfold PublicProduction.CanExecute
  dsimp [initialProduction, initialLedgerStock, workerLedgerOps]
  infer_instance

@[reducible] def initialWorkerLedger :
    CertificateState.WorkLedger (Person := Unit) (Good := WorkerGood) WorkerTask where
  production := initialProduction
  certificates :=
    { balance := fun _ => 0
      stock := initialLedgerStock
      consumed := fun _ _ => 0 }

def voucherPrice (_ : WorkerGood) : ℕ := 1

/-- Execute the worker's chosen task and issue personal time certificates. -/
def ledgerAfterWork : WorkerChoice →
    CertificateState.WorkLedger (Person := Unit) (Good := WorkerGood) WorkerTask
  | .idle => initialWorkerLedger
  | .easy => initialWorkerLedger.executeAndIssue () .easy 1 0
  | .hard => initialWorkerLedger.executeAndIssue () .hard 1 0

/-- Redeem earned time certificates for consumer food using atomic `WorkLedger.redeem`. -/
def ledgerAfterRedeem : WorkerChoice →
    CertificateState.WorkLedger (Person := Unit) (Good := WorkerGood) WorkerTask
  | .idle => initialWorkerLedger
  | .easy => (ledgerAfterWork .easy).redeem voucherPrice () .food 1
  | .hard => (ledgerAfterWork .hard).redeem voucherPrice () .food 1

theorem easy_and_hard_feasible_on_ledger :
    initialWorkerLedger.production.CanExecute () .easy 1 ∧
    initialWorkerLedger.production.CanExecute () .hard 1 := by
  constructor
  · refine ⟨trivial, by decide, ?_⟩
    intro g; cases g <;> decide
  · refine ⟨trivial, by decide, ?_⟩
    intro g; cases g <;> decide

theorem equal_voucher_issuance :
    (ledgerAfterWork .easy).certificates.balance () = 1 ∧
    (ledgerAfterWork .hard).certificates.balance () = 1 ∧
    (ledgerAfterWork .idle).certificates.balance () = 0 := by
  have heasy : initialWorkerLedger.production.CanExecute () .easy 1 :=
    easy_and_hard_feasible_on_ledger.1
  have hhard : initialWorkerLedger.production.CanExecute () .hard 1 :=
    easy_and_hard_feasible_on_ledger.2
  refine ⟨?_, ?_, rfl⟩
  · simp [ledgerAfterWork, CertificateState.WorkLedger.executeAndIssue, heasy,
      CertificateState.issue, initialWorkerLedger, initialProduction]
  · simp [ledgerAfterWork, CertificateState.WorkLedger.executeAndIssue, hhard,
      CertificateState.issue, initialWorkerLedger, initialProduction]

theorem ledger_after_work_stock_sync (c : WorkerChoice) :
    (ledgerAfterWork c).certificates.stock = (ledgerAfterWork c).production.publicStock := by
  cases c
  · rfl
  · exact CertificateState.WorkLedger.executeAndIssue_stock_sync
      initialWorkerLedger () .easy 1 0 rfl
  · exact CertificateState.WorkLedger.executeAndIssue_stock_sync
      initialWorkerLedger () .hard 1 0 rfl

theorem ledger_after_redeem_stock_sync (c : WorkerChoice) :
    (ledgerAfterRedeem c).certificates.stock =
      (ledgerAfterRedeem c).production.publicStock := by
  cases c
  · rfl
  · exact CertificateState.WorkLedger.redeem_stock_sync
      (ledgerAfterWork .easy) voucherPrice () .food 1 (ledger_after_work_stock_sync .easy)
  · exact CertificateState.WorkLedger.redeem_stock_sync
      (ledgerAfterWork .hard) voucherPrice () .food 1 (ledger_after_work_stock_sync .hard)

theorem equal_food_consumption :
    (ledgerAfterRedeem .easy).certificates.consumed () .food = 1 ∧
    (ledgerAfterRedeem .hard).certificates.consumed () .food = 1 ∧
    (ledgerAfterRedeem .idle).certificates.consumed () .food = 0 := by
  have heasy : initialWorkerLedger.production.CanExecute () .easy 1 :=
    easy_and_hard_feasible_on_ledger.1
  have hhard : initialWorkerLedger.production.CanExecute () .hard 1 :=
    easy_and_hard_feasible_on_ledger.2
  refine ⟨?_, ?_, rfl⟩
  · simp [ledgerAfterRedeem, CertificateState.WorkLedger.redeem,
      ledgerAfterWork, CertificateState.WorkLedger.executeAndIssue, heasy,
      CertificateState.redeem, CertificateState.issue, PublicProduction.execute,
      initialProduction, initialLedgerStock, voucherPrice]
  · simp [ledgerAfterRedeem, CertificateState.WorkLedger.redeem,
      ledgerAfterWork, CertificateState.WorkLedger.executeAndIssue, hhard,
      CertificateState.redeem, CertificateState.issue, PublicProduction.execute,
      initialProduction, initialLedgerStock, voucherPrice]

theorem ledger_residual_stocks :
    (ledgerAfterRedeem .idle).production.publicStock .effort = 2 ∧
    (ledgerAfterRedeem .idle).production.publicStock .intermediate = 0 ∧
    (ledgerAfterRedeem .easy).production.publicStock .effort = 1 ∧
    (ledgerAfterRedeem .easy).production.publicStock .intermediate = 0 ∧
    (ledgerAfterRedeem .hard).production.publicStock .effort = 0 ∧
    (ledgerAfterRedeem .hard).production.publicStock .intermediate = 1 := by
  have heasy : initialWorkerLedger.production.CanExecute () .easy 1 :=
    easy_and_hard_feasible_on_ledger.1
  have hhard : initialWorkerLedger.production.CanExecute () .hard 1 :=
    easy_and_hard_feasible_on_ledger.2
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [ledgerAfterRedeem, CertificateState.WorkLedger.redeem, ledgerAfterWork,
      CertificateState.WorkLedger.executeAndIssue, heasy, CertificateState.redeem,
      CertificateState.issue, PublicProduction.execute,
      initialProduction, initialLedgerStock, voucherPrice]
  · simp [ledgerAfterRedeem, CertificateState.WorkLedger.redeem, ledgerAfterWork,
      CertificateState.WorkLedger.executeAndIssue, heasy, CertificateState.redeem,
      CertificateState.issue, PublicProduction.execute,
      initialProduction, initialLedgerStock, voucherPrice]
  · simp [ledgerAfterRedeem, CertificateState.WorkLedger.redeem, ledgerAfterWork,
      CertificateState.WorkLedger.executeAndIssue, hhard, CertificateState.redeem,
      CertificateState.issue, PublicProduction.execute,
      initialProduction, initialLedgerStock, voucherPrice]
  · simp [ledgerAfterRedeem, CertificateState.WorkLedger.redeem, ledgerAfterWork,
      CertificateState.WorkLedger.executeAndIssue, hhard, CertificateState.redeem,
      CertificateState.issue, PublicProduction.execute,
      initialProduction, initialLedgerStock, voucherPrice]

/-- Physical stage operations matching the worker's effort outlay and redeemed
consumer food benefit under flat 1-hour voucher compensation. -/
def workerStageOps : OperationSemantics WorkerTask WorkerGood Unit where
  input := workerLedgerOps.input
  output t g :=
    match t, g with
    | .easy, .food => 1
    | .hard, .food => 1
    | .hard, .intermediate => 1
    | .downstream, .final => 1
    | _, _ => 0
  service _ _ := 0

def workerBeforeState : PhysicalState Unit WorkerGood Unit where
  stock _ g :=
    match g with
    | .effort => 2
    | _ => 0
  services _ _ := 0

def workerChoiceStage : FiniteChoiceStage Unit WorkerGood WorkerTask where
  menu _ := {.idle, .operate .easy, .operate .hard}
  idle_mem _ := by simp
  activeAgents := {()}
  active_iff i := by
    cases i
    simp
  maxActiveAgents := 1
  activity_bound := by simp
  menu_wellFormed i a ha := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [EconomyAction.WellFormed]

def workerPhysicalStage : FinitePhysicalChoiceStage Unit WorkerGood WorkerTask Unit where
  choices := workerChoiceStage
  operations := workerStageOps
  before := workerBeforeState
  menu_affordable i a ha m := by
    cases i
    simp only [workerChoiceStage, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp [rawActionUse]
    · cases m <;> decide
    · cases m <;> decide

def choiceAction : WorkerChoice → EconomyAction Unit WorkerGood WorkerTask
  | .idle => .idle
  | .easy => .operate .easy
  | .hard => .operate .hard

def choiceProfile (c : WorkerChoice) : workerChoiceStage.Profile :=
  ⟨fun _ => choiceAction c, fun _ => by
    cases c <;> simp [choiceAction, workerChoiceStage]⟩

/-- The physical stage transition reproduces the exact food consumption,
remaining effort, and intermediate stock of the work-and-redemption ledger. -/
theorem stage_matches_workerLedger (c : WorkerChoice) :
    (workerPhysicalStage.advance (choiceProfile c)).stock () .food =
      (ledgerAfterRedeem c).certificates.consumed () .food ∧
    (workerPhysicalStage.advance (choiceProfile c)).stock () .effort =
      (ledgerAfterRedeem c).production.publicStock .effort ∧
    (workerPhysicalStage.advance (choiceProfile c)).stock () .intermediate =
      (ledgerAfterRedeem c).production.publicStock .intermediate := by
  have hfood_bal := workerPhysicalStage.advance_balance (choiceProfile c) () .food
  have heff_bal := workerPhysicalStage.advance_balance (choiceProfile c) () .effort
  have hint_bal := workerPhysicalStage.advance_balance (choiceProfile c) () .intermediate
  change _ + effectiveUse workerStageOps (choiceProfile c).1 () .food =
      workerBeforeState.stock () .food + effectiveYield workerStageOps (choiceProfile c).1 () .food
    at hfood_bal
  change _ + effectiveUse workerStageOps (choiceProfile c).1 () .effort =
      workerBeforeState.stock () .effort +
        effectiveYield workerStageOps (choiceProfile c).1 () .effort
    at heff_bal
  change _ + effectiveUse workerStageOps (choiceProfile c).1 () .intermediate =
      workerBeforeState.stock () .intermediate +
        effectiveYield workerStageOps (choiceProfile c).1 () .intermediate
    at hint_bal
  rcases equal_food_consumption with ⟨hfe, hfh, hfi⟩
  rcases ledger_residual_stocks with ⟨hei, hii, hee, hie, heh, hih⟩
  have hval : (choiceProfile c).1 () = choiceAction c := rfl
  rw [effectiveUse, effectiveYield, hval] at hfood_bal heff_bal hint_bal
  cases c <;>
    simp [choiceAction, workerStageOps, workerBeforeState]
      at hfood_bal heff_bal hint_bal <;>
    omega

/-- Valued ends for the worker: obtaining 1 unit of food and retaining 1 unit
of effort (rest). -/
def foodEnd : workerPhysicalStage.End := .quantity .food 1
def restEnd : workerPhysicalStage.End := .quantity .effort 1

def workerValuedEnd (e : workerPhysicalStage.End) : Prop :=
  e = foodEnd ∨ e = restEnd

def choiceEndBundle : workerPhysicalStage.End → (WorkerGood → ℕ)
  | .bundle b => b
  | .timed e _ => choiceEndBundle e
  | .quantity m q => fun m' => if m' = m then q else 0

theorem easy_attains_food_and_rest :
    JointlyAttains finitePhysicalChoiceRequirement
      ((workerPhysicalStage.advance (choiceProfile .easy)).stock ()) {foodEnd, restEnd} := by
  intro m
  have hmatch := stage_matches_workerLedger .easy
  rcases equal_food_consumption with ⟨hfe, _, _⟩
  rcases ledger_residual_stocks with ⟨_, _, hee, _, _, _⟩
  have hfood : (workerPhysicalStage.advance (choiceProfile .easy)).stock () .food = 1 := by
    omega
  have heff : (workerPhysicalStage.advance (choiceProfile .easy)).stock () .effort = 1 := by
    omega
  have hne : foodEnd ≠ restEnd := by
    intro h; cases h
  rw [Finset.sum_pair hne]
  cases m <;> simp [foodEnd, restEnd, finitePhysicalChoiceRequirement, hfood, heff]

theorem hard_misses_rest_and_idle_misses_food :
    ¬ AttainsEnd finitePhysicalChoiceRequirement
        ((workerPhysicalStage.advance (choiceProfile .hard)).stock ()) restEnd ∧
    ¬ AttainsEnd finitePhysicalChoiceRequirement
        ((workerPhysicalStage.advance (choiceProfile .idle)).stock ()) foodEnd := by
  have hmhard := stage_matches_workerLedger .hard
  have hmidle := stage_matches_workerLedger .idle
  rcases equal_food_consumption with ⟨_, _, hfi⟩
  rcases ledger_residual_stocks with ⟨_, _, _, _, heh, _⟩
  constructor
  · intro h
    have he := h .effort
    simp [restEnd, finitePhysicalChoiceRequirement] at he
    omega
  · intro h
    have hf := h .food
    simp [foodEnd, finitePhysicalChoiceRequirement] at hf
    omega

theorem easy_teleological_dominates_hard :
    SubjectiveTeleologicalDominates finitePhysicalChoiceRequirement workerValuedEnd
      ((workerPhysicalStage.advance (choiceProfile .easy)).stock ())
      ((workerPhysicalStage.advance (choiceProfile .hard)).stock ()) := by
  refine ⟨?_, ⟨{foodEnd, restEnd}, ?_, easy_attains_food_and_rest, ?_⟩⟩
  · intro S hval hatt m
    have hmatch_easy := stage_matches_workerLedger .easy
    have hmatch_hard := stage_matches_workerLedger .hard
    rcases equal_food_consumption with ⟨hfe, hfh, _⟩
    rcases ledger_residual_stocks with ⟨_, _, hee, _, heh, _⟩
    have hnot_rest : restEnd ∉ S := by
      intro hmem
      have hle := Finset.single_le_sum (f := fun e => finitePhysicalChoiceRequirement e .effort)
        (fun _ _ => Nat.zero_le _) hmem
      have hb := hatt .effort
      simp [restEnd, finitePhysicalChoiceRequirement] at hle
      omega
    have hsub : S ⊆ {foodEnd} := by
      intro e he
      rcases hval e he with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact (hnot_rest he).elim
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
    · simp
    · cases m <;>
        simp [foodEnd, finitePhysicalChoiceRequirement, hmatch_easy.1, hfe]
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hatt
    apply hard_misses_rest_and_idle_misses_food.1
    intro m
    have hle := Finset.single_le_sum (s := ({foodEnd, restEnd} : Finset _))
      (f := fun e => finitePhysicalChoiceRequirement e m)
      (fun _ _ => Nat.zero_le _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self restEnd))
    exact le_trans hle (hatt m)

theorem easy_teleological_dominates_idle :
    SubjectiveTeleologicalDominates finitePhysicalChoiceRequirement workerValuedEnd
      ((workerPhysicalStage.advance (choiceProfile .easy)).stock ())
      ((workerPhysicalStage.advance (choiceProfile .idle)).stock ()) := by
  refine ⟨?_, ⟨{foodEnd, restEnd}, ?_, easy_attains_food_and_rest, ?_⟩⟩
  · intro S hval hatt m
    have hmatch_easy := stage_matches_workerLedger .easy
    have hmatch_idle := stage_matches_workerLedger .idle
    rcases equal_food_consumption with ⟨hfe, _, hfi⟩
    rcases ledger_residual_stocks with ⟨hei, _, hee, _, _, _⟩
    have hnot_food : foodEnd ∉ S := by
      intro hmem
      have hle := Finset.single_le_sum (f := fun e => finitePhysicalChoiceRequirement e .food)
        (fun _ _ => Nat.zero_le _) hmem
      have hb := hatt .food
      simp [foodEnd, finitePhysicalChoiceRequirement] at hle
      omega
    have hsub : S ⊆ {restEnd} := by
      intro e he
      rcases hval e he with rfl | rfl
      · exact (hnot_food he).elim
      · exact Finset.mem_singleton_self _
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
    · simp
    · cases m <;>
        simp [restEnd, finitePhysicalChoiceRequirement, hmatch_easy.2.1, hee]
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hatt
    apply hard_misses_rest_and_idle_misses_food.2
    intro m
    have hle := Finset.single_le_sum (f := fun e => finitePhysicalChoiceRequirement e m)
      (fun _ _ => Nat.zero_le _) (Finset.mem_insert_self foodEnd {restEnd})
    exact le_trans hle (hatt m)

/-- Appraisal-based behavior selecting `choiceProfile .easy` as the root
reference history, with ordinal preferences derived directly from
`SubjectiveTeleologicalDominates`. -/
noncomputable def workerBehavior : FinitePhysicalChoiceBehavior workerPhysicalStage where
  referenceHistory _ := choiceProfile .easy
  valuedEnd _ _ _ e := workerValuedEnd e
  valuedEnd_invariant _ _ _ _ _ _ _ := Iff.rfl
  preference _ _ _ e₁ e₂ :=
    SubjectiveTeleologicalDominates finitePhysicalChoiceRequirement workerValuedEnd
      (choiceEndBundle e₁) (choiceEndBundle e₂)
  preference_invariant _ _ _ _ _ _ := rfl
  preference_asymmetric _ _ _ _ _ h₁ h₂ := by
    rcases h₁ with ⟨_, ⟨S, hval, hatt₁, hnatt₂⟩⟩
    exact hnatt₂ (h₂.1 S hval hatt₁)
  teleological_dominance_prefers _ _ _ b₁ b₂ h := h

@[instance_reducible] noncomputable def workerFrame : ActionFrame :=
  workerPhysicalStage.toActionFrame workerBehavior

theorem worker_selectAt_root (c : WorkerChoice) :
    workerPhysicalStage.selectAt () none (choiceAction c) (choiceProfile .easy) =
      choiceProfile c := by
  have hmem : choiceAction c ∈ workerPhysicalStage.choices.menu () := by
    cases c <;> simp [choiceAction, workerPhysicalStage, workerChoiceStage]
  simp only [FinitePhysicalChoiceStage.selectAt, hmem, ↓reduceDIte]
  apply Subtype.ext
  funext i
  cases i
  simp [FiniteChoiceStage.replaceProfile, choiceAction, choiceProfile]

theorem worker_intendedEnd_eq (c : WorkerChoice) :
    workerFrame.End_of () (choiceAction c) none (choiceProfile .easy) =
      .bundle ((workerPhysicalStage.advance (choiceProfile c)).stock ()) := by
  change workerPhysicalStage.intendedEnd workerBehavior () none (choiceAction c) = _
  simp [FinitePhysicalChoiceStage.intendedEnd, FinitePhysicalChoiceStage.referenceAt,
    workerBehavior, worker_selectAt_root, FinitePhysicalChoiceStage.maturationAt,
    FinitePhysicalChoiceStage.outcomeAt, FinitePhysicalChoiceStage.stateAt]

theorem worker_prefers_easy_over_hard (h : workerFrame.History) :
    workerFrame.Preference () none h
      (workerFrame.End_of () (.operate .easy) none h)
      (workerFrame.End_of () (.operate .hard) none h) := by
  have hinv := workerFrame.Preference_bundle_invariant () none
    (h1 := h) (h2 := choiceProfile .easy) trivial trivial
  have he1 := workerFrame.End_of_bundle_invariant () (.operate .easy) none
    (h1 := h) (h2 := choiceProfile .easy) trivial trivial
  have he2 := workerFrame.End_of_bundle_invariant () (.operate .hard) none
    (h1 := h) (h2 := choiceProfile .easy) trivial trivial
  rw [hinv, he1, he2]
  have he_easy : workerFrame.End_of () (.operate .easy) none (choiceProfile .easy) =
      .bundle ((workerPhysicalStage.advance (choiceProfile .easy)).stock ()) :=
    worker_intendedEnd_eq .easy
  have he_hard : workerFrame.End_of () (.operate .hard) none (choiceProfile .easy) =
      .bundle ((workerPhysicalStage.advance (choiceProfile .hard)).stock ()) :=
    worker_intendedEnd_eq .hard
  rw [he_easy, he_hard]
  exact easy_teleological_dominates_hard

theorem worker_prefers_easy_over_idle (h : workerFrame.History) :
    workerFrame.Preference () none h
      (workerFrame.End_of () (.operate .easy) none h)
      (workerFrame.End_of () .idle none h) := by
  have hinv := workerFrame.Preference_bundle_invariant () none
    (h1 := h) (h2 := choiceProfile .easy) trivial trivial
  have he1 := workerFrame.End_of_bundle_invariant () (.operate .easy) none
    (h1 := h) (h2 := choiceProfile .easy) trivial trivial
  have he2 := workerFrame.End_of_bundle_invariant () .idle none
    (h1 := h) (h2 := choiceProfile .easy) trivial trivial
  rw [hinv, he1, he2]
  have he_easy : workerFrame.End_of () (.operate .easy) none (choiceProfile .easy) =
      .bundle ((workerPhysicalStage.advance (choiceProfile .easy)).stock ()) :=
    worker_intendedEnd_eq .easy
  have he_idle : workerFrame.End_of () .idle none (choiceProfile .easy) =
      .bundle ((workerPhysicalStage.advance (choiceProfile .idle)).stock ()) :=
    worker_intendedEnd_eq .idle
  rw [he_easy, he_idle]
  exact easy_teleological_dominates_idle

/-- An actual purposeful execution of `easy` exists on the worker ActionFrame. -/
theorem worker_easy_purposeful :
    @PurposefulAct workerFrame () none (choiceProfile .easy) (.operate .easy) := by
  have hfeas : EconomyAction.operate .easy ∈ workerFrame.A_feas () none (choiceProfile .easy) := by
    apply (workerFrame.A_feas_coupling () none (choiceProfile .easy) (.operate .easy)).2
    refine ⟨?_, ?_⟩
    · change EconomyAction.operate .easy ∈ workerChoiceStage.menu ()
      simp [workerChoiceStage]
    · intro m
      change rawActionUse workerStageOps (.operate .easy) m ≤ workerBeforeState.stock () m
      cases m <;> decide
  have hexec : @Exec workerFrame () none (.operate .easy) (choiceProfile .easy) :=
    ⟨trivial, rfl⟩
  have hgain : workerFrame.Preference () none (choiceProfile .easy)
      (workerFrame.End_of () (.operate .easy) none (choiceProfile .easy))
      (workerFrame.End_of () workerFrame.alpha_zero none (choiceProfile .easy)) :=
    worker_prefers_easy_over_idle (choiceProfile .easy)
  refine ⟨hfeas, hexec, Or.inr hgain, ?_⟩
  intro β hβ hpref
  have hmem : β ∈ workerChoiceStage.menu () :=
    (workerFrame.A_feas_coupling () none (choiceProfile .easy) β).1 hβ |>.1
  simp only [workerChoiceStage, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact workerFrame.pref_asymm () none (choiceProfile .easy)
      (worker_prefers_easy_over_idle (choiceProfile .easy)) hpref
  · exact workerFrame.pref_asymm () none (choiceProfile .easy) hpref hpref
  · exact workerFrame.pref_asymm () none (choiceProfile .easy)
      (worker_prefers_easy_over_hard (choiceProfile .easy)) hpref

/-- Every purposeful response on the complete worker menu selects `easy`. -/
theorem worker_every_purposeful_selects_easy (h : workerFrame.History)
    (hpurp : @PurposefulAct workerFrame () none h (workerFrame.enacted () none h)) :
    workerFrame.enacted () none h = .operate .easy := by
  have heasy_feas : EconomyAction.operate .easy ∈ workerFrame.A_feas () none h := by
    apply (workerFrame.A_feas_coupling () none h (.operate .easy)).2
    refine ⟨?_, ?_⟩
    · change EconomyAction.operate .easy ∈ workerChoiceStage.menu ()
      simp [workerChoiceStage]
    · intro m
      change rawActionUse workerStageOps (.operate .easy) m ≤ workerBeforeState.stock () m
      cases m <;> decide
  exact (@enacted_eq_of_strictly_best workerFrame () none h (.operate .easy) hpurp heasy_feas
    (fun β hβ hne => by
      have hmem : β ∈ workerChoiceStage.menu () :=
        (workerFrame.A_feas_coupling () none h β).1 hβ |>.1
      simp only [workerChoiceStage, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact worker_prefers_easy_over_idle h
      · exact (hne rfl).elim
      · exact worker_prefers_easy_over_hard h)).1

theorem worker_hard_and_idle_not_purposeful (h : workerFrame.History) :
    ¬ @PurposefulAct workerFrame () none h (.operate .hard) ∧
    ¬ @PurposefulAct workerFrame () none h .idle := by
  have heasy_feas : EconomyAction.operate .easy ∈ workerFrame.A_feas () none h := by
    apply (workerFrame.A_feas_coupling () none h (.operate .easy)).2
    refine ⟨?_, ?_⟩
    · change EconomyAction.operate .easy ∈ workerChoiceStage.menu ()
      simp [workerChoiceStage]
    · intro m
      change rawActionUse workerStageOps (.operate .easy) m ≤ workerBeforeState.stock () m
      cases m <;> decide
  constructor
  · intro hp
    exact hp.2.2.2 (.operate .easy) heasy_feas (worker_prefers_easy_over_hard h)
  · intro hp
    exact hp.2.2.2 (.operate .easy) heasy_feas (worker_prefers_easy_over_idle h)

/-- Purposeful easy work leaves zero intermediate stock and renders the
downstream bottleneck task infeasible on both the ledger and physical stage. -/
theorem purposeful_easy_starves_downstream :
    (ledgerAfterRedeem .easy).production.publicStock .intermediate = 0 ∧
    (workerPhysicalStage.advance (choiceProfile .easy)).stock () .intermediate = 0 ∧
    ¬ (ledgerAfterRedeem .easy).production.CanExecute () .downstream 1 ∧
    ¬ actionAffordable workerStageOps (workerPhysicalStage.advance (choiceProfile .easy))
        () (.operate .downstream) := by
  have hmatch := stage_matches_workerLedger .easy
  rcases ledger_residual_stocks with ⟨_, _, _, hie, _, _⟩
  refine ⟨hie, by omega, ?_, ?_⟩
  · intro hcan
    have hle := hcan.2.2 .intermediate
    have hin : (ledgerAfterRedeem .easy).production.input .downstream .intermediate = 1 := by
      simp [ledgerAfterRedeem, CertificateState.WorkLedger.redeem, ledgerAfterWork,
        CertificateState.WorkLedger.executeAndIssue, easy_and_hard_feasible_on_ledger.1,
        initialProduction, workerLedgerOps]
    simp [hin, hie] at hle
  · intro haff
    have hle := haff .intermediate
    have hzero :
        (workerPhysicalStage.advance (choiceProfile .easy)).stock () .intermediate = 0 := by
      omega
    simp [rawActionUse, workerStageOps, hzero] at hle

/-! ## Equal-effort control

Reducing the hard task's effort cost from 2 to 1 restores equal effort with
`easy`, permitting purposeful `hard` execution and making the downstream
bottleneck operation physically feasible. -/

@[reducible] def equalEffortLedgerOps : OperationSemantics WorkerTask WorkerGood Unit where
  input t g :=
    match t, g with
    | .easy, .effort => 1
    | .hard, .effort => 1
    | .downstream, .intermediate => 1
    | _, _ => 0
  output := workerLedgerOps.output
  service _ _ := 0

@[reducible] def equalEffortStageOps : OperationSemantics WorkerTask WorkerGood Unit where
  input := equalEffortLedgerOps.input
  output := workerStageOps.output
  service _ _ := 0

@[reducible] def equalEffortProduction : PublicProduction Unit WorkerGood WorkerTask :=
  { initialProduction with input := equalEffortLedgerOps.input }

instance (p : Unit) (t : WorkerTask) (r : ℕ) :
    Decidable (equalEffortProduction.CanExecute p t r) := by
  unfold PublicProduction.CanExecute
  dsimp [equalEffortProduction, initialProduction, initialLedgerStock,
    equalEffortLedgerOps, workerLedgerOps]
  infer_instance

@[reducible] def equalEffortInitialLedger :
    CertificateState.WorkLedger (Person := Unit) (Good := WorkerGood) WorkerTask :=
  { initialWorkerLedger with production := equalEffortProduction }

def equalEffortLedgerAfterHard :
    CertificateState.WorkLedger (Person := Unit) (Good := WorkerGood) WorkerTask :=
  (equalEffortInitialLedger.executeAndIssue () .hard 1 0).redeem voucherPrice () .food 1

def equalEffortPhysicalStage : FinitePhysicalChoiceStage Unit WorkerGood WorkerTask Unit where
  choices := workerChoiceStage
  operations := equalEffortStageOps
  before := workerBeforeState
  menu_affordable i a ha m := by
    cases i
    simp only [workerChoiceStage, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp [rawActionUse]
    · cases m <;> decide
    · cases m <;> decide

def equalHardProfile : equalEffortPhysicalStage.choices.Profile := choiceProfile .hard

theorem equal_effort_hard_stock :
    (equalEffortPhysicalStage.advance equalHardProfile).stock () .food = 1 ∧
    (equalEffortPhysicalStage.advance equalHardProfile).stock () .effort = 1 ∧
    (equalEffortPhysicalStage.advance equalHardProfile).stock () .intermediate = 1 := by
  have hf := equalEffortPhysicalStage.advance_balance equalHardProfile () .food
  have he := equalEffortPhysicalStage.advance_balance equalHardProfile () .effort
  have hi := equalEffortPhysicalStage.advance_balance equalHardProfile () .intermediate
  change _ + effectiveUse equalEffortStageOps equalHardProfile.1 () .food =
      workerBeforeState.stock () .food +
        effectiveYield equalEffortStageOps equalHardProfile.1 () .food
    at hf
  change _ + effectiveUse equalEffortStageOps equalHardProfile.1 () .effort =
      workerBeforeState.stock () .effort +
        effectiveYield equalEffortStageOps equalHardProfile.1 () .effort
    at he
  change _ + effectiveUse equalEffortStageOps equalHardProfile.1 () .intermediate =
      workerBeforeState.stock () .intermediate +
        effectiveYield equalEffortStageOps equalHardProfile.1 () .intermediate
    at hi
  have hp : equalHardProfile.1 () = .operate .hard := rfl
  rw [effectiveUse, effectiveYield, hp] at hf he hi
  simp [workerStageOps, workerBeforeState] at hf he hi
  omega

theorem equal_effort_hard_attains_both :
    JointlyAttains finitePhysicalChoiceRequirement
      ((equalEffortPhysicalStage.advance equalHardProfile).stock ()) {foodEnd, restEnd} := by
  intro m
  rcases equal_effort_hard_stock with ⟨hf, he, _⟩
  have hne : foodEnd ≠ restEnd := by
    intro h; cases h
  rw [Finset.sum_pair hne]
  cases m <;> simp [foodEnd, restEnd, finitePhysicalChoiceRequirement, hf, he]

noncomputable def equalEffortBehavior :
    FinitePhysicalChoiceBehavior equalEffortPhysicalStage where
  referenceHistory _ := equalHardProfile
  valuedEnd _ _ _ e := workerValuedEnd e
  valuedEnd_invariant _ _ _ _ _ _ _ := Iff.rfl
  preference _ _ _ e₁ e₂ :=
    SubjectiveTeleologicalDominates finitePhysicalChoiceRequirement workerValuedEnd
      (choiceEndBundle e₁) (choiceEndBundle e₂)
  preference_invariant _ _ _ _ _ _ := rfl
  preference_asymmetric _ _ _ _ _ h₁ h₂ := by
    rcases h₁ with ⟨_, ⟨S, hval, hatt₁, hnatt₂⟩⟩
    exact hnatt₂ (h₂.1 S hval hatt₁)
  teleological_dominance_prefers _ _ _ b₁ b₂ h := h

@[instance_reducible] noncomputable def equalEffortFrame : ActionFrame :=
  equalEffortPhysicalStage.toActionFrame equalEffortBehavior

theorem equal_effort_selectAt_root (c : WorkerChoice) :
    equalEffortPhysicalStage.selectAt () none (choiceAction c) equalHardProfile =
      choiceProfile c := by
  have hmem : choiceAction c ∈ equalEffortPhysicalStage.choices.menu () := by
    cases c <;> simp [choiceAction, equalEffortPhysicalStage, workerChoiceStage]
  simp only [FinitePhysicalChoiceStage.selectAt, hmem, ↓reduceDIte]
  apply Subtype.ext
  funext i
  cases i
  simp [FiniteChoiceStage.replaceProfile, choiceAction, choiceProfile]

theorem equal_effort_intendedEnd_eq (c : WorkerChoice) :
    equalEffortFrame.End_of () (choiceAction c) none equalHardProfile =
      .bundle ((equalEffortPhysicalStage.advance (choiceProfile c)).stock ()) := by
  change equalEffortPhysicalStage.intendedEnd equalEffortBehavior () none (choiceAction c) = _
  simp [FinitePhysicalChoiceStage.intendedEnd, FinitePhysicalChoiceStage.referenceAt,
    equalEffortBehavior, equal_effort_selectAt_root, FinitePhysicalChoiceStage.maturationAt,
    FinitePhysicalChoiceStage.outcomeAt, FinitePhysicalChoiceStage.stateAt]

theorem equal_effort_hard_purposeful_and_downstream_feasible :
    @PurposefulAct equalEffortFrame () none equalHardProfile (.operate .hard) ∧
    equalEffortLedgerAfterHard.production.CanExecute () .downstream 1 ∧
    actionAffordable equalEffortStageOps
      (equalEffortPhysicalStage.advance equalHardProfile) () (.operate .downstream) := by
  have hhard_stock := equal_effort_hard_stock
  have hidle_food :
      (equalEffortPhysicalStage.advance (choiceProfile .idle)).stock () .food = 0 := by
    have hf := equalEffortPhysicalStage.advance_balance (choiceProfile .idle) () .food
    simpa [choiceProfile, choiceAction, effectiveUse, effectiveYield,
      equalEffortPhysicalStage, workerBeforeState] using hf
  have hdom_idle :
      SubjectiveTeleologicalDominates finitePhysicalChoiceRequirement workerValuedEnd
        ((equalEffortPhysicalStage.advance equalHardProfile).stock ())
        ((equalEffortPhysicalStage.advance (choiceProfile .idle)).stock ()) := by
    refine ⟨?_, ⟨{foodEnd, restEnd}, ?_, equal_effort_hard_attains_both, ?_⟩⟩
    · intro S hval hatt m
      have hnot_food : foodEnd ∉ S := by
        intro hmem
        have hle := Finset.single_le_sum (f := fun e => finitePhysicalChoiceRequirement e .food)
          (fun _ _ => Nat.zero_le _) hmem
        have hb := hatt .food
        simp [foodEnd, finitePhysicalChoiceRequirement] at hle
        omega
      have hsub : S ⊆ {restEnd} := by
        intro e he
        rcases hval e he with rfl | rfl
        · exact (hnot_food he).elim
        · exact Finset.mem_singleton_self _
      rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
      · simp
      · cases m <;>
          simp [restEnd, finitePhysicalChoiceRequirement, hhard_stock.2.1]
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hatt
      have hle := Finset.single_le_sum (f := fun e => finitePhysicalChoiceRequirement e .food)
        (fun _ _ => Nat.zero_le _) (Finset.mem_insert_self foodEnd {restEnd})
      have hb := hatt .food
      simp [foodEnd, finitePhysicalChoiceRequirement, hidle_food] at hle hb
  have hfeas : EconomyAction.operate .hard ∈ equalEffortFrame.A_feas () none equalHardProfile := by
    apply (equalEffortFrame.A_feas_coupling () none equalHardProfile (.operate .hard)).2
    refine ⟨?_, ?_⟩
    · change EconomyAction.operate .hard ∈ workerChoiceStage.menu ()
      simp [workerChoiceStage]
    · intro m
      change rawActionUse equalEffortStageOps (.operate .hard) m ≤ workerBeforeState.stock () m
      cases m <;> decide
  have hexec : @Exec equalEffortFrame () none (.operate .hard) equalHardProfile :=
    ⟨trivial, rfl⟩
  have hgain : equalEffortFrame.Preference () none equalHardProfile
      (equalEffortFrame.End_of () (.operate .hard) none equalHardProfile)
      (equalEffortFrame.End_of () equalEffortFrame.alpha_zero none equalHardProfile) := by
    have he_hard :
        equalEffortFrame.End_of () (.operate .hard) none equalHardProfile =
          .bundle ((equalEffortPhysicalStage.advance (choiceProfile .hard)).stock ()) :=
      equal_effort_intendedEnd_eq .hard
    have he_idle :
        equalEffortFrame.End_of () equalEffortFrame.alpha_zero none equalHardProfile =
          .bundle ((equalEffortPhysicalStage.advance (choiceProfile .idle)).stock ()) :=
      equal_effort_intendedEnd_eq .idle
    rw [he_hard, he_idle]
    exact hdom_idle
  have hundom : ∀ β ∈ equalEffortFrame.A_feas () none equalHardProfile,
      ¬ equalEffortFrame.Preference () none equalHardProfile
          (equalEffortFrame.End_of () β none equalHardProfile)
          (equalEffortFrame.End_of () (.operate .hard) none equalHardProfile) := by
    intro β hβ hpref
    have hmem : β ∈ workerChoiceStage.menu () :=
      (equalEffortFrame.A_feas_coupling () none equalHardProfile β).1 hβ |>.1
    simp only [workerChoiceStage, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact equalEffortFrame.pref_asymm () none equalHardProfile hgain hpref
    · have he_easy :
          equalEffortFrame.End_of () (.operate .easy) none equalHardProfile =
            .bundle ((equalEffortPhysicalStage.advance (choiceProfile .easy)).stock ()) :=
        equal_effort_intendedEnd_eq .easy
      have he_hard :
          equalEffortFrame.End_of () (.operate .hard) none equalHardProfile =
            .bundle ((equalEffortPhysicalStage.advance (choiceProfile .hard)).stock ()) :=
        equal_effort_intendedEnd_eq .hard
      rw [he_easy, he_hard] at hpref
      rcases hpref with ⟨_, ⟨S, hval, _, hnatt⟩⟩
      apply hnatt
      intro m
      have hsub : S ⊆ {foodEnd, restEnd} := by
        intro e he
        rcases hval e he with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hsum_le : S.sum (fun e => finitePhysicalChoiceRequirement e m) ≤
          ({foodEnd, restEnd} : Finset _).sum (fun e => finitePhysicalChoiceRequirement e m) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      exact le_trans hsum_le (equal_effort_hard_attains_both m)
    · exact equalEffortFrame.pref_asymm () none equalHardProfile hpref hpref
  refine ⟨⟨hfeas, hexec, Or.inr hgain, hundom⟩, ?_, ?_⟩
  · have hhard_can : equalEffortInitialLedger.production.CanExecute () .hard 1 := by
      refine ⟨trivial, by decide, ?_⟩
      intro g; cases g <;> decide
    refine ⟨trivial, ?_, ?_⟩
    · simp [equalEffortLedgerAfterHard, CertificateState.WorkLedger.redeem,
        CertificateState.WorkLedger.executeAndIssue, hhard_can,
        equalEffortInitialLedger, initialWorkerLedger, equalEffortProduction, initialProduction]
    · intro g
      cases g <;>
        simp [equalEffortLedgerAfterHard, CertificateState.WorkLedger.redeem,
          CertificateState.WorkLedger.executeAndIssue, hhard_can, CertificateState.redeem,
          CertificateState.issue, PublicProduction.execute,
          equalEffortProduction, initialLedgerStock, voucherPrice]
  · intro m
    cases m <;> simp [rawActionUse, hhard_stock.2.2]

end Incentives
end EconomicCalculation
end Praxeology

end
