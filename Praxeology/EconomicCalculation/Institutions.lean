/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
-/
module

public import Praxeology.EconomicCalculation
public import Praxeology.FiniteEconomy.ProgramActionFrame
public import Praxeology.FiniteEconomy.ActionFrameCompiler
public import Praxeology.Catallactics
public import Praxeology.FirmBoundary

/-!
# Institutional Economic Calculation Witnesses and Controls

This module implements one shared finite physical economy (`K1 = 2`, `K2 = 2`,
one consumable `setup` unit, and shared post-prefix labor capacity `2`) and
derives:

1. Two closed negative instances of `InformationProblem`:
   * `voucher_accounting_cannot_always_economize` for a labor-voucher accounting
     interface using `WorkLedger.executeAndIssue` and atomic `WorkLedger.redeem`,
     where embodied + direct labor charges equal `4` for both target techniques.
   * `io_accounting_cannot_always_economize` for an input-output and
     administered-price interface with separate input and output matrices.
2. An `ActionFrame` instantiation over the two-stage `FinitePhysicalEconomyProgram`
   with terminal outcome evaluation and purposeful downstream execution on each
   successful branch, plus a ground witness for
   `action_frame_socialist_calculation_impossibility`.
3. Multi-round transcript induction, a pre-commitment zero-queue
   `AdministeredPriceState` invariance witness, and an explicit
   `InIndeterminacyCone` witness.
4. Successful calculation controls (physical dominance, reverse dominance and
   ties, single-factor linearity, successful shared-appraisal antichain,
   distinguishing-report restoration, full information) and the exact
   necessary-and-sufficient `PhysicalAntichain` conflict equivalence over the
   two-factor bottleneck family.

Scope: the impossibility results characterize the explicitly restricted
pre-commitment accounting and queue records, in which downstream ordinal
appraisals are not reported until after technique commitment.
-/

@[expose] public section

open scoped BigOperators

namespace Praxeology
namespace EconomicCalculation
namespace Institutions

/-! ## 1. Shared Physical Economy -/

/-- Physical goods in the shared two-factor economy. -/
inductive CalcGood where
  | K1
  | K2
  | setup
  | Q
  | C1
  | C2
  | preGood
  deriving DecidableEq, Inhabited, Repr

instance : Fintype CalcGood where
  elems := {.K1, .K2, .setup, .Q, .C1, .C2, .preGood}
  complete := by intro g; cases g <;> decide

/-- Target techniques producing good `Q`. -/
inductive Method where
  | A
  | B
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Method where
  elems := {.A, .B}
  complete := by intro m; cases m <;> decide

/-- Downstream actions executed after the target technique. -/
inductive DownstreamAct where
  | idle
  | D1
  | D2
  deriving DecidableEq, Inhabited, Repr

instance : Fintype DownstreamAct where
  elems := {.idle, .D1, .D2}
  complete := by intro d; cases d <;> decide

/-- Productive operations in the shared economy. -/
inductive CalcTask where
  | prefixTask
  | techA
  | techB
  | down1
  | down2
  deriving DecidableEq, Inhabited, Repr

instance : Fintype CalcTask where
  elems := {.prefixTask, .techA, .techB, .down1, .down2}
  complete := by intro t; cases t <;> decide

@[reducible] def methodToTask : Method → CalcTask
  | .A => .techA
  | .B => .techB

/-- Physical inputs, outputs, and zero service yields for all tasks. -/
@[reducible] def sharedOps : OperationSemantics CalcTask CalcGood Unit where
  input t g :=
    match t, g with
    | .techA, .K1 => 2
    | .techA, .K2 => 1
    | .techA, .setup => 1
    | .techB, .K1 => 1
    | .techB, .K2 => 2
    | .techB, .setup => 1
    | .down1, .K1 => 1
    | .down2, .K2 => 1
    | _, _ => 0
  output t g :=
    match t, g with
    | .prefixTask, .preGood => 1
    | .techA, .Q => 1
    | .techB, .Q => 1
    | .down1, .C1 => 1
    | .down2, .C2 => 1
    | _, _ => 0
  service _ _ := 0

/-- Initial endowments before the common pre-commitment prefix. -/
@[reducible] def initialCalcStock : CalcGood → ℕ
  | .K1 => 2
  | .K2 => 2
  | .setup => 1
  | _ => 0

@[reducible] def initialCalcProduction : PublicProduction Unit CalcGood CalcTask where
  publicStock := initialCalcStock
  capacity _ _ := 1
  input := sharedOps.input
  output := sharedOps.output
  laborHours _ := 1
  authorized _ _ := True

instance (p : Unit) (t : CalcTask) (r : ℕ) :
    Decidable (initialCalcProduction.CanExecute p t r) := by
  dsimp [PublicProduction.CanExecute, initialCalcProduction, initialCalcStock, sharedOps]
  infer_instance

/-- Shared post-prefix labor budget sufficient for either target technique plus
one downstream operation (`1 + 1 ≤ 2`). -/
def sharedPostPrefixLaborCapacity : ℕ := 2

@[reducible] def initialCalcLedger :
    CertificateState.WorkLedger (Person := Unit) (Good := CalcGood) CalcTask where
  production := initialCalcProduction
  certificates :=
    { balance := fun _ => 0
      stock := initialCalcStock
      consumed := fun _ _ => 0 }

@[reducible] def voucherConsumerPrice (_ : CalcGood) : ℕ := 1

/-- Common pre-commitment work execution and certificate issuance. -/
def afterPrefixWorkLedger :
    CertificateState.WorkLedger (Person := Unit) (Good := CalcGood) CalcTask :=
  initialCalcLedger.executeAndIssue () .prefixTask 1 0

/-- Common pre-commitment certificate redemption using atomic `WorkLedger.redeem`. -/
def precommitmentLedger :
    CertificateState.WorkLedger (Person := Unit) (Good := CalcGood) CalcTask :=
  afterPrefixWorkLedger.redeem voucherConsumerPrice () .preGood 1

theorem prefix_task_feasible :
    initialCalcLedger.production.CanExecute () .prefixTask 1 := by
  refine ⟨trivial, by decide, ?_⟩
  intro g; cases g <;> decide

theorem after_prefix_stock_sync :
    afterPrefixWorkLedger.certificates.stock = afterPrefixWorkLedger.production.publicStock :=
  CertificateState.WorkLedger.executeAndIssue_stock_sync
    initialCalcLedger () .prefixTask 1 0 rfl

theorem precommitment_stock_sync :
    precommitmentLedger.certificates.stock = precommitmentLedger.production.publicStock :=
  CertificateState.WorkLedger.redeem_stock_sync
    afterPrefixWorkLedger voucherConsumerPrice () .preGood 1 after_prefix_stock_sync

theorem precommitment_balances :
    precommitmentLedger.production.publicStock .K1 = 2 ∧
    precommitmentLedger.production.publicStock .K2 = 2 ∧
    precommitmentLedger.production.publicStock .setup = 1 ∧
    precommitmentLedger.production.publicStock .Q = 0 ∧
    precommitmentLedger.production.publicStock .C1 = 0 ∧
    precommitmentLedger.production.publicStock .C2 = 0 ∧
    precommitmentLedger.production.publicStock .preGood = 0 ∧
    precommitmentLedger.certificates.balance () = 0 ∧
    precommitmentLedger.certificates.consumed () .preGood = 1 := by
  have hp := prefix_task_feasible
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [precommitmentLedger, CertificateState.WorkLedger.redeem,
      afterPrefixWorkLedger, CertificateState.WorkLedger.executeAndIssue, hp,
      CertificateState.redeem, CertificateState.issue, PublicProduction.execute,
      initialCalcProduction, initialCalcStock, voucherConsumerPrice]

theorem precommitment_capacities :
    precommitmentLedger.production.capacity () .prefixTask = 0 ∧
    precommitmentLedger.production.capacity () .techA = 1 ∧
    precommitmentLedger.production.capacity () .techB = 1 ∧
    precommitmentLedger.production.capacity () .down1 = 1 ∧
    precommitmentLedger.production.capacity () .down2 = 1 := by
  have hp := prefix_task_feasible
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [precommitmentLedger, CertificateState.WorkLedger.redeem,
      afterPrefixWorkLedger, CertificateState.WorkLedger.executeAndIssue, hp,
      initialCalcLedger, initialCalcProduction]

theorem precommitment_input (t : CalcTask) (g : CalcGood) :
    precommitmentLedger.production.input t g = sharedOps.input t g := by
  have hp := prefix_task_feasible
  simp [precommitmentLedger, CertificateState.WorkLedger.redeem,
    afterPrefixWorkLedger, CertificateState.WorkLedger.executeAndIssue, hp]

theorem precommitment_output (t : CalcTask) (g : CalcGood) :
    precommitmentLedger.production.output t g = sharedOps.output t g := by
  have hp := prefix_task_feasible
  simp [precommitmentLedger, CertificateState.WorkLedger.redeem,
    afterPrefixWorkLedger, CertificateState.WorkLedger.executeAndIssue, hp]

theorem precommitment_authorized (p : Unit) (t : CalcTask) :
    precommitmentLedger.production.authorized p t ↔ True := by
  have hp := prefix_task_feasible
  simp [precommitmentLedger, CertificateState.WorkLedger.redeem,
    afterPrefixWorkLedger, CertificateState.WorkLedger.executeAndIssue, hp]

theorem precommitment_laborHours (t : CalcTask) :
    precommitmentLedger.production.laborHours t = 1 := by
  have hp := prefix_task_feasible
  simp [precommitmentLedger, CertificateState.WorkLedger.redeem,
    afterPrefixWorkLedger, CertificateState.WorkLedger.executeAndIssue, hp]

instance (p : Unit) (t : CalcTask) (r : ℕ) :
    Decidable (precommitmentLedger.production.CanExecute p t r) := by
  unfold PublicProduction.CanExecute
  rw [precommitment_authorized p t]
  infer_instance

theorem both_methods_initially_feasible :
    precommitmentLedger.production.CanExecute () .techA 1 ∧
    precommitmentLedger.production.CanExecute () .techB 1 := by
  rcases precommitment_balances with ⟨hk1, hk2, hset, _, _, _, _, _, _⟩
  rcases precommitment_capacities with ⟨_, hca, hcb, _, _⟩
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · have hp := prefix_task_feasible
      simp [precommitmentLedger, CertificateState.WorkLedger.redeem,
        afterPrefixWorkLedger, CertificateState.WorkLedger.executeAndIssue, hp]
    · omega
    · intro g
      rw [precommitment_input]
      cases g <;> simp [hk1, hk2, hset] at *
  · refine ⟨?_, ?_, ?_⟩
    · have hp := prefix_task_feasible
      simp [precommitmentLedger, CertificateState.WorkLedger.redeem,
        afterPrefixWorkLedger, CertificateState.WorkLedger.executeAndIssue, hp]
    · omega
    · intro g
      rw [precommitment_input]
      cases g <;> simp [hk1, hk2, hset] at *

/-- Execute the selected target technique on the work ledger. -/
def afterMethodLedger (m : Method) :
    CertificateState.WorkLedger (Person := Unit) (Good := CalcGood) CalcTask :=
  precommitmentLedger.executeAndIssue () (methodToTask m) 1 0

def afterMethodProd (m : Method) : PublicProduction Unit CalcGood CalcTask :=
  (afterMethodLedger m).production

theorem afterMethod_feasible (m : Method) :
    precommitmentLedger.production.CanExecute () (methodToTask m) 1 := by
  cases m
  · exact both_methods_initially_feasible.1
  · exact both_methods_initially_feasible.2

instance (m : Method) (p : Unit) (t : CalcTask) (r : ℕ) :
    Decidable ((afterMethodProd m).CanExecute p t r) := by
  unfold PublicProduction.CanExecute
  have hauth : (afterMethodProd m).authorized p t ↔ True := by
    have hs := precommitment_stock_sync
    have hm := afterMethod_feasible m
    simp [afterMethodProd, afterMethodLedger, CertificateState.WorkLedger.executeAndIssue,
      hs, hm, precommitment_authorized]
  rw [hauth]
  infer_instance

theorem method_stock_conservation (m : Method) (g : CalcGood) :
    (afterMethodProd m).publicStock g + sharedOps.input (methodToTask m) g =
      precommitmentLedger.production.publicStock g + sharedOps.output (methodToTask m) g := by
  have hs := precommitment_stock_sync
  have hm := afterMethod_feasible m
  have hin := precommitment_input (methodToTask m) g
  have hout := precommitment_output (methodToTask m) g
  have hle : 1 * precommitmentLedger.production.input (methodToTask m) g ≤
      precommitmentLedger.production.publicStock g := hm.2.2 g
  simp only [afterMethodProd, afterMethodLedger, CertificateState.WorkLedger.executeAndIssue,
    hs, hm, and_self, ↓reduceIte, PublicProduction.execute, one_mul]
  rw [hin, hout]
  rw [hin] at hle
  dsimp [sharedOps] at hle ⊢
  omega

theorem residual_stocks_after_A :
    (afterMethodProd .A).publicStock .K1 = 0 ∧
    (afterMethodProd .A).publicStock .K2 = 1 ∧
    (afterMethodProd .A).publicStock .setup = 0 ∧
    (afterMethodProd .A).publicStock .Q = 1 ∧
    (afterMethodProd .A).publicStock .C1 = 0 ∧
    (afterMethodProd .A).publicStock .C2 = 0 := by
  rcases precommitment_balances with ⟨hk1, hk2, hset, hq, hc1, hc2, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hk1] using method_stock_conservation .A .K1
  · simpa [hk2] using method_stock_conservation .A .K2
  · simpa [hset] using method_stock_conservation .A .setup
  · simpa [hq] using method_stock_conservation .A .Q
  · simpa [hc1] using method_stock_conservation .A .C1
  · simpa [hc2] using method_stock_conservation .A .C2

theorem residual_stocks_after_B :
    (afterMethodProd .B).publicStock .K1 = 1 ∧
    (afterMethodProd .B).publicStock .K2 = 0 ∧
    (afterMethodProd .B).publicStock .setup = 0 ∧
    (afterMethodProd .B).publicStock .Q = 1 ∧
    (afterMethodProd .B).publicStock .C1 = 0 ∧
    (afterMethodProd .B).publicStock .C2 = 0 := by
  rcases precommitment_balances with ⟨hk1, hk2, hset, hq, hc1, hc2, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hk1] using method_stock_conservation .B .K1
  · simpa [hk2] using method_stock_conservation .B .K2
  · simpa [hset] using method_stock_conservation .B .setup
  · simpa [hq] using method_stock_conservation .B .Q
  · simpa [hc1] using method_stock_conservation .B .C1
  · simpa [hc2] using method_stock_conservation .B .C2

theorem afterMethodProd_authorized (m : Method) (p : Unit) (t : CalcTask) :
    (afterMethodProd m).authorized p t := by
  have hs := precommitment_stock_sync
  have hm := afterMethod_feasible m
  simp [afterMethodProd, afterMethodLedger, CertificateState.WorkLedger.executeAndIssue,
    hs, hm, precommitment_authorized]

theorem afterMethodProd_input (m : Method) (t : CalcTask) (g : CalcGood) :
    (afterMethodProd m).input t g = sharedOps.input t g := by
  have hs := precommitment_stock_sync
  have hm := afterMethod_feasible m
  simp [afterMethodProd, afterMethodLedger, CertificateState.WorkLedger.executeAndIssue,
    hs, hm, precommitment_input]

theorem afterMethodProd_output (m : Method) (t : CalcTask) (g : CalcGood) :
    (afterMethodProd m).output t g = sharedOps.output t g := by
  have hs := precommitment_stock_sync
  have hm := afterMethod_feasible m
  simp [afterMethodProd, afterMethodLedger, CertificateState.WorkLedger.executeAndIssue,
    hs, hm, precommitment_output]

theorem afterMethodProd_capacity (m : Method) (p : Unit) (t : CalcTask)
    (hne : t ≠ methodToTask m) (hpre : t ≠ .prefixTask) :
    (afterMethodProd m).capacity p t = 1 := by
  have hs := precommitment_stock_sync
  have hm := afterMethod_feasible m
  cases p
  rcases precommitment_capacities with ⟨_, hca, hcb, hd1, hd2⟩
  simp only [afterMethodProd, afterMethodLedger, CertificateState.WorkLedger.executeAndIssue,
    hs, hm, and_self, ↓reduceIte, Function.update_self, Function.update_of_ne hne]
  cases t
  · exact absurd rfl hpre
  · exact hca
  · exact hcb
  · exact hd1
  · exact hd2

/-- Setup consumption prevents running the alternative target technique after either method. -/
theorem cannot_run_second_method :
    ¬ (afterMethodProd .A).CanExecute () .techB 1 ∧
    ¬ (afterMethodProd .B).CanExecute () .techA 1 := by
  constructor
  · intro hcan
    have hle := hcan.2.2 .setup
    have hset := residual_stocks_after_A.2.2.1
    rw [afterMethodProd_input] at hle
    simp [hset] at hle
  · intro hcan
    have hle := hcan.2.2 .setup
    have hset := residual_stocks_after_B.2.2.1
    rw [afterMethodProd_input] at hle
    simp [hset] at hle

/-- Downstream execution feasibility derived from `PublicProduction.CanExecute`. -/
def downstreamFeasible (m : Method) : DownstreamAct → Prop
  | .idle => True
  | .D1 => (afterMethodProd m).CanExecute () .down1 1
  | .D2 => (afterMethodProd m).CanExecute () .down2 1

theorem downstream_affordability_after_A :
    downstreamFeasible .A .idle ∧
    ¬ downstreamFeasible .A .D1 ∧
    downstreamFeasible .A .D2 := by
  rcases residual_stocks_after_A with ⟨hk1, hk2, _, _, _, _⟩
  refine ⟨trivial, ?_, ?_⟩
  · intro hcan
    have hle := hcan.2.2 .K1
    rw [afterMethodProd_input] at hle
    simp [hk1] at hle
  · refine ⟨afterMethodProd_authorized .A () .down2,
      by simp [afterMethodProd_capacity .A () .down2 (by simp [methodToTask]) (by simp)], ?_⟩
    intro g
    rw [afterMethodProd_input]
    cases g <;> simp [hk2]

theorem downstream_affordability_after_B :
    downstreamFeasible .B .idle ∧
    downstreamFeasible .B .D1 ∧
    ¬ downstreamFeasible .B .D2 := by
  rcases residual_stocks_after_B with ⟨hk1, hk2, _, _, _, _⟩
  refine ⟨trivial, ?_, ?_⟩
  · refine ⟨afterMethodProd_authorized .B () .down1,
      by simp [afterMethodProd_capacity .B () .down1 (by simp [methodToTask]) (by simp)], ?_⟩
    intro g
    rw [afterMethodProd_input]
    cases g <;> simp [hk1]
  · intro hcan
    have hle := hcan.2.2 .K2
    rw [afterMethodProd_input] at hle
    simp [hk2] at hle

/-- Terminal physical stock after executing `m` and then `d`. -/
def afterDownstreamStock (m : Method) : DownstreamAct → CalcGood → ℕ
  | .idle => (afterMethodProd m).publicStock
  | .D1 => (afterMethodProd m).execute () .down1 1
  | .D2 => (afterMethodProd m).execute () .down2 1

theorem terminal_outcomes_table :
    (afterDownstreamStock .A .idle .C1 = 0 ∧ afterDownstreamStock .A .idle .C2 = 0 ∧
      afterDownstreamStock .A .idle .Q = 1) ∧
    (afterDownstreamStock .A .D2 .C1 = 0 ∧ afterDownstreamStock .A .D2 .C2 = 1 ∧
      afterDownstreamStock .A .D2 .Q = 1) ∧
    (afterDownstreamStock .B .idle .C1 = 0 ∧ afterDownstreamStock .B .idle .C2 = 0 ∧
      afterDownstreamStock .B .idle .Q = 1) ∧
    (afterDownstreamStock .B .D1 .C1 = 1 ∧ afterDownstreamStock .B .D1 .C2 = 0 ∧
      afterDownstreamStock .B .D1 .Q = 1) := by
  have hA := residual_stocks_after_A
  have hB := residual_stocks_after_B
  have hAD2 : (afterMethodProd .A).CanExecute () .down2 1 := downstream_affordability_after_A.2.2
  have hBD1 : (afterMethodProd .B).CanExecute () .down1 1 := downstream_affordability_after_B.2.1
  refine ⟨⟨hA.2.2.2.2.1, hA.2.2.2.2.2, hA.2.2.2.1⟩, ?_,
    ⟨hB.2.2.2.2.1, hB.2.2.2.2.2, hB.2.2.2.1⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [afterDownstreamStock, PublicProduction.execute, hAD2,
        afterMethodProd_input, afterMethodProd_output, hA.2.2.2.2.1]
    · simp [afterDownstreamStock, PublicProduction.execute, hAD2,
        afterMethodProd_input, afterMethodProd_output, hA.2.2.2.2.2]
    · simp [afterDownstreamStock, PublicProduction.execute, hAD2,
        afterMethodProd_input, afterMethodProd_output, hA.2.2.2.1]
  · refine ⟨?_, ?_, ?_⟩
    · simp [afterDownstreamStock, PublicProduction.execute, hBD1,
        afterMethodProd_input, afterMethodProd_output, hB.2.2.2.2.1]
    · simp [afterDownstreamStock, PublicProduction.execute, hBD1,
        afterMethodProd_input, afterMethodProd_output, hB.2.2.2.2.2]
    · simp [afterDownstreamStock, PublicProduction.execute, hBD1,
        afterMethodProd_input, afterMethodProd_output, hB.2.2.2.1]

/-! ## 2. Economic Criterion and ActionFrame Bridge -/

/-- Private downstream valuation state revealed only after technique commitment. -/
inductive World where
  | wantsC1
  | wantsC2
  deriving DecidableEq, Inhabited, Repr

instance : Fintype World where
  elems := {.wantsC1, .wantsC2}
  complete := by intro w; cases w <;> decide

def worldGoal : World → CalcGood
  | .wantsC1 => .C1
  | .wantsC2 => .C2

def methodFeasible (m : Method) : Prop :=
  precommitmentLedger.production.CanExecute () (methodToTask m) 1 ∧
  1 ≤ (afterMethodProd m).publicStock .Q

/-- Purely ordinal preference over physical terminal bundles. -/
def worldStrictlyPrefers (w : World) (b₁ b₂ : CalcGood → ℕ) : Prop :=
  1 ≤ b₁ (worldGoal w) ∧ b₂ (worldGoal w) = 0

/-- Acceptability is defined solely from physical feasibility, required output `Q`,
and ordinal end attainment, without reading any observation map. -/
def acceptable (w : World) (m : Method) : Prop :=
  methodFeasible m ∧
  ∃ d, downstreamFeasible m d ∧
    ∀ m' d', methodFeasible m' → downstreamFeasible m' d' →
      ¬ worldStrictlyPrefers w (afterDownstreamStock m' d') (afterDownstreamStock m d)

theorem methodFeasible_all (m : Method) : methodFeasible m := by
  cases m
  · exact ⟨both_methods_initially_feasible.1, by simp [residual_stocks_after_A.2.2.2.1]⟩
  · exact ⟨both_methods_initially_feasible.2, by simp [residual_stocks_after_B.2.2.2.1]⟩

theorem acceptable_wantsC1_iff (m : Method) : acceptable .wantsC1 m ↔ m = .B := by
  rcases terminal_outcomes_table with ⟨⟨hAi1, _, _⟩, ⟨hAD1, _, _⟩, ⟨hBi1, _, _⟩, ⟨hBD1, _, _⟩⟩
  constructor
  · rintro ⟨_, d, hd, hbest⟩
    cases m
    · exfalso
      apply hbest .B .D1 (methodFeasible_all .B) downstream_affordability_after_B.2.1
      cases d
      · exact ⟨by simp [worldGoal, hBD1], hAi1⟩
      · exact (downstream_affordability_after_A.2.1 hd).elim
      · exact ⟨by simp [worldGoal, hBD1], hAD1⟩
    · rfl
  · rintro rfl
    refine ⟨methodFeasible_all .B, .D1, downstream_affordability_after_B.2.1, ?_⟩
    intro m' d' _ _ ⟨_, h0⟩
    simp [worldGoal, hBD1] at h0

theorem acceptable_wantsC2_iff (m : Method) : acceptable .wantsC2 m ↔ m = .A := by
  rcases terminal_outcomes_table with ⟨⟨_, hAi2, _⟩, ⟨_, hAD2, _⟩, ⟨_, hBi2, _⟩, ⟨_, hBD2, _⟩⟩
  constructor
  · rintro ⟨_, d, hd, hbest⟩
    cases m
    · rfl
    · exfalso
      apply hbest .A .D2 (methodFeasible_all .A) downstream_affordability_after_A.2.2
      cases d
      · exact ⟨by simp [worldGoal, hAD2], hBi2⟩
      · exact ⟨by simp [worldGoal, hAD2], hBD2⟩
      · exact (downstream_affordability_after_B.2.2 hd).elim
  · rintro rfl
    refine ⟨methodFeasible_all .A, .D2, downstream_affordability_after_A.2.2, ?_⟩
    intro m' d' _ _ ⟨_, h0⟩
    simp [worldGoal, hAD2] at h0

theorem exists_acceptable (w : World) : ∃ m, acceptable w m := by
  cases w
  · exact ⟨.B, (acceptable_wantsC1_iff .B).mpr rfl⟩
  · exact ⟨.A, (acceptable_wantsC2_iff .A).mpr rfl⟩

/-- Single reduction lemma for any world-blind record. -/
theorem unsolvable_of_world_blind {Record : Type} (obs : World → Record)
    (h_same : obs .wantsC1 = obs .wantsC2) :
    ¬ (InformationProblem.mk obs acceptable).Solvable := by
  apply InformationProblem.unsolvable_of_conflicting_states _ .wantsC1 .wantsC2 h_same
  rintro (⟨⟩ | ⟨⟩) ⟨h1, h2⟩
  · exact Method.noConfusion ((acceptable_wantsC1_iff .A).mp h1)
  · exact Method.noConfusion ((acceptable_wantsC2_iff .B).mp h2)

/-! ### ActionFrame connection over the two-stage physical program -/

def calcInitialPhysicalState : PhysicalState Unit CalcGood Unit :=
  PhysicalState.zeroServices (fun _ => precommitmentLedger.production.publicStock)

def calcStage0Choices : FiniteChoiceStage Unit CalcGood CalcTask where
  menu _ := {.idle, .operate .techA, .operate .techB}
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

@[reducible] def calcStage0 : FinitePhysicalChoiceStage Unit CalcGood CalcTask Unit where
  choices := calcStage0Choices
  operations := sharedOps
  before := calcInitialPhysicalState
  menu_affordable i a ha m := by
    cases i
    simp only [calcStage0Choices, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp [rawActionUse]
    · have hcan := both_methods_initially_feasible.1
      have hle := hcan.2.2 m
      rw [precommitment_input] at hle
      simpa [rawActionUse, calcInitialPhysicalState, PhysicalState.zeroServices] using hle
    · have hcan := both_methods_initially_feasible.2
      have hle := hcan.2.2 m
      rw [precommitment_input] at hle
      simpa [rawActionUse, calcInitialPhysicalState, PhysicalState.zeroServices] using hle

def stage0Profile (a : EconomyAction Unit CalcGood CalcTask)
    (ha : a ∈ calcStage0Choices.menu ()) : calcStage0Choices.Profile :=
  ⟨fun _ => a, fun _ => ha⟩

def profileTechA : calcStage0Choices.Profile :=
  stage0Profile (.operate .techA) (by simp [calcStage0Choices])

def profileTechB : calcStage0Choices.Profile :=
  stage0Profile (.operate .techB) (by simp [calcStage0Choices])

def profileIdle0 : calcStage0Choices.Profile :=
  stage0Profile .idle (by simp [calcStage0Choices])

theorem stage0_advance_matches_method (m : Method) :
    (calcStage0.advance (stage0Profile (.operate (methodToTask m))
        (by cases m <;> simp [methodToTask, calcStage0Choices]))).stock () =
      (afterMethodProd m).publicStock := by
  funext g
  have hbal := calcStage0.advance_balance
    (stage0Profile (.operate (methodToTask m))
      (by cases m <;> simp [methodToTask, calcStage0Choices])) () g
  have hcon := method_stock_conservation m g
  conv at hbal =>
    lhs
    arg 2
    simp [calcStage0, effectiveUse, stage0Profile]
  conv at hbal =>
    rhs
    arg 2
    simp [calcStage0, effectiveYield, stage0Profile]
  change _ + sharedOps.input (methodToTask m) g =
    precommitmentLedger.production.publicStock g + sharedOps.output (methodToTask m) g at hbal
  omega

def stage1Menu (p : calcStage0Choices.Profile) :
    Finset (EconomyAction Unit CalcGood CalcTask) :=
  if p.1 () = .operate .techA then {.idle, .operate .down2}
  else if p.1 () = .operate .techB then {.idle, .operate .down1}
  else {.idle, .operate .down1, .operate .down2}

def calcStage1Choices (p : calcStage0Choices.Profile) :
    FiniteChoiceStage Unit CalcGood CalcTask where
  menu _ := stage1Menu p
  idle_mem _ := by
    unfold stage1Menu
    split_ifs <;> simp
  activeAgents := {()}
  active_iff i := by
    cases i
    simp only [Finset.mem_singleton, true_iff]
    unfold stage1Menu
    split_ifs
    · exact ⟨.operate .down2, by simp, by simp⟩
    · exact ⟨.operate .down1, by simp, by simp⟩
    · exact ⟨.operate .down1, by simp, by simp⟩
  maxActiveAgents := 1
  activity_bound := by simp
  menu_wellFormed i a ha := by
    unfold stage1Menu at ha
    split_ifs at ha <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha <;>
      rcases ha with rfl | rfl | rfl <;>
      simp [EconomyAction.WellFormed]

theorem stage1_menu_affordable (p : calcStage0Choices.Profile) :
    ∀ actor a, a ∈ (calcStage1Choices p).menu actor →
      actionAffordable sharedOps (calcStage0.advance p) actor a := by
  intro actor a ha g
  cases actor
  have hmenu := p.2 ()
  simp only [calcStage0Choices, Finset.mem_insert, Finset.mem_singleton] at hmenu
  have hbal := calcStage0.advance_balance p () g
  change (calcStage0.advance p).stock () g + effectiveUse sharedOps p.1 () g =
    calcStage0.before.stock () g + effectiveYield sharedOps p.1 () g at hbal
  rcases hmenu with hidle | hA | hB
  · have huse : effectiveUse sharedOps p.1 () g = 0 := by simp [effectiveUse, hidle]
    have hyield : effectiveYield sharedOps p.1 () g = 0 := by simp [effectiveYield, hidle]
    rw [huse, hyield] at hbal
    have hk : (calcStage0.advance p).stock () g = precommitmentLedger.production.publicStock g := by
      simpa [calcStage0, calcInitialPhysicalState, PhysicalState.zeroServices] using hbal
    have ha' : a = .idle ∨ a = .operate .down1 ∨ a = .operate .down2 := by
      simpa [calcStage1Choices, stage1Menu, hidle] using ha
    rcases ha' with rfl | rfl | rfl
    · simp [rawActionUse]
    · rw [hk]; cases g <;> simp [rawActionUse, precommitment_balances]
    · rw [hk]; cases g <;> simp [rawActionUse, precommitment_balances]
  · have ha' : a = .idle ∨ a = .operate .down2 := by
      simpa [calcStage1Choices, stage1Menu, hA] using ha
    rcases ha' with rfl | rfl
    · simp [rawActionUse]
    · have hp : p = profileTechA := Subtype.ext (funext fun i => by cases i; exact hA)
      subst hp
      have hst := congrArg (· g) (stage0_advance_matches_method .A)
      change (calcStage0.advance profileTechA).stock () g =
        (afterMethodProd .A).publicStock g at hst
      rw [hst]
      cases g <;> simp [rawActionUse, residual_stocks_after_A]
  · have ha' : a = .idle ∨ a = .operate .down1 := by
      simpa [calcStage1Choices, stage1Menu, hB] using ha
    rcases ha' with rfl | rfl
    · simp [rawActionUse]
    · have hp : p = profileTechB := Subtype.ext (funext fun i => by cases i; exact hB)
      subst hp
      have hst := congrArg (· g) (stage0_advance_matches_method .B)
      change (calcStage0.advance profileTechB).stock () g =
        (afterMethodProd .B).publicStock g at hst
      rw [hst]
      cases g <;> simp [rawActionUse, residual_stocks_after_B]

@[reducible] def calcStage1 (p : calcStage0Choices.Profile) :
    FinitePhysicalChoiceStage Unit CalcGood CalcTask Unit where
  choices := calcStage1Choices p
  operations := sharedOps
  before := calcStage0.advance p
  menu_affordable := stage1_menu_affordable p

@[reducible] def calcContinuation (p : calcStage0Choices.Profile) :
    FinitePhysicalEconomyProgram Unit CalcGood CalcTask Unit 1 (calcStage0.advance p) :=
  .decision (state := calcStage0.advance p) (calcStage1 p) (fun _ => .halt)

/-- Two-stage physical execution program shared by both worlds. -/
@[reducible] def calcProgram :
    FinitePhysicalEconomyProgram Unit CalcGood CalcTask Unit 2 calcInitialPhysicalState :=
  .decision (state := calcInitialPhysicalState) calcStage0 calcContinuation

theorem calcProgram_stable : calcProgram.HasStableOperationSemantics sharedOps := by
  change calcStage0.operations = sharedOps ∧
    ∀ p, (calcContinuation p).HasStableOperationSemantics sharedOps
  exact ⟨rfl, fun _ => ⟨rfl, fun _ => trivial⟩⟩

def calcProgramEndBundle : calcProgram.End → (CalcGood → ℕ)
  | .bundle b => b
  | .timed e _ => calcProgramEndBundle e
  | .quantity m q => fun m' => if m' = m then q else 0

def calcValuedEnd (w : World) (e : calcProgram.End) : Prop :=
  e = .quantity (worldGoal w) 1

theorem worldStrictlyPrefers_iff_subjective_dominates (w : World) (b₁ b₂ : CalcGood → ℕ) :
    SubjectiveTeleologicalDominates finiteProgramEndRequirement (calcValuedEnd w) b₁ b₂ ↔
      worldStrictlyPrefers w b₁ b₂ := by
  constructor
  · rintro ⟨_, ⟨S, hval, hatt₁, hnatt₂⟩⟩
    have hS : S = {.quantity (worldGoal w) 1} := by
      have hsub : S ⊆ {.quantity (worldGoal w) 1} := fun e he => by
        simpa [calcValuedEnd] using hval e he
      rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
      · exfalso; apply hnatt₂; intro g; simp
      · rfl
    subst hS
    refine ⟨?_, ?_⟩
    · have h1 := hatt₁ (worldGoal w)
      simpa [finiteProgramEndRequirement] using h1
    · by_contra hne
      apply hnatt₂
      intro g
      by_cases hg : g = worldGoal w
      · subst g
        simpa [finiteProgramEndRequirement] using Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
      · simp [finiteProgramEndRequirement, hg]
  · rintro ⟨hb₁, hb₂⟩
    refine ⟨?_, ⟨{.quantity (worldGoal w) 1}, ?_, ?_, ?_⟩⟩
    · intro S hval hatt g
      have hsub : S ⊆ {.quantity (worldGoal w) 1} := fun e he => by
        simpa [calcValuedEnd] using hval e he
      rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
      · simp
      · exfalso
        have hbad := hatt (worldGoal w)
        simp [finiteProgramEndRequirement, hb₂] at hbad
    · intro e he
      simp only [Finset.mem_singleton] at he
      subst e
      rfl
    · intro g
      by_cases hg : g = worldGoal w
      · subst g; simpa [finiteProgramEndRequirement] using hb₁
      · simp [finiteProgramEndRequirement, hg]
    · intro hatt
      have hbad := hatt (worldGoal w)
      simp [finiteProgramEndRequirement, hb₂] at hbad

def stage1DownstreamProfile (p : calcStage0Choices.Profile) (w : World) :
    (calcStage1Choices p).Profile :=
  ⟨fun _ =>
    if p.1 () = .operate .techA then
      match w with | .wantsC2 => .operate .down2 | .wantsC1 => .idle
    else if p.1 () = .operate .techB then
      match w with | .wantsC1 => .operate .down1 | .wantsC2 => .idle
    else .idle,
   fun _ => by
     dsimp [calcStage1Choices, stage1Menu]
     split_ifs <;> cases w <;> simp⟩

def continueWithOptimal (w : World) (p : calcStage0Choices.Profile) :
    FinitePhysicalEconomyProgram.History (calcContinuation p) :=
  .decision (stage1DownstreamProfile p w) .halt

def optimalProgramHistory : World → calcProgram.History
  | .wantsC1 => .decision profileTechB (continueWithOptimal .wantsC1 profileTechB)
  | .wantsC2 => .decision profileTechA (continueWithOptimal .wantsC2 profileTechA)

def worldReferenceHistory (w : World) (_actor : Unit) :
    calcProgram.Moment → calcProgram.History
  | .root => optimalProgramHistory w
  | .afterProfile p .root => .decision p (continueWithOptimal w p)
  | .afterProfile p (.afterProfile q .root) => .decision p (.decision q .halt)

theorem worldReferenceHistory_mem (w : World) (actor : Unit) (t : calcProgram.Moment) :
    FiniteEconomyProgram.ProgramMoment.memHist calcProgram.toFiniteEconomyProgram t
      (worldReferenceHistory w actor t) := by
  match t with
  | .root =>
      exact FiniteEconomyProgram.ProgramMoment.root_memHist _
  | .afterProfile p .root =>
      dsimp [worldReferenceHistory, FiniteEconomyProgram.ProgramMoment.memHist]
      exact ⟨rfl, trivial⟩
  | .afterProfile p (.afterProfile q .root) =>
      dsimp [worldReferenceHistory, FiniteEconomyProgram.ProgramMoment.memHist]
      exact ⟨rfl, ⟨rfl, trivial⟩⟩

noncomputable def calcBaseBehavior (w : World) : calcProgram.ActionFrameBehavior :=
  FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory
    (worldReferenceHistory w) (worldReferenceHistory_mem w)
    (fun _ _ _ e => calcValuedEnd w e)
    (fun _ _ _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ e₁ e₂ =>
      SubjectiveTeleologicalDominates finiteProgramEndRequirement (calcValuedEnd w)
        (calcProgramEndBundle e₁) (calcProgramEndBundle e₂))
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ h₁ h₂ => by
      rcases h₁ with ⟨_, ⟨S, hval, hatt₁, hnatt₂⟩⟩
      exact hnatt₂ (h₂.1 S hval hatt₁))
    (fun _ _ _ _ _ h => h)

noncomputable def calcBehavior (w : World) : calcProgram.ActionFrameBehavior :=
  (calcBaseBehavior w).withRootContinuation (continueWithOptimal w)

private theorem enactedAt_decision_afterProfile
    {fuel : ℕ} {State Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation]
    {state : State} {stage : FiniteChoiceStage Agent Means Operation}
    {advance : stage.Profile → State}
    {continuation : ∀ profile,
      FiniteEconomyProgram State Agent Means Operation fuel (advance profile)}
    (p : stage.Profile) (tail : FiniteEconomyProgram.ProgramHistory (continuation p))
    (m : FiniteEconomyProgram.ProgramMoment (continuation p)) (actor : Agent) :
    FiniteEconomyProgram.ProgramHistory.enactedAt
      (FiniteEconomyProgram.ProgramHistory.decision (state := state) (stage := stage)
        (advance := advance) (continuation := continuation) p tail)
      (FiniteEconomyProgram.ProgramMoment.afterProfile (state := state) (stage := stage)
        (advance := advance) (continuation := continuation) p m)
      actor =
      FiniteEconomyProgram.ProgramHistory.enactedAt tail m actor := by
  simp only [FiniteEconomyProgram.ProgramHistory.enactedAt, ↓reduceDIte]

private theorem calcContinuation_history_form (p : calcStage0Choices.Profile)
    (t : FiniteEconomyProgram.ProgramHistory (calcContinuation p).toFiniteEconomyProgram) :
    ∃ q : (calcStage1Choices p).Profile, t = .decision q .halt := by
  dsimp [calcContinuation, FinitePhysicalEconomyProgram.toFiniteEconomyProgram,
    FiniteEconomyProgram.physicalDecision, calcStage1] at t
  cases t with
  | decision q rest =>
      cases rest
      exact ⟨q, rfl⟩

private theorem calcProgram_enactedAt_afterProfile
    (p : calcStage0Choices.Profile) (tail : (calcContinuation p).History) :
    FiniteEconomyProgram.ProgramHistory.enactedAt
      ((FiniteEconomyProgram.ProgramHistory.decision
        (state := calcInitialPhysicalState) (stage := calcStage0Choices)
        (advance := calcStage0.advance)
        (continuation := fun profile => (calcContinuation profile).toFiniteEconomyProgram)
        p tail) : calcProgram.History)
      (FiniteEconomyProgram.ProgramMoment.afterProfile p .root : calcProgram.Moment) () =
      FiniteEconomyProgram.ProgramHistory.enactedAt tail .root () := by
  dsimp [FinitePhysicalEconomyProgram.History, calcProgram,
    FinitePhysicalEconomyProgram.toFiniteEconomyProgram,
    FiniteEconomyProgram.physicalDecision, calcStage0]
  exact enactedAt_decision_afterProfile
    (continuation := fun profile => (calcContinuation profile).toFiniteEconomyProgram)
    p tail .root ()

private theorem calcProgram_history_eq_of_mem_enacted
    (p : calcStage0Choices.Profile) (a : EconomyAction Unit CalcGood CalcTask)
    (ha : a ∈ (calcStage1Choices p).menu ())
    (h : calcProgram.History)
    (hmem : FiniteEconomyProgram.ProgramMoment.memHist calcProgram.toFiniteEconomyProgram
      (FiniteEconomyProgram.ProgramMoment.afterProfile p .root) h)
    (hen : FiniteEconomyProgram.ProgramHistory.enactedAt h
      (FiniteEconomyProgram.ProgramMoment.afterProfile p .root) () = a) :
    h = .decision p (.decision ⟨fun _ => a, fun _ => ha⟩ .halt) := by
  revert h hmem hen
  dsimp [FinitePhysicalEconomyProgram.History, calcProgram,
    FinitePhysicalEconomyProgram.toFiniteEconomyProgram,
    FiniteEconomyProgram.physicalDecision]
  intro h hmem hen
  cases h with
  | decision p' tail =>
      rcases hmem with ⟨hprof, hmem_tail⟩
      clear hmem_tail
      revert tail hen
      cases hprof
      intro tail hen
      rcases calcContinuation_history_form p tail with ⟨q, rfl⟩
      have hstep :
          FiniteEconomyProgram.ProgramHistory.enactedAt
            (FiniteEconomyProgram.ProgramHistory.decision
              (state := calcInitialPhysicalState) (stage := calcStage0Choices)
              (advance := calcStage0.advance)
              (continuation := fun profile => (calcContinuation profile).toFiniteEconomyProgram)
              p (.decision q .halt))
            (FiniteEconomyProgram.ProgramMoment.afterProfile
              (state := calcInitialPhysicalState) (stage := calcStage0Choices)
              (advance := calcStage0.advance)
              (continuation := fun profile => (calcContinuation profile).toFiniteEconomyProgram)
              p .root) () = q.1 () :=
        (enactedAt_decision_afterProfile
          (state := calcInitialPhysicalState) (stage := calcStage0Choices)
          (advance := calcStage0.advance)
          (continuation := fun profile => (calcContinuation profile).toFiniteEconomyProgram)
          p (.decision q .halt) .root ()).trans
          (by
            simp [FiniteEconomyProgram.ProgramHistory.enactedAt])
      have hq1 : q.1 () = a := hstep.symm.trans hen
      have hq : q = ⟨fun _ => a, fun _ => ha⟩ := by
        apply Subtype.ext; funext i; cases i; exact hq1
      subst hq
      rfl

/-- Separate `ActionFrame` world over the shared two-stage physical program. -/
@[instance_reducible] noncomputable def worldFrame (w : World) : ActionFrame :=
  calcProgram.toActionFrame sharedOps calcProgram_stable (calcBehavior w)

def momentAfterTechB : calcProgram.Moment :=
  FiniteEconomyProgram.ProgramMoment.afterProfile profileTechB .root

def momentAfterTechA : calcProgram.Moment :=
  FiniteEconomyProgram.ProgramMoment.afterProfile profileTechA .root

theorem downstream_advance_D1 :
    ((calcStage1 profileTechB).advance (stage1DownstreamProfile profileTechB .wantsC1)).stock
        () .C1 = 1 := by
  have hbal := (calcStage1 profileTechB).advance_balance
    (stage1DownstreamProfile profileTechB .wantsC1) () .C1
  change ((calcStage1 profileTechB).advance
      (stage1DownstreamProfile profileTechB .wantsC1)).stock () .C1 +
      effectiveUse sharedOps (stage1DownstreamProfile profileTechB .wantsC1).1 () .C1 =
    (calcStage1 profileTechB).before.stock () .C1 +
      effectiveYield sharedOps (stage1DownstreamProfile profileTechB .wantsC1).1 () .C1 at hbal
  have huse : effectiveUse sharedOps
      (stage1DownstreamProfile profileTechB .wantsC1).1 () .C1 = 0 := by
    simp [effectiveUse, stage1DownstreamProfile, profileTechB, stage0Profile]
  have hyield : effectiveYield sharedOps
      (stage1DownstreamProfile profileTechB .wantsC1).1 () .C1 = 1 := by
    simp [effectiveYield, stage1DownstreamProfile, profileTechB, stage0Profile]
  have hbef : (calcStage1 profileTechB).before.stock () .C1 = 0 := by
    change (calcStage0.advance profileTechB).stock () .C1 = 0
    have hst := congrArg (· .C1) (stage0_advance_matches_method .B)
    change (calcStage0.advance profileTechB).stock () .C1 =
      (afterMethodProd .B).publicStock .C1 at hst
    rw [hst, residual_stocks_after_B.2.2.2.2.1]
  rw [huse, hyield] at hbal
  omega

theorem downstream_advance_D2 :
    ((calcStage1 profileTechA).advance (stage1DownstreamProfile profileTechA .wantsC2)).stock
        () .C2 = 1 := by
  have hbal := (calcStage1 profileTechA).advance_balance
    (stage1DownstreamProfile profileTechA .wantsC2) () .C2
  change ((calcStage1 profileTechA).advance
      (stage1DownstreamProfile profileTechA .wantsC2)).stock () .C2 +
      effectiveUse sharedOps (stage1DownstreamProfile profileTechA .wantsC2).1 () .C2 =
    (calcStage1 profileTechA).before.stock () .C2 +
      effectiveYield sharedOps (stage1DownstreamProfile profileTechA .wantsC2).1 () .C2 at hbal
  have huse : effectiveUse sharedOps
      (stage1DownstreamProfile profileTechA .wantsC2).1 () .C2 = 0 := by
    simp [effectiveUse, stage1DownstreamProfile, profileTechA, stage0Profile]
  have hyield : effectiveYield sharedOps
      (stage1DownstreamProfile profileTechA .wantsC2).1 () .C2 = 1 := by
    simp [effectiveYield, stage1DownstreamProfile, profileTechA, stage0Profile]
  have hbef : (calcStage1 profileTechA).before.stock () .C2 = 0 := by
    change (calcStage0.advance profileTechA).stock () .C2 = 0
    have hst := congrArg (· .C2) (stage0_advance_matches_method .A)
    change (calcStage0.advance profileTechA).stock () .C2 =
      (afterMethodProd .A).publicStock .C2 at hst
    rw [hst, residual_stocks_after_A.2.2.2.2.2]
  rw [huse, hyield] at hbal
  omega

theorem downstream_idle_C1_zero :
    ((calcStage1 profileTechB).advance
      ⟨fun _ => .idle, (calcStage1Choices profileTechB).idle_mem⟩).stock () .C1 = 0 := by
  have hbal := (calcStage1 profileTechB).advance_balance
    ⟨fun _ => .idle, (calcStage1Choices profileTechB).idle_mem⟩ () .C1
  change ((calcStage1 profileTechB).advance
      ⟨fun _ => .idle, (calcStage1Choices profileTechB).idle_mem⟩).stock () .C1 +
      effectiveUse sharedOps (fun _ => EconomyAction.idle) () .C1 =
    (calcStage1 profileTechB).before.stock () .C1 +
      effectiveYield sharedOps (fun _ => EconomyAction.idle) () .C1 at hbal
  have huse : effectiveUse sharedOps (fun _ => EconomyAction.idle) () .C1 = 0 := rfl
  have hyield : effectiveYield sharedOps (fun _ => EconomyAction.idle) () .C1 = 0 := rfl
  have hbef : (calcStage1 profileTechB).before.stock () .C1 = 0 := by
    change (calcStage0.advance profileTechB).stock () .C1 = 0
    have hst := congrArg (· .C1) (stage0_advance_matches_method .B)
    change (calcStage0.advance profileTechB).stock () .C1 =
      (afterMethodProd .B).publicStock .C1 at hst
    rw [hst, residual_stocks_after_B.2.2.2.2.1]
  rw [huse, hyield] at hbal
  omega

theorem downstream_idle_C2_zero :
    ((calcStage1 profileTechA).advance
      ⟨fun _ => .idle, (calcStage1Choices profileTechA).idle_mem⟩).stock () .C2 = 0 := by
  have hbal := (calcStage1 profileTechA).advance_balance
    ⟨fun _ => .idle, (calcStage1Choices profileTechA).idle_mem⟩ () .C2
  change ((calcStage1 profileTechA).advance
      ⟨fun _ => .idle, (calcStage1Choices profileTechA).idle_mem⟩).stock () .C2 +
      effectiveUse sharedOps (fun _ => EconomyAction.idle) () .C2 =
    (calcStage1 profileTechA).before.stock () .C2 +
      effectiveYield sharedOps (fun _ => EconomyAction.idle) () .C2 at hbal
  have huse : effectiveUse sharedOps (fun _ => EconomyAction.idle) () .C2 = 0 := rfl
  have hyield : effectiveYield sharedOps (fun _ => EconomyAction.idle) () .C2 = 0 := rfl
  have hbef : (calcStage1 profileTechA).before.stock () .C2 = 0 := by
    change (calcStage0.advance profileTechA).stock () .C2 = 0
    have hst := congrArg (· .C2) (stage0_advance_matches_method .A)
    change (calcStage0.advance profileTechA).stock () .C2 =
      (afterMethodProd .A).publicStock .C2 at hst
    rw [hst, residual_stocks_after_A.2.2.2.2.2]
  rw [huse, hyield] at hbal
  omega

/-- Purposeful downstream execution on the `wantsC1` branch (`down1` after `techB`). -/
theorem wantsC1_downstream_purposeful :
    @PurposefulAct (worldFrame .wantsC1) () momentAfterTechB
      (optimalProgramHistory .wantsC1) (.operate .down1) := by
  have hmem : (worldFrame .wantsC1).mem_hist momentAfterTechB (optimalProgramHistory .wantsC1) := by
    change ∃ hprofile : profileTechB = profileTechB,
      FiniteEconomyProgram.ProgramMoment.memHist _ .root
        (hprofile ▸ continueWithOptimal .wantsC1 profileTechB)
    exact ⟨rfl, FiniteEconomyProgram.ProgramMoment.root_memHist _⟩
  have henacted_at :
      FiniteEconomyProgram.ProgramHistory.enactedAt
        (optimalProgramHistory .wantsC1) momentAfterTechB () = .operate .down1 :=
    (calcProgram_enactedAt_afterProfile profileTechB
      (continueWithOptimal .wantsC1 profileTechB)).trans
      (by
        simp [continueWithOptimal, FinitePhysicalEconomyProgram.toFiniteEconomyProgram,
          FiniteEconomyProgram.physicalDecision, FiniteEconomyProgram.ProgramHistory.enactedAt,
          stage1DownstreamProfile, profileTechB, stage0Profile])
  have henacted : (worldFrame .wantsC1).enacted () momentAfterTechB
      (optimalProgramHistory .wantsC1) = .operate .down1 := henacted_at
  have hfeas : EconomyAction.operate .down1 ∈
      (worldFrame .wantsC1).A_feas () momentAfterTechB (optimalProgramHistory .wantsC1) := by
    rw [← henacted]
    exact (worldFrame .wantsC1).enacted_in_A_feas () momentAfterTechB
      (optimalProgramHistory .wantsC1) hmem
  have hexec : @Exec (worldFrame .wantsC1) () momentAfterTechB (.operate .down1)
      (optimalProgramHistory .wantsC1) := ⟨hmem, henacted⟩
  have hgain : (worldFrame .wantsC1).Preference () momentAfterTechB
      (optimalProgramHistory .wantsC1)
      ((worldFrame .wantsC1).End_of () (.operate .down1) momentAfterTechB
        (optimalProgramHistory .wantsC1))
      ((worldFrame .wantsC1).End_of () (worldFrame .wantsC1).alpha_zero momentAfterTechB
        (optimalProgramHistory .wantsC1)) := by
    have hact_idle :
        (EconomyAction.idle : EconomyAction Unit CalcGood CalcTask) ∈
          momentAfterTechB.currentStage.menu () :=
      momentAfterTechB.currentStage.idle_mem ()
    have href_eq : (calcBehavior .wantsC1).referenceHistory () momentAfterTechB =
        optimalProgramHistory .wantsC1 := rfl
    have hsel_d1 :
        calcProgram.selectByBehavior (calcBehavior .wantsC1) () momentAfterTechB (.operate .down1)
            ((calcBehavior .wantsC1).referenceHistory () momentAfterTechB) =
          optimalProgramHistory .wantsC1 := by
      rw [href_eq]
      exact calcProgram.selectByBehavior_centered (calcBehavior .wantsC1) () momentAfterTechB
        (.operate .down1) (optimalProgramHistory .wantsC1) hmem henacted_at
    have hsel_idle :
        calcProgram.selectByBehavior (calcBehavior .wantsC1) () momentAfterTechB .idle
            ((calcBehavior .wantsC1).referenceHistory () momentAfterTechB) =
          .decision profileTechB
            (.decision ⟨fun _ => .idle, (calcStage1Choices profileTechB).idle_mem⟩ .halt) :=
      calcProgram_history_eq_of_mem_enacted profileTechB .idle
        ((calcStage1Choices profileTechB).idle_mem ()) _
        (calcProgram.selectByBehavior_memHist (calcBehavior .wantsC1) () momentAfterTechB .idle
          ((calcBehavior .wantsC1).referenceHistory () momentAfterTechB)
          ((calcBehavior .wantsC1).referenceHistory_mem () momentAfterTechB) hact_idle)
        (calcProgram.selectByBehavior_enacted (calcBehavior .wantsC1) () momentAfterTechB .idle
          ((calcBehavior .wantsC1).referenceHistory () momentAfterTechB)
          ((calcBehavior .wantsC1).referenceHistory_mem () momentAfterTechB) hact_idle)
    have hterm_d1 :
        (calcProgram.stateAt (calcProgram.expectedMaturation (calcBehavior .wantsC1) ()
            momentAfterTechB (.operate .down1)
            (calcProgram.selectByBehavior (calcBehavior .wantsC1) () momentAfterTechB
              (.operate .down1)
              ((calcBehavior .wantsC1).referenceHistory () momentAfterTechB)))).stock
          () .C1 = 1 := by
      rw [hsel_d1]
      dsimp [calcBehavior, FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
        calcBaseBehavior, FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory,
        FinitePhysicalEconomyProgram.expectedMaturation,
        FinitePhysicalEconomyProgram.horizonMoment,
        FinitePhysicalEconomyProgram.terminalSettlementHorizon,
        optimalProgramHistory, continueWithOptimal,
        FiniteEconomyProgram.ProgramHistory.terminalMoment,
        FinitePhysicalEconomyProgram.stateAt]
      exact downstream_advance_D1
    have hterm_idle :
        (calcProgram.stateAt (calcProgram.expectedMaturation (calcBehavior .wantsC1) ()
            momentAfterTechB .idle
            (calcProgram.selectByBehavior (calcBehavior .wantsC1) () momentAfterTechB
              .idle ((calcBehavior .wantsC1).referenceHistory () momentAfterTechB)))).stock
          () .C1 = 0 := by
      rw [hsel_idle]
      dsimp [calcBehavior, FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
        calcBaseBehavior, FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory,
        FinitePhysicalEconomyProgram.expectedMaturation,
        FinitePhysicalEconomyProgram.horizonMoment,
        FinitePhysicalEconomyProgram.terminalSettlementHorizon,
        FiniteEconomyProgram.ProgramHistory.terminalMoment,
        FinitePhysicalEconomyProgram.stateAt]
      exact downstream_idle_C1_zero
    change SubjectiveTeleologicalDominates finiteProgramEndRequirement (calcValuedEnd .wantsC1)
      (calcProgramEndBundle (calcProgram.intendedEnd (calcBehavior .wantsC1) ()
        momentAfterTechB (.operate .down1)))
      (calcProgramEndBundle (calcProgram.intendedEnd (calcBehavior .wantsC1) ()
        momentAfterTechB .idle))
    rw [worldStrictlyPrefers_iff_subjective_dominates]
    exact ⟨by
        simpa [worldGoal, FinitePhysicalEconomyProgram.intendedEnd,
          FinitePhysicalEconomyProgram.outcomeAt, calcProgramEndBundle] using
          Nat.le_of_eq hterm_d1.symm,
      by simpa [worldGoal, FinitePhysicalEconomyProgram.intendedEnd,
        FinitePhysicalEconomyProgram.outcomeAt, calcProgramEndBundle] using hterm_idle⟩
  refine ⟨hfeas, hexec, Or.inr hgain, ?_⟩
  intro (β : EconomyAction Unit CalcGood CalcTask) hβ hpref
  have hmem_menu : β ∈ (calcStage1Choices profileTechB).menu () :=
    ((worldFrame .wantsC1).A_feas_coupling () momentAfterTechB
      (optimalProgramHistory .wantsC1) β).1 hβ |>.1
  have hmenu_eq : (calcStage1Choices profileTechB).menu () = {.idle, .operate .down1} := by
    simp [calcStage1Choices, stage1Menu, profileTechB, stage0Profile]
  rw [hmenu_eq, Finset.mem_insert, Finset.mem_singleton] at hmem_menu
  rcases hmem_menu with rfl | rfl
  · exact (worldFrame .wantsC1).pref_asymm () momentAfterTechB
      (optimalProgramHistory .wantsC1) hgain hpref
  · exact (worldFrame .wantsC1).pref_asymm () momentAfterTechB
      (optimalProgramHistory .wantsC1) hpref hpref

/-- Purposeful downstream execution on the `wantsC2` branch (`down2` after `techA`). -/
theorem wantsC2_downstream_purposeful :
    @PurposefulAct (worldFrame .wantsC2) () momentAfterTechA
      (optimalProgramHistory .wantsC2) (.operate .down2) := by
  have hmem : (worldFrame .wantsC2).mem_hist momentAfterTechA (optimalProgramHistory .wantsC2) := by
    change ∃ hprofile : profileTechA = profileTechA,
      FiniteEconomyProgram.ProgramMoment.memHist _ .root
        (hprofile ▸ continueWithOptimal .wantsC2 profileTechA)
    exact ⟨rfl, FiniteEconomyProgram.ProgramMoment.root_memHist _⟩
  have henacted_at :
      FiniteEconomyProgram.ProgramHistory.enactedAt
        (optimalProgramHistory .wantsC2) momentAfterTechA () = .operate .down2 :=
    (calcProgram_enactedAt_afterProfile profileTechA
      (continueWithOptimal .wantsC2 profileTechA)).trans
      (by
        simp [continueWithOptimal, FinitePhysicalEconomyProgram.toFiniteEconomyProgram,
          FiniteEconomyProgram.physicalDecision, FiniteEconomyProgram.ProgramHistory.enactedAt,
          stage1DownstreamProfile, profileTechA, stage0Profile])
  have henacted : (worldFrame .wantsC2).enacted () momentAfterTechA
      (optimalProgramHistory .wantsC2) = .operate .down2 := henacted_at
  have hfeas : EconomyAction.operate .down2 ∈
      (worldFrame .wantsC2).A_feas () momentAfterTechA (optimalProgramHistory .wantsC2) := by
    rw [← henacted]
    exact (worldFrame .wantsC2).enacted_in_A_feas () momentAfterTechA
      (optimalProgramHistory .wantsC2) hmem
  have hexec : @Exec (worldFrame .wantsC2) () momentAfterTechA (.operate .down2)
      (optimalProgramHistory .wantsC2) := ⟨hmem, henacted⟩
  have hgain : (worldFrame .wantsC2).Preference () momentAfterTechA
      (optimalProgramHistory .wantsC2)
      ((worldFrame .wantsC2).End_of () (.operate .down2) momentAfterTechA
        (optimalProgramHistory .wantsC2))
      ((worldFrame .wantsC2).End_of () (worldFrame .wantsC2).alpha_zero momentAfterTechA
        (optimalProgramHistory .wantsC2)) := by
    have hact_idle :
        (EconomyAction.idle : EconomyAction Unit CalcGood CalcTask) ∈
          momentAfterTechA.currentStage.menu () :=
      momentAfterTechA.currentStage.idle_mem ()
    have href_eq : (calcBehavior .wantsC2).referenceHistory () momentAfterTechA =
        optimalProgramHistory .wantsC2 := rfl
    have hsel_d2 :
        calcProgram.selectByBehavior (calcBehavior .wantsC2) () momentAfterTechA (.operate .down2)
            ((calcBehavior .wantsC2).referenceHistory () momentAfterTechA) =
          optimalProgramHistory .wantsC2 := by
      rw [href_eq]
      exact calcProgram.selectByBehavior_centered (calcBehavior .wantsC2) () momentAfterTechA
        (.operate .down2) (optimalProgramHistory .wantsC2) hmem henacted_at
    have hsel_idle :
        calcProgram.selectByBehavior (calcBehavior .wantsC2) () momentAfterTechA .idle
            ((calcBehavior .wantsC2).referenceHistory () momentAfterTechA) =
          .decision profileTechA
            (.decision ⟨fun _ => .idle, (calcStage1Choices profileTechA).idle_mem⟩ .halt) :=
      calcProgram_history_eq_of_mem_enacted profileTechA .idle
        ((calcStage1Choices profileTechA).idle_mem ()) _
        (calcProgram.selectByBehavior_memHist (calcBehavior .wantsC2) () momentAfterTechA .idle
          ((calcBehavior .wantsC2).referenceHistory () momentAfterTechA)
          ((calcBehavior .wantsC2).referenceHistory_mem () momentAfterTechA) hact_idle)
        (calcProgram.selectByBehavior_enacted (calcBehavior .wantsC2) () momentAfterTechA .idle
          ((calcBehavior .wantsC2).referenceHistory () momentAfterTechA)
          ((calcBehavior .wantsC2).referenceHistory_mem () momentAfterTechA) hact_idle)
    have hterm_d2 :
        (calcProgram.stateAt (calcProgram.expectedMaturation (calcBehavior .wantsC2) ()
            momentAfterTechA (.operate .down2)
            (calcProgram.selectByBehavior (calcBehavior .wantsC2) () momentAfterTechA
              (.operate .down2)
              ((calcBehavior .wantsC2).referenceHistory () momentAfterTechA)))).stock
          () .C2 = 1 := by
      rw [hsel_d2]
      dsimp [calcBehavior, FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
        calcBaseBehavior, FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory,
        FinitePhysicalEconomyProgram.expectedMaturation,
        FinitePhysicalEconomyProgram.horizonMoment,
        FinitePhysicalEconomyProgram.terminalSettlementHorizon,
        optimalProgramHistory, continueWithOptimal,
        FiniteEconomyProgram.ProgramHistory.terminalMoment,
        FinitePhysicalEconomyProgram.stateAt]
      exact downstream_advance_D2
    have hterm_idle :
        (calcProgram.stateAt (calcProgram.expectedMaturation (calcBehavior .wantsC2) ()
            momentAfterTechA .idle
            (calcProgram.selectByBehavior (calcBehavior .wantsC2) () momentAfterTechA
              .idle ((calcBehavior .wantsC2).referenceHistory () momentAfterTechA)))).stock
          () .C2 = 0 := by
      rw [hsel_idle]
      dsimp [calcBehavior, FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
        calcBaseBehavior, FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory,
        FinitePhysicalEconomyProgram.expectedMaturation,
        FinitePhysicalEconomyProgram.horizonMoment,
        FinitePhysicalEconomyProgram.terminalSettlementHorizon,
        FiniteEconomyProgram.ProgramHistory.terminalMoment,
        FinitePhysicalEconomyProgram.stateAt]
      exact downstream_idle_C2_zero
    change SubjectiveTeleologicalDominates finiteProgramEndRequirement (calcValuedEnd .wantsC2)
      (calcProgramEndBundle (calcProgram.intendedEnd (calcBehavior .wantsC2) ()
        momentAfterTechA (.operate .down2)))
      (calcProgramEndBundle (calcProgram.intendedEnd (calcBehavior .wantsC2) ()
        momentAfterTechA .idle))
    rw [worldStrictlyPrefers_iff_subjective_dominates]
    exact ⟨by
        simpa [worldGoal, FinitePhysicalEconomyProgram.intendedEnd,
          FinitePhysicalEconomyProgram.outcomeAt, calcProgramEndBundle] using
          Nat.le_of_eq hterm_d2.symm,
      by simpa [worldGoal, FinitePhysicalEconomyProgram.intendedEnd,
        FinitePhysicalEconomyProgram.outcomeAt, calcProgramEndBundle] using hterm_idle⟩
  refine ⟨hfeas, hexec, Or.inr hgain, ?_⟩
  intro (β : EconomyAction Unit CalcGood CalcTask) hβ hpref
  have hmem_menu : β ∈ (calcStage1Choices profileTechA).menu () :=
    ((worldFrame .wantsC2).A_feas_coupling () momentAfterTechA
      (optimalProgramHistory .wantsC2) β).1 hβ |>.1
  have hmenu_eq : (calcStage1Choices profileTechA).menu () = {.idle, .operate .down2} := by
    simp [calcStage1Choices, stage1Menu, profileTechA, stage0Profile]
  rw [hmenu_eq, Finset.mem_insert, Finset.mem_singleton] at hmem_menu
  rcases hmem_menu with rfl | rfl
  · exact (worldFrame .wantsC2).pref_asymm () momentAfterTechA
      (optimalProgramHistory .wantsC2) hgain hpref
  · exact (worldFrame .wantsC2).pref_asymm () momentAfterTechA
      (optimalProgramHistory .wantsC2) hpref hpref

/-! ### Ground witness for `ActionFrameSocialistEconomy` in `Catallactics.lean` -/

def xAVec : InputVec 2 := ![2, 1]
def xBVec : InputVec 2 := ![1, 2]

def twoWorldChoiceStage : FiniteChoiceStage World CalcGood CalcTask where
  menu _ := {.idle}
  idle_mem _ := by simp
  activeAgents := ∅
  active_iff _ := by simp
  maxActiveAgents := 0
  activity_bound := by simp
  menu_wellFormed _ a ha := by
    simp only [Finset.mem_singleton] at ha
    subst a
    simp [EconomyAction.WellFormed]

def twoWorldPhysicalStage : FinitePhysicalChoiceStage World CalcGood CalcTask Unit where
  choices := twoWorldChoiceStage
  operations := sharedOps
  before := PhysicalState.zeroServices (fun _ => precommitmentLedger.production.publicStock)
  menu_affordable _ a ha _ := by
    simp only [twoWorldChoiceStage, Finset.mem_singleton] at ha
    subst a
    simp [rawActionUse]

def twoWorldEndBundle : FinitePhysicalChoiceEnd twoWorldChoiceStage → (CalcGood → ℕ)
  | .bundle b => b
  | .timed e _ => twoWorldEndBundle e
  | .quantity m q => fun m' => if m' = m then q else 0

noncomputable def twoWorldBehavior : FinitePhysicalChoiceBehavior twoWorldPhysicalStage where
  referenceHistory _ := ⟨fun _ => .idle, twoWorldChoiceStage.idle_mem⟩
  valuedEnd i _ _ e := e = .quantity (worldGoal i) 1
  valuedEnd_invariant _ _ _ _ _ _ _ := Iff.rfl
  preference i _ _ e₁ e₂ :=
    SubjectiveTeleologicalDominates finitePhysicalChoiceRequirement
      (fun e => e = .quantity (worldGoal i) 1)
      (twoWorldEndBundle e₁) (twoWorldEndBundle e₂)
  preference_invariant _ _ _ _ _ _ := rfl
  preference_asymmetric _ _ _ _ _ h₁ h₂ := by
    rcases h₁ with ⟨_, ⟨S, hval, hatt₁, hnatt₂⟩⟩
    exact hnatt₂ (h₂.1 S hval hatt₁)
  teleological_dominance_prefers _ _ _ b₁ b₂ h := h

@[instance_reducible] noncomputable def twoWorldActionFrame : ActionFrame :=
  twoWorldPhysicalStage.toActionFrame twoWorldBehavior

section

attribute [local instance] twoWorldActionFrame

theorem twoWorld_bundle_dominance (i : World) (b₁ b₂ : CalcGood → ℕ)
    (h : worldStrictlyPrefers i b₁ b₂) :
    twoWorldActionFrame.SubjectiveTeleologicalDominates i none
      ⟨fun _ => .idle, twoWorldChoiceStage.idle_mem⟩ b₁ b₂ := by
  rcases h with ⟨hb₁, hb₂⟩
  change SubjectiveTeleologicalDominates finitePhysicalChoiceRequirement
    (fun e => e = .quantity (worldGoal i) 1) b₁ b₂
  refine ⟨?_, ⟨{.quantity (worldGoal i) 1}, ?_, ?_, ?_⟩⟩
  · intro S hval hatt g
    have hsub : S ⊆ {.quantity (worldGoal i) 1} := fun e he => by
      simpa using hval e he
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
    · simp
    · exfalso
      have hbad := hatt (worldGoal i)
      simp [finitePhysicalChoiceRequirement, hb₂] at hbad
  · intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    rfl
  · intro g
    by_cases hg : g = worldGoal i
    · subst g
      simpa [finitePhysicalChoiceRequirement] using hb₁
    · simp [finitePhysicalChoiceRequirement, hg]
  · intro hatt
    have hbad := hatt (worldGoal i)
    simp [finitePhysicalChoiceRequirement, hb₂] at hbad

noncomputable def legacySocialistEconomy (w : World) :
    @ActionFrameSocialistEconomy twoWorldActionFrame w none
      ⟨fun _ => .idle, twoWorldChoiceStage.idle_mem⟩ where
  mA := .K1
  mB := .K2
  h_diff_means := by intro h; cases h
  eA := .bundle (afterDownstreamStock .B .D1)
  eB := .bundle (afterDownstreamStock .A .D2)
  h_diff_ends := by
    intro h
    have h1 := congrFun (FinitePhysicalChoiceEnd.bundle.inj h) .C1
    have hBD1 := terminal_outcomes_table.2.2.2.1
    have hAD2 := terminal_outcomes_table.2.1.1
    omega
  x_A := xAVec
  x_B := xBVec
  non_market_report := ![4, 4]
  bundle_A := afterDownstreamStock .B .D1
  bundle_B := afterDownstreamStock .A .D2
  h_end_A := rfl
  h_end_B := rfl
  prefers_A := match w with | .wantsC1 => true | .wantsC2 => false
  end_dominance := by
    rcases terminal_outcomes_table with ⟨_, ⟨hAD2_C1, hAD2_C2, _⟩, _, ⟨hBD1_C1, hBD1_C2, _⟩⟩
    cases w
    · exact twoWorld_bundle_dominance .wantsC1 _ _ ⟨by simp [worldGoal, hBD1_C1], hAD2_C1⟩
    · exact twoWorld_bundle_dominance .wantsC2 _ _ ⟨by simp [worldGoal, hAD2_C2], hBD1_C2⟩

theorem ground_action_frame_calculation_witness :
    PhysicalAntichain xAVec xBVec ∧
    ∀ (planner_rule : (InputVec 2 × InputVec 2 × (Fin 2 → ℕ)) → Bool),
      (let chosen1 := if planner_rule
          (@action_frame_non_market_observable twoWorldActionFrame
            .wantsC1 none _ (legacySocialistEconomy .wantsC1))
        then (legacySocialistEconomy .wantsC1).x_A else (legacySocialistEconomy .wantsC1).x_B
       @ViolatesActionFrameMengerianEconomizing twoWorldActionFrame
          .wantsC1 none _ (legacySocialistEconomy .wantsC1) chosen1) ∨
      (let chosen2 := if planner_rule
          (@action_frame_non_market_observable twoWorldActionFrame
            .wantsC2 none _ (legacySocialistEconomy .wantsC2))
        then (legacySocialistEconomy .wantsC2).x_A else (legacySocialistEconomy .wantsC2).x_B
       @ViolatesActionFrameMengerianEconomizing twoWorldActionFrame
          .wantsC2 none _ (legacySocialistEconomy .wantsC2) chosen2) := by
  have hanti : PhysicalAntichain xAVec xBVec :=
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  have hpresA : @ActionFramePreservedEnd twoWorldActionFrame .wantsC1 none _
      (legacySocialistEconomy .wantsC1) xAVec =
      (legacySocialistEconomy .wantsC1).eB := by
    simp [ActionFramePreservedEnd, xAVec]
  have hpresB : @ActionFramePreservedEnd twoWorldActionFrame .wantsC1 none _
      (legacySocialistEconomy .wantsC1) xBVec =
      (legacySocialistEconomy .wantsC1).eA := by
    simp [ActionFramePreservedEnd, xBVec]
  have hres := @action_frame_socialist_calculation_impossibility twoWorldActionFrame
    .wantsC1 .wantsC2 none none _ _
    (legacySocialistEconomy .wantsC1) (legacySocialistEconomy .wantsC2)
    ⟨rfl, rfl⟩ hanti rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hpresA hpresB
  exact ⟨hres.1, hres.2.2.2.2.2.2⟩

end

/-! ## 3. Labor-Voucher Accounting Interface -/

/-- Acyclic embodied-hour coefficients from factor preparation recipes. -/
def embodiedHours : CalcGood → ℕ
  | .K1 => 1
  | .K2 => 1
  | _ => 0

def laborCost (m : Method) : ℕ :=
  precommitmentLedger.production.laborHours (methodToTask m) +
    ∑ g : CalcGood, sharedOps.input (methodToTask m) g * embodiedHours g

theorem laborCost_A_eq_four : laborCost .A = 4 := by
  have hhrs := precommitment_laborHours .techA
  have hsum : (∑ g : CalcGood, sharedOps.input .techA g * embodiedHours g) = 3 := by
    decide
  simp [laborCost, methodToTask, hhrs, hsum]

theorem laborCost_B_eq_four : laborCost .B = 4 := by
  have hhrs := precommitment_laborHours .techB
  have hsum : (∑ g : CalcGood, sharedOps.input .techB g * embodiedHours g) = 3 := by
    decide
  simp [laborCost, methodToTask, hhrs, hsum]

theorem laborCost_equal : laborCost .A = laborCost .B := by
  rw [laborCost_A_eq_four, laborCost_B_eq_four]

/-- Public labor-voucher record available before commitment; downstream ordinal
appraisals are absent until after commitment. -/
structure VoucherRecord where
  stocks : CalcGood → ℕ
  recipeInputs : CalcTask → CalcGood → ℕ
  recipeOutputs : CalcTask → CalcGood → ℕ
  taskCapacities : CalcTask → ℕ
  sharedLaborCap : ℕ
  directHours : Method → ℕ
  factorEmbodiedHours : CalcGood → ℕ
  laborCharges : Method → ℕ
  certificateBalance : ℕ
  completedRedemptions : CalcGood → ℕ

/-- Concrete pre-commitment voucher observation, reading directly from the
executed pre-commitment work-and-redemption ledger. -/
def observeVoucher (_w : World) : VoucherRecord where
  stocks := precommitmentLedger.production.publicStock
  recipeInputs := sharedOps.input
  recipeOutputs := sharedOps.output
  taskCapacities := precommitmentLedger.production.capacity ()
  sharedLaborCap := sharedPostPrefixLaborCapacity
  directHours m := precommitmentLedger.production.laborHours (methodToTask m)
  factorEmbodiedHours := embodiedHours
  laborCharges := laborCost
  certificateBalance := precommitmentLedger.certificates.balance ()
  completedRedemptions := precommitmentLedger.certificates.consumed ()

def voucherProblem : InformationProblem World VoucherRecord Method :=
  ⟨observeVoucher, acceptable⟩

theorem voucher_records_equal :
    observeVoucher .wantsC1 = observeVoucher .wantsC2 := rfl

theorem voucher_accounting_cannot_always_economize :
    ¬ voucherProblem.Solvable :=
  unsolvable_of_world_blind observeVoucher voucher_records_equal

/-! ## 4. Input-Output and Administrative-Price Interface -/

def ioInputMatrix : CalcTask → CalcGood → ℕ := sharedOps.input
def ioOutputMatrix : CalcTask → CalcGood → ℕ := sharedOps.output

theorem io_material_constraints_satisfied (m : Method) :
    ∀ g : CalcGood,
      ioInputMatrix (methodToTask m) g ≤ precommitmentLedger.production.publicStock g ∧
      1 ≤ ioOutputMatrix (methodToTask m) .Q := by
  intro g
  refine ⟨?_, ?_⟩
  · exact (afterMethod_feasible m).2.2 g |> fun h => by
      simpa [ioInputMatrix, precommitment_input] using h
  · cases m <;> decide

/-- Pre-commitment common consumer transaction settled before private signal arrives. -/
def preSignalCommonSpot : SpotState :=
  (SpotState.mk 1 0 1 0).settle 1 1 true true

theorem preSignalCommonSpot_settled :
    preSignalCommonSpot.sellerStock = 0 ∧
    preSignalCommonSpot.buyerStock = 1 ∧
    preSignalCommonSpot.buyerCash = 0 ∧
    preSignalCommonSpot.sellerCash = 1 := by
  decide

/-- Public input-output and administrative-price record available before
commitment. -/
structure IORecord where
  inputMatrix : CalcTask → CalcGood → ℕ
  outputMatrix : CalcTask → CalcGood → ℕ
  availableStocks : CalcGood → ℕ
  sharedLaborCap : ℕ
  targetQ : ℕ
  adminQuotes : CalcGood → ℕ
  permittedCurrentOrders : CalcGood → ℕ
  completedReceipt : SpotState

def defaultAdminQuotes : CalcGood → ℕ
  | .K1 => 1
  | .K2 => 1
  | _ => 0

def observeIO (_w : World) : IORecord where
  inputMatrix := ioInputMatrix
  outputMatrix := ioOutputMatrix
  availableStocks := precommitmentLedger.production.publicStock
  sharedLaborCap := sharedPostPrefixLaborCapacity
  targetQ := 1
  adminQuotes := defaultAdminQuotes
  permittedCurrentOrders _ := 0
  completedReceipt := preSignalCommonSpot

def ioProblem : InformationProblem World IORecord Method :=
  ⟨observeIO, acceptable⟩

theorem io_records_equal :
    observeIO .wantsC1 = observeIO .wantsC2 := rfl

theorem io_accounting_cannot_always_economize :
    ¬ ioProblem.Solvable :=
  unsolvable_of_world_blind observeIO io_records_equal

/-! ## 5. Multi-Round Transcript Induction, Zero-Queue Example, and Cone Witness -/

/-- Finite-horizon algorithmic transcript over an initial record and a
permitted-reply interface. -/
def transcript {R Reply : Type} (step : R → Reply → R) (initial : World → R)
    (permittedReply : World → R → Reply) : ℕ → World → R
  | 0, w => initial w
  | n + 1, w =>
      step (transcript step initial permittedReply n w)
        (permittedReply w (transcript step initial permittedReply n w))

theorem transcript_eq_of_initial_eq {R Reply : Type}
    (step : R → Reply → R) (initial : World → R)
    (permittedReply : World → R → Reply)
    (h_init : initial .wantsC1 = initial .wantsC2)
    (h_reply : ∀ r, permittedReply .wantsC1 r = permittedReply .wantsC2 r) :
    ∀ n, transcript step initial permittedReply n .wantsC1 =
      transcript step initial permittedReply n .wantsC2 := by
  intro n
  induction n with
  | zero => exact h_init
  | succ k ih =>
      dsimp [transcript]
      rw [ih, h_reply (transcript step initial permittedReply k .wantsC2)]

theorem transcript_cannot_always_economize {R Reply : Type}
    (step : R → Reply → R) (initial : World → R)
    (permittedReply : World → R → Reply)
    (h_init : initial .wantsC1 = initial .wantsC2)
    (h_reply : ∀ r, permittedReply .wantsC1 r = permittedReply .wantsC2 r) (n : ℕ) :
    ¬ (InformationProblem.mk (transcript step initial permittedReply n) acceptable).Solvable :=
  unsolvable_of_world_blind _
    (transcript_eq_of_initial_eq step initial permittedReply h_init h_reply n)

/-- Posted current-round capital order book is empty during pre-commitment quote
rounds (future capital-use requests are not yet admissible), distinct from the
positive physical reserves (`K1 = 2`, `K2 = 2`). -/
def precommitmentPostedOrderSupply (_ : CalcGood) : ℕ := 0
def precommitmentAdmissibleDemand (_ : CalcGood) : ℕ := 0

def toAdministeredPriceState (initialQuotes : CalcGood → ℕ) :
    AdministeredPriceState CalcGood where
  price := initialQuotes
  stock := precommitmentPostedOrderSupply

theorem precommitment_queue_clears (initialQuotes : CalcGood → ℕ) :
    (toAdministeredPriceState initialQuotes).clear precommitmentAdmissibleDemand := by
  intro g
  rfl

theorem precommitment_zero_queue_leaves_quotes_unchanged
    (initialQuotes : CalcGood → ℕ) (ceiling : ℕ) :
    ((toAdministeredPriceState initialQuotes).adjust ceiling
      precommitmentAdmissibleDemand).price = initialQuotes :=
  (toAdministeredPriceState initialQuotes).balanced_price_stays ceiling
    precommitmentAdmissibleDemand (precommitment_queue_clears initialQuotes)

theorem precommitment_zero_queue_cannot_always_economize
    (initialQuotes : CalcGood → ℕ) (ceiling : ℕ) :
    ¬ (InformationProblem.mk
      (fun _ : World =>
        ((toAdministeredPriceState initialQuotes).adjust ceiling
          precommitmentAdmissibleDemand).price)
      acceptable).Solvable :=
  unsolvable_of_world_blind _ rfl

/-- Explicit `InIndeterminacyCone` witness showing price vectors `(1, 3)` and
`(3, 1)` reverse the cost ranking of `(2, 1)` and `(1, 2)`. -/
theorem methods_form_physical_antichain : PhysicalAntichain xAVec xBVec :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

theorem methods_in_indeterminacy_cone :
    InIndeterminacyCone 2 ![1, 1] ![3, 3] xAVec xBVec := by
  refine indeterminacy_cone_criterion 2 ![1, 1] ![3, 3] xAVec xBVec ![1, 3] ![3, 1]
    ?_ ?_ ?_ ?_
  · intro r; fin_cases r <;> decide
  · intro r; fin_cases r <;> decide
  · have hA : Cost 2 ![1, 3] xAVec = 5 := by decide
    have hB : Cost 2 ![1, 3] xBVec = 7 := by decide
    omega
  · have hA : Cost 2 ![3, 1] xAVec = 7 := by decide
    have hB : Cost 2 ![3, 1] xBVec = 5 := by decide
    omega

/-! ## 6. Controls and Exact Antichain Equivalence Corollary -/

/-- Parameterized two-factor bottleneck family over arbitrary input requirements
`xA xB : InputVec 2`, with scarce factor endowment `max (xA r) (xB r)` and
downstream unit bottleneck requirements for factor `0` (`wantsC1`) and
factor `1` (`wantsC2`). -/
def paramEndowment (xA xB : InputVec 2) (r : Fin 2) : ℕ :=
  max (xA r) (xB r)

def paramResidual (xA xB : InputVec 2) (m : Method) (r : Fin 2) : ℕ :=
  paramEndowment xA xB r - (match m with | .A => xA r | .B => xB r)

def paramWorldCoord : World → Fin 2
  | .wantsC1 => 0
  | .wantsC2 => 1

def paramAttainsGoal (xA xB : InputVec 2) (w : World) (m : Method) : Prop :=
  1 ≤ paramResidual xA xB m (paramWorldCoord w)

/-- Both methods remain initially feasible (`x ≤ max x y`) and produce the same
stipulated target `Q`. Acceptability means no method leaves a strictly preferred
downstream attainment profile in world `w`. -/
def acceptableParam (xA xB : InputVec 2) (w : World) (m : Method) : Prop :=
  ∀ m' : Method, ¬ (paramAttainsGoal xA xB w m' ∧ ¬ paramAttainsGoal xA xB w m)

theorem paramAttainsGoal_A_iff (xA xB : InputVec 2) (w : World) :
    paramAttainsGoal xA xB w .A ↔ xA (paramWorldCoord w) < xB (paramWorldCoord w) := by
  simp [paramAttainsGoal, paramResidual, paramEndowment]
  omega

theorem paramAttainsGoal_B_iff (xA xB : InputVec 2) (w : World) :
    paramAttainsGoal xA xB w .B ↔ xB (paramWorldCoord w) < xA (paramWorldCoord w) := by
  simp [paramAttainsGoal, paramResidual, paramEndowment]
  omega

theorem acceptableParam_A_iff (xA xB : InputVec 2) (w : World) :
    acceptableParam xA xB w .A ↔ xA (paramWorldCoord w) ≤ xB (paramWorldCoord w) := by
  constructor
  · intro h
    by_contra hlt
    have hgt : xB (paramWorldCoord w) < xA (paramWorldCoord w) := Nat.lt_of_not_le hlt
    apply h .B
    exact ⟨(paramAttainsGoal_B_iff xA xB w).mpr hgt,
      fun ha => Nat.not_lt_of_le (Nat.le_of_lt hgt) ((paramAttainsGoal_A_iff xA xB w).mp ha)⟩
  · intro hle m' ⟨hm', hnotA⟩
    cases m'
    · exact hnotA hm'
    · have hlt := (paramAttainsGoal_B_iff xA xB w).mp hm'
      omega

theorem acceptableParam_B_iff (xA xB : InputVec 2) (w : World) :
    acceptableParam xA xB w .B ↔ xB (paramWorldCoord w) ≤ xA (paramWorldCoord w) := by
  constructor
  · intro h
    by_contra hlt
    have hgt : xA (paramWorldCoord w) < xB (paramWorldCoord w) := Nat.lt_of_not_le hlt
    apply h .A
    exact ⟨(paramAttainsGoal_A_iff xA xB w).mpr hgt,
      fun hb => Nat.not_lt_of_le (Nat.le_of_lt hgt) ((paramAttainsGoal_B_iff xA xB w).mp hb)⟩
  · intro hle m' ⟨hm', hnotB⟩
    cases m'
    · have hlt := (paramAttainsGoal_A_iff xA xB w).mp hm'
      omega
    · exact hnotB hm'

/-- Control 1 (Physical dominance): when `A` uses no more of either factor than
`B` (`PhysLE xA xB`), `A` preserves every downstream end available after `B` and
constant `Method.A` succeeds for every observation map. -/
theorem control_physical_dominance {Record : Type} (xA xB : InputVec 2)
    (obs : World → Record) (h_dom : PhysLE xA xB) :
    (InformationProblem.mk obs (acceptableParam xA xB)).Solvable := by
  refine ⟨fun _ => .A, fun w => ?_⟩
  dsimp
  rw [acceptableParam_A_iff]
  exact h_dom (paramWorldCoord w)

/-- Control 2 (Reverse dominance and ties): when `B` uses no more of either
factor than `A` (`PhysLE xB xA`, including ties `xA = xB`), constant `Method.B`
succeeds. -/
theorem control_reverse_dominance_and_tie {Record : Type} (xA xB : InputVec 2)
    (obs : World → Record) (h_dom : PhysLE xB xA) :
    (InformationProblem.mk obs (acceptableParam xA xB)).Solvable := by
  refine ⟨fun _ => .B, fun w => ?_⟩
  dsimp
  rw [acceptableParam_B_iff]
  exact h_dom (paramWorldCoord w)

/-- Control 3 (Single factor): when input requirements lie in a single factor
(`Fin 1 → ℕ`), inputs are linearly ordered; selecting the smaller requirement
succeeds, and agrees with labor-only selection when labor charges are strictly
monotone in that factor. -/
theorem control_single_factor (xA xB : InputVec 1)
    (laborCharge : Method → ℕ) (baseHours unitHours : ℕ) (hpos : 0 < unitHours)
    (hA : laborCharge .A = baseHours + xA 0 * unitHours)
    (hB : laborCharge .B = baseHours + xB 0 * unitHours) :
    (let chosen : Method := if laborCharge .A ≤ laborCharge .B then .A else .B
     (chosen = .A → xA 0 ≤ xB 0) ∧ (chosen = .B → xB 0 ≤ xA 0)) := by
  by_cases hle : laborCharge .A ≤ laborCharge .B
  · simp only [hle, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    rw [hA, hB] at hle
    exact Nat.le_of_mul_le_mul_right (by omega) hpos
  · simp only [hle, ↓reduceIte]
    refine ⟨fun h => (by cases h), fun _ => ?_⟩
    rw [hA, hB] at hle
    have hlt : xB 0 * unitHours < xA 0 * unitHours := by omega
    exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right hlt)

/-- Control 4 (Successful antichain): keeping the antichain `(2, 1)` vs `(1, 2)`
while restricting states to share the same downstream appraisal (`wantsC1`) allows
constant `Method.B` to succeed. -/
theorem control_successful_antichain :
    PhysicalAntichain xAVec xBVec ∧
    (InformationProblem.mk (fun _ : Unit => observeVoucher .wantsC1)
      (fun _ => acceptable .wantsC1)).Solvable :=
  ⟨methods_form_physical_antichain,
    ⟨fun _ => .B, fun _ => (acceptable_wantsC1_iff .B).mpr rfl⟩⟩

/-- Control 5 (Distinguishing report): adding the pre-commitment downstream
appraisal bit restores solvability for the shared economy. -/
def observeVoucherWithReport (w : World) : VoucherRecord × World :=
  (observeVoucher w, w)

theorem control_distinguishing_report :
    (InformationProblem.mk observeVoucherWithReport acceptable).Solvable := by
  refine ⟨fun ⟨_, w⟩ => match w with | .wantsC1 => .B | .wantsC2 => .A, ?_⟩
  intro w
  cases w
  · exact (acceptable_wantsC1_iff .B).mpr rfl
  · exact (acceptable_wantsC2_iff .A).mpr rfl

/-- Control 6 (Full information): supplying the full world state succeeds. -/
theorem control_full_information :
    (InformationProblem.mk id acceptable).Solvable :=
  InformationProblem.full_information_control acceptable exists_acceptable

/-- Exact antichain necessity and sufficiency within the parameterized
two-factor bottleneck family: a physical antichain holds if and only if
the two downstream worlds admit no common acceptable method. -/
theorem antichain_iff_param_conflict (xA xB : InputVec 2) :
    PhysicalAntichain xA xB ↔
      ∀ m, ¬ (acceptableParam xA xB .wantsC1 m ∧ acceptableParam xA xB .wantsC2 m) := by
  constructor
  · rintro hanti (⟨⟩ | ⟨⟩) ⟨h1, h2⟩
    · rw [acceptableParam_A_iff] at h1 h2
      exact (antichain_incomparable xA xB hanti).1 (fun r => by fin_cases r <;> assumption)
    · rw [acceptableParam_B_iff] at h1 h2
      exact (antichain_incomparable xA xB hanti).2 (fun r => by fin_cases r <;> assumption)
  · intro hno
    have hnotA : ¬ (xA 0 ≤ xB 0 ∧ xA 1 ≤ xB 1) := by
      rintro ⟨h0, h1⟩
      exact hno .A ⟨(acceptableParam_A_iff xA xB .wantsC1).mpr h0,
        (acceptableParam_A_iff xA xB .wantsC2).mpr h1⟩
    have hnotB : ¬ (xB 0 ≤ xA 0 ∧ xB 1 ≤ xA 1) := by
      rintro ⟨h0, h1⟩
      exact hno .B ⟨(acceptableParam_B_iff xA xB .wantsC1).mpr h0,
        (acceptableParam_B_iff xA xB .wantsC2).mpr h1⟩
    have ha : ∃ a : Fin 2, xB a < xA a := by
      by_cases h0 : xA 0 ≤ xB 0
      · exact ⟨1, Nat.lt_of_not_le (fun h1 => hnotA ⟨h0, h1⟩)⟩
      · exact ⟨0, Nat.lt_of_not_le h0⟩
    have hb : ∃ b : Fin 2, xA b < xB b := by
      by_cases h0 : xB 0 ≤ xA 0
      · exact ⟨1, Nat.lt_of_not_le (fun h1 => hnotB ⟨h0, h1⟩)⟩
      · exact ⟨0, Nat.lt_of_not_le h0⟩
    exact ⟨ha, hb⟩

/-- Under any record that equates `wantsC1` and `wantsC2`, unsolvability in the
two-factor bottleneck family is equivalent to `PhysicalAntichain xA xB`. -/
theorem param_unsolvable_iff_antichain_of_blind_obs {Record : Type}
    (xA xB : InputVec 2) (obs : World → Record)
    (h_same : obs .wantsC1 = obs .wantsC2) :
    ¬ (InformationProblem.mk obs (acceptableParam xA xB)).Solvable ↔
      PhysicalAntichain xA xB := by
  constructor
  · intro hunsolv
    by_contra hnot
    have hcomp : PhysLE xA xB ∨ PhysLE xB xA := by
      by_cases hle : PhysLE xA xB
      · exact Or.inl hle
      · right
        by_contra hge
        apply hnot
        have ha : ∃ a : Fin 2, xB a < xA a := by
          by_cases h0 : xA 0 ≤ xB 0
          · exact ⟨1, Nat.lt_of_not_le (fun h1 => hle (fun r => by fin_cases r <;> assumption))⟩
          · exact ⟨0, Nat.lt_of_not_le h0⟩
        have hb : ∃ b : Fin 2, xA b < xB b := by
          by_cases h0 : xB 0 ≤ xA 0
          · exact ⟨1, Nat.lt_of_not_le (fun h1 => hge (fun r => by fin_cases r <;> assumption))⟩
          · exact ⟨0, Nat.lt_of_not_le h0⟩
        exact ⟨ha, hb⟩
    rcases hcomp with hle | hge
    · exact hunsolv (control_physical_dominance xA xB obs hle)
    · exact hunsolv (control_reverse_dominance_and_tie xA xB obs hge)
  · intro hanti
    exact InformationProblem.unsolvable_of_conflicting_states _ .wantsC1 .wantsC2 h_same
      ((antichain_iff_param_conflict xA xB).mp hanti)

end Institutions
end EconomicCalculation
end Praxeology

end
