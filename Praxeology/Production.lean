/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action

/-!
# Production: Inventory Accounting and Operational Traces

Shared inventory accounting for production and exchange transitions in an
ActionFrame.
-/

@[expose] public section

namespace Praxeology

/-- Action-level service yields used to account for flows along a run. -/
structure ServiceAccounting (W : ActionFrame) (Service : Type) where
  yield_service : W.Action → Service → ℕ
  yield_service_alpha_zero : ∀ s, yield_service W.alpha_zero s = 0

variable [W : ActionFrame]

def projectedStock (W : ActionFrame) (i : W.Agent) (α : W.Action)
    (t : W.Moment) (h' : W.History) : W.Means → ℕ :=
  let t' := W.tau i t h'
  W.omega i (W.ExpectedMaturation i α t' (W.sigma i t' α h')) (W.sigma i t' α h')


inductive InventoryStep (W : ActionFrame) (i : W.Agent) (h : W.History) :
    W.Moment → W.Moment → Type where
  | production {t t'} (α : W.Action)
      (h_exec : W.enacted i t h = α)
      (h_nontrade : ¬ W.IsTradeAction α)
      (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
      InventoryStep W i h t t'
  | matchedOffer {t t'} (j : W.Agent) (qA : ℕ) (mA : W.Means) (qB : ℕ) (mB : W.Means)
      (h_agents : i ≠ j)
      (h_offer : W.enacted i t h = W.Offer i j qA mA qB mB)
      (h_accept : W.enacted j t h = W.Accept j i qA mA qB mB)
      (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
      InventoryStep W i h t t'
  | matchedAccept {t t'} (j : W.Agent) (qA : ℕ) (mA : W.Means) (qB : ℕ) (mB : W.Means)
      (h_agents : j ≠ i)
      (h_accept : W.enacted i t h = W.Accept i j qA mA qB mB)
      (h_offer : W.enacted j t h = W.Offer j i qA mA qB mB)
      (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
      InventoryStep W i h t t'
  | unmatchedOffer {t t'} (j : W.Agent) (qA : ℕ) (mA : W.Means) (qB : ℕ) (mB : W.Means)
      (h_offer : W.enacted i t h = W.Offer i j qA mA qB mB)
      (h_not_accept : W.enacted j t h ≠ W.Accept j i qA mA qB mB)
      (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
      InventoryStep W i h t t'
  | unmatchedAccept {t t'} (j : W.Agent) (qA : ℕ) (mA : W.Means) (qB : ℕ) (mB : W.Means)
      (h_accept : W.enacted i t h = W.Accept i j qA mA qB mB)
      (h_not_offer : W.enacted j t h ≠ W.Offer j i qA mA qB mB)
      (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
      InventoryStep W i h t t'

/-- The action whose physical flow is recorded by an inventory step. -/
def InventoryStep.action {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t t' : W.Moment} (s : InventoryStep W i h t t') : W.Action :=
  match s with
  | .production α _ _ _ => α
  | .matchedOffer j qA mA qB mB _ _ _ _ => W.Offer i j qA mA qB mB
  | .matchedAccept j qA mA qB mB _ _ _ _ => W.Accept i j qA mA qB mB
  | .unmatchedOffer j qA mA qB mB _ _ _ => W.Offer i j qA mA qB mB
  | .unmatchedAccept j qA mA qB mB _ _ _ => W.Accept i j qA mA qB mB


def InventoryStep.effectiveUse {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t t' : W.Moment} (s : InventoryStep W i h t t') (m : W.Means) : ℕ :=
  match s with
  | .production α _ _ _ => W.use_means α m
  | .matchedOffer _ _ _ _ _ _ _ _ _ => W.use_means s.action m
  | .matchedAccept _ _ _ _ _ _ _ _ _ => W.use_means s.action m
  | .unmatchedOffer _ _ _ _ _ _ _ _ => 0
  | .unmatchedAccept _ _ _ _ _ _ _ _ => 0

/-- Physical output attributed to a step. -/
def InventoryStep.effectiveYield {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t t' : W.Moment} (s : InventoryStep W i h t t') (m : W.Means) : ℕ :=
  match s with
  | .production α _ _ _ => W.yield_means α m
  | .matchedOffer _ _ _ _ _ _ _ _ _ => W.yield_means s.action m
  | .matchedAccept _ _ _ _ _ _ _ _ _ => W.yield_means s.action m
  | .unmatchedOffer _ _ _ _ _ _ _ _ => 0
  | .unmatchedAccept _ _ _ _ _ _ _ _ => 0

/-- Physical yield from a production step. -/
def InventoryStep.productionYield {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t t' : W.Moment} (s : InventoryStep W i h t t') (m : W.Means) : ℕ :=
  match s with
  | .production α _ _ _ => W.yield_means α m
  | .matchedOffer _ _ _ _ _ _ _ _ _ => 0
  | .matchedAccept _ _ _ _ _ _ _ _ _ => 0
  | .unmatchedOffer _ _ _ _ _ _ _ _ => 0
  | .unmatchedAccept _ _ _ _ _ _ _ _ => 0

/-- Physical yield from a matched transfer step. -/
def InventoryStep.tradeYield {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t t' : W.Moment} (s : InventoryStep W i h t t') (m : W.Means) : ℕ :=
  match s with
  | .production _ _ _ _ => 0
  | .matchedOffer _ _ _ _ _ _ _ _ _ => W.yield_means s.action m
  | .matchedAccept _ _ _ _ _ _ _ _ _ => W.yield_means s.action m
  | .unmatchedOffer _ _ _ _ _ _ _ _ => 0
  | .unmatchedAccept _ _ _ _ _ _ _ _ => 0

/-- Every effective yield is classified as production output or a matched transfer receipt. -/
theorem InventoryStep.effectiveYield_eq_production_add_trade
    {i : Agent} {h : History} {t t' : Moment}
    (s : InventoryStep W i h t t') (m : W.Means) :
    s.effectiveYield m = s.productionYield m + s.tradeYield m := by
  cases s <;>
    simp [InventoryStep.effectiveYield, InventoryStep.productionYield,
      InventoryStep.tradeYield, InventoryStep.action]

/-- A finite sequence of actual physical transitions along one history. -/
inductive InventoryRun (W : ActionFrame) (i : W.Agent) (h : W.History) :
    W.Moment → W.Moment → Type where
  | done (t : W.Moment) : InventoryRun W i h t t
  | step {t u v : W.Moment}
      (head : InventoryStep W i h t u)
      (tail : InventoryRun W i h u v) :
      InventoryRun W i h t v

/-- Concatenate two adjacent transition runs on one history. -/
def InventoryRun.append {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u v : W.Moment} (first : InventoryRun W i h t u)
    (second : InventoryRun W i h u v) : InventoryRun W i h t v :=
  match first with
  | .done _ => second
  | .step head tail => .step head (tail.append second)

/-- Number of transitions in a finite inventory run. -/
def InventoryRun.length {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (run : InventoryRun W i h t u) : ℕ :=
  match run with
  | .done _ => 0
  | .step _ tail => tail.length + 1

/-- Sum of the physical inputs used by each step in the run. -/
def InventoryRun.totalUse {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (r : InventoryRun W i h t u) (m : W.Means) : ℕ :=
  match r with
  | .done _ => 0
  | .step head tail => head.effectiveUse m + tail.totalUse m

/-- Inputs add across concatenated runs. -/
theorem InventoryRun.totalUse_append {i : Agent} {h : History}
    {t u v : Moment} (first : InventoryRun W i h t u)
    (second : InventoryRun W i h u v) (m : Means) :
    (first.append second).totalUse m = first.totalUse m + second.totalUse m := by
  induction first with
  | done _ => simp [InventoryRun.append, InventoryRun.totalUse]
  | @step t u v head tail ih =>
      simp [InventoryRun.append, InventoryRun.totalUse, ih, Nat.add_assoc]

/-- Total physical outputs generated by an actual run. -/
def InventoryRun.totalYield {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (r : InventoryRun W i h t u) (m : W.Means) : ℕ :=
  match r with
  | .done _ => 0
  | .step head tail => head.effectiveYield m + tail.totalYield m

/-- Outputs add across concatenated runs. -/
theorem InventoryRun.totalYield_append {i : Agent} {h : History}
    {t u v : Moment} (first : InventoryRun W i h t u)
    (second : InventoryRun W i h u v) (m : Means) :
    (first.append second).totalYield m = first.totalYield m + second.totalYield m := by
  induction first with
  | done _ => simp [InventoryRun.append, InventoryRun.totalYield]
  | @step t u v head tail ih =>
      simp [InventoryRun.append, InventoryRun.totalYield, ih, Nat.add_assoc]

/-- Cumulative production output, excluding goods received in exchange. -/
def InventoryRun.totalProductionYield {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (r : InventoryRun W i h t u) (m : W.Means) : ℕ :=
  match r with
  | .done _ => 0
  | .step head tail => head.productionYield m + tail.totalProductionYield m

/-- Cumulative goods received through matched trade, excluding physical production. -/
def InventoryRun.totalTradeYield {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (r : InventoryRun W i h t u) (m : W.Means) : ℕ :=
  match r with
  | .done _ => 0
  | .step head tail => head.tradeYield m + tail.totalTradeYield m


def InventoryStep.IsMatchedOfferAt {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t t' : W.Moment} (step : InventoryStep W i h t t')
    (moment : W.Moment) (buyer : W.Agent) (qA : ℕ) (mA : W.Means)
    (qB : ℕ) (mB : W.Means) : Prop :=
  match step with
  | .matchedOffer j qA' mA' qB' mB' _ _ _ _ =>
      t = moment ∧ j = buyer ∧ qA' = qA ∧ mA' = mA ∧ qB' = qB ∧ mB' = mB
  | _ => False

/-- Whether this step is the matched acceptance at `moment` with the listed partner
and quantities. -/
def InventoryStep.IsMatchedAcceptAt {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t t' : W.Moment} (step : InventoryStep W i h t t')
    (moment : W.Moment) (operator : W.Agent) (qA : ℕ) (mA : W.Means)
    (qB : ℕ) (mB : W.Means) : Prop :=
  match step with
  | .matchedAccept j qA' mA' qB' mB' _ _ _ _ =>
      t = moment ∧ j = operator ∧ qA' = qA ∧ mA' = mA ∧ qB' = qB ∧ mB' = mB
  | _ => False

/-- A production step at the named moment performs the specified nontrade production action. -/
def InventoryStep.IsProductionAt {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t t' : W.Moment} (step : InventoryStep W i h t t')
    (moment : W.Moment) (action : W.Action) : Prop :=
  match step with
  | .production α _ _ _ => t = moment ∧ α = action
  | _ => False


def InventoryRun.containsMatchedOfferAt {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (run : InventoryRun W i h t u)
    (moment : W.Moment) (buyer : W.Agent) (qA : ℕ) (mA : W.Means)
    (qB : ℕ) (mB : W.Means) : Prop :=
  match run with
  | .done _ => False
  | .step head tail =>
      head.IsMatchedOfferAt moment buyer qA mA qB mB ∨
        tail.containsMatchedOfferAt moment buyer qA mA qB mB

/-- The run contains a matched acceptance with the listed values. -/
def InventoryRun.containsMatchedAcceptAt {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (run : InventoryRun W i h t u)
    (moment : W.Moment) (operator : W.Agent) (qA : ℕ) (mA : W.Means)
    (qB : ℕ) (mB : W.Means) : Prop :=
  match run with
  | .done _ => False
  | .step head tail =>
      head.IsMatchedAcceptAt moment operator qA mA qB mB ∨
        tail.containsMatchedAcceptAt moment operator qA mA qB mB

/-- The finite run contains the named nontrade production action. -/
def InventoryRun.containsProductionAt {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (run : InventoryRun W i h t u)
    (moment : W.Moment) (action : W.Action) : Prop :=
  match run with
  | .done _ => False
  | .step head tail =>
      head.IsProductionAt moment action ∨ tail.containsProductionAt moment action


def InventoryRun.containsActionAt {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} (run : InventoryRun W i h t u)
    (moment : W.Moment) (action : W.Action) : Prop :=
  match run with
  | .done _ => False
  | @InventoryRun.step _ _ _ start _ _ head tail =>
      (start = moment ∧ head.action = action) ∨ tail.containsActionAt moment action

/-- Total yield is the sum of production yield and matched-transfer yield. -/
theorem InventoryRun.totalYield_eq_production_add_trade
    {i : Agent} {h : History} {t u : Moment}
    (r : InventoryRun W i h t u) (m : W.Means) :
    r.totalYield m = r.totalProductionYield m + r.totalTradeYield m := by
  induction r with
  | done _ => rfl
  | @step t v u head tail ih =>
      rw [InventoryRun.totalYield, InventoryRun.totalProductionYield,
        InventoryRun.totalTradeYield,
        head.effectiveYield_eq_production_add_trade, ih]
      omega

/-- Sum of externally specified service output for each step in the run. -/
def InventoryRun.totalService {W : ActionFrame} {i : W.Agent} {h : W.History}
    {t u : W.Moment} {Service : Type} (r : InventoryRun W i h t u)
    (A : ServiceAccounting W Service) (s : Service) : ℕ :=
  match r with
  | .done _ => 0
  | .step head tail => A.yield_service head.action s + tail.totalService A s

/-- A run with no transitions has no service output. -/
theorem InventoryRun.totalService_done {i : W.Agent} {h : W.History}
    (t : W.Moment) {Service : Type} (A : ServiceAccounting W Service) (s : Service) :
    (@InventoryRun.done W i h t).totalService A s = 0 := rfl

/-- The head action's service yield adds to the tail run's service total. -/
theorem InventoryRun.totalService_step {i : W.Agent} {h : W.History}
    {t u v : W.Moment} (head : InventoryStep W i h t u)
    (tail : InventoryRun W i h u v) {Service : Type}
    (A : ServiceAccounting W Service) (s : Service) :
    (InventoryRun.step head tail).totalService A s =
      A.yield_service head.action s + tail.totalService A s := rfl

/-- A passive action contributes no service to a run. -/
theorem InventoryRun.totalService_step_alpha_zero {i : W.Agent}
    {h : W.History} {t u v : W.Moment} (head : InventoryStep W i h t u)
    (tail : InventoryRun W i h u v) {Service : Type}
    (A : ServiceAccounting W Service) (s : Service)
    (h_action : head.action = W.alpha_zero) :
    (InventoryRun.step head tail).totalService A s = tail.totalService A s := by
  rw [InventoryRun.totalService_step, h_action, A.yield_service_alpha_zero, Nat.zero_add]

/-- Service output adds across concatenated runs. -/
theorem InventoryRun.totalService_append {i : Agent} {h : History} {Service : Type}
    {t u v : Moment} (first : InventoryRun W i h t u)
    (second : InventoryRun W i h u v) (A : ServiceAccounting W Service) (s : Service) :
    (first.append second).totalService A s =
      first.totalService A s + second.totalService A s := by
  induction first with
  | done _ => simp [InventoryRun.append, InventoryRun.totalService]
  | @step t u v head tail ih =>
      simp [InventoryRun.append, InventoryRun.totalService, ih, Nat.add_assoc]


theorem InventoryRun.inventory_balance {i : Agent} {h : History}
    {t u : Moment} (r : InventoryRun W i h t u) (m : Means) :
    W.omega i u h m + r.totalUse m = W.omega i t h m + r.totalYield m := by
  induction r with
  | done t => simp [InventoryRun.totalUse, InventoryRun.totalYield]
  | @step t v u head tail ih =>
      have hstep : W.omega i v h m + head.effectiveUse m =
          W.omega i t h m + head.effectiveYield m := by
        cases head with
        | production α h_exec h_nontrade h_next =>
            exact W.law_in_re_transition i t v h α m h_nontrade h_exec h_next
        | matchedOffer j qA mA qB mB h_agents h_offer h_accept h_next =>
            have htransfer := (W.bilateral_transfer_law i j qA mA qB mB t v h m
              h_agents h_offer h_accept h_next).1
            change W.omega i v h m + W.use_means (W.Offer i j qA mA qB mB) m =
              W.omega i t h m + W.yield_means (W.Offer i j qA mA qB mB) m
            rw [W.use_means_offer, W.yield_means_offer]
            exact htransfer
        | matchedAccept j qA mA qB mB h_agents h_accept h_offer h_next =>
            have htransfer := (W.bilateral_transfer_law j i qA mA qB mB t v h m
              h_agents h_offer h_accept h_next).2
            change W.omega i v h m + W.use_means (W.Accept i j qA mA qB mB) m =
              W.omega i t h m + W.yield_means (W.Accept i j qA mA qB mB) m
            rw [W.use_means_accept, W.yield_means_accept]
            exact htransfer
        | unmatchedOffer j qA mA qB mB h_offer h_not_accept h_next =>
            have hstable := W.unilateral_offer_noop i j qA mA qB mB t v h m
              h_offer h_not_accept h_next
            simp [InventoryStep.effectiveUse,
              InventoryStep.effectiveYield, hstable]
        | unmatchedAccept j qA mA qB mB h_accept h_not_offer h_next =>
            have hstable := W.unilateral_accept_noop i j qA mA qB mB t v h m
              h_accept h_not_offer h_next
            simp [InventoryStep.effectiveUse,
              InventoryStep.effectiveYield, hstable]
      simp only [InventoryRun.totalUse, InventoryRun.totalYield]
      omega

/-- One observed transition obeys the same physical inventory balance as a
one-step `InventoryRun`. -/
theorem InventoryStep.inventory_balance {i : Agent} {h : History}
    {t t' : Moment} (s : InventoryStep W i h t t') (m : Means) :
    W.omega i t' h m + s.effectiveUse m =
      W.omega i t h m + s.effectiveYield m := by
  have hbalance := (InventoryRun.step s (.done t')).inventory_balance m
  simpa [InventoryRun.totalUse, InventoryRun.totalYield] using hbalance


structure ProjectedInventoryTrace (W : ActionFrame) (i : W.Agent) (α : W.Action)
    (t : W.Moment) (h' : W.History) (hh' : h' ∈ W.MinPlausible i t) where
  projected_node_incident : W.mem_hist (W.tau i t h') h' :=
    W.min_plausible_node_incidence i t h' hh'
  projected_feasible : α ∈ W.A_feas i (W.tau i t h') h'
  run : InventoryRun W i (W.sigma i (W.tau i t h') α h')
    (W.tau i t h')
    (W.ExpectedMaturation i α (W.tau i t h')
      (W.sigma i (W.tau i t h') α h'))

/-- The action-selected history enacts the feasible action at its projected node. -/
theorem ProjectedInventoryTrace.selected_action_realized
    {i : Agent} {α : Action} {t : Moment} {h' : History}
    {hh' : h' ∈ W.MinPlausible i t}
    (R : ProjectedInventoryTrace W i α t h' hh') :
    W.enacted i (W.tau i t h') (W.sigma i (W.tau i t h') α h') = α := by
  exact (W.projected_sigma_enacted i t h' α hh' R.projected_feasible).2

/-- Inventory at the projected decision node, before the traced transitions occur. -/
def projectedInitialStock (W : ActionFrame) (i : W.Agent) (α : W.Action)
    (t : W.Moment) (h' : W.History) (m : W.Means) : ℕ :=
  W.omega i (W.tau i t h') (W.sigma i (W.tau i t h') α h') m


theorem ProjectedInventoryTrace.common_initial_stock
    {i : Agent} {α β : Action} {t : Moment} {h' : History}
    {hh' : h' ∈ W.MinPlausible i t}
    (Rα : ProjectedInventoryTrace W i α t h' hh')
    (Rβ : ProjectedInventoryTrace W i β t h' hh') (m : Means) :
    projectedInitialStock W i α t h' m = projectedInitialStock W i β t h' m := by
  have hα := W.projected_sigma_enacted i t h' α hh' Rα.projected_feasible
  have hβ := W.projected_sigma_enacted i t h' β hh' Rβ.projected_feasible
  have hstock := W.omega_bundle_invariant i (W.tau i t h') m hα.1 hβ.1
  simpa [projectedInitialStock] using hstock

/-- An inventory trace is represented by an additive balance, without computing
a truncated subtraction. -/
def ProjectedInventoryTrace.StockBalance {W : ActionFrame} {i : W.Agent} {α : W.Action}
    {t : W.Moment} {h' : W.History} {hh' : h' ∈ W.MinPlausible i t}
    (R : ProjectedInventoryTrace W i α t h' hh') (stock : W.Means → ℕ) : Prop :=
  ∀ m, stock m + R.run.totalUse m =
    projectedInitialStock W i α t h' m + R.run.totalYield m

/-- The projected inventory satisfies the exact additive trace balance. -/
theorem ProjectedInventoryTrace.projectedStock_balance
    {i : Agent} {α : Action} {t : Moment} {h' : History}
    {hh' : h' ∈ W.MinPlausible i t}
    (R : ProjectedInventoryTrace W i α t h' hh') :
    R.StockBalance (projectedStock W i α t h') := by
  intro m
  exact R.run.inventory_balance m

/-- A trace balance determines the inventory function uniquely. -/
theorem ProjectedInventoryTrace.stockBalance_unique
    {i : Agent} {α : Action} {t : Moment} {h' : History}
    {hh' : h' ∈ W.MinPlausible i t}
    (R : ProjectedInventoryTrace W i α t h' hh')
    {stock₁ stock₂ : W.Means → ℕ}
    (h₁ : R.StockBalance stock₁) (h₂ : R.StockBalance stock₂) :
    stock₁ = stock₂ := by
  funext m
  have h₁m := h₁ m
  have h₂m := h₂ m
  omega

/-- The additive balance characterizes the projected stock exactly. -/
theorem ProjectedInventoryTrace.stockBalance_iff
    {i : Agent} {α : Action} {t : Moment} {h' : History}
    {hh' : h' ∈ W.MinPlausible i t}
    (R : ProjectedInventoryTrace W i α t h' hh') (stock : W.Means → ℕ) :
    R.StockBalance stock ↔ stock = projectedStock W i α t h' := by
  constructor
  · intro hstock
    exact R.stockBalance_unique hstock R.projectedStock_balance
  · rintro rfl
    exact R.projectedStock_balance


/-- Total externally accounted service flow along a projected trace. -/
def ProjectedInventoryTrace.totalService {W : ActionFrame} {i : W.Agent}
    {α : W.Action} {t : W.Moment} {h' : W.History} {hh' : h' ∈ W.MinPlausible i t}
    {Service : Type} (R : ProjectedInventoryTrace W i α t h' hh')
    (A : ServiceAccounting W Service) (s : Service) : ℕ :=
  R.run.totalService A s


-- Section 3: Lockean Property, Homesteading, and Path-Dependent Title Traces


section LockeanPropertyAndTitleTraces

/-- Agent `i`'s physical stock of every means is weakly preserved from `t` to `t'`. -/
def StockPreserved (i : Agent) (t t' : Moment) (h : History) : Prop :=
  ∀ m : Means, omega i t h m ≤ omega i t' h m

/-- Agent `i`'s physical stock of `m` is strictly contracted from `t` to `t'`. -/
def StockContractedAt (i : Agent) (t t' : Moment) (h : History)
    (m : Means) : Prop :=
  omega i t' h m < omega i t h m

/-- Every action resource-feasible at `t` remains resource-feasible at `t'`. -/
def ResourceMenuPreserved (i : Agent) (t t' : Moment) (h : History) : Prop :=
  ∀ α : Action, (∀ m, use_means α m ≤ omega i t h m) →
    (∀ m, use_means α m ≤ omega i t' h m)

/-- Feasible menu `A_feas` is strictly contracted when an action feasible at `t`
becomes infeasible at `t'` despite remaining contemplated. -/
def FeasibleMenuStripped (i : Agent) (t t' : Moment) (h : History)
    (α : Action) : Prop :=
  α ∈ A_feas i t h ∧ α ∈ A_cont i t' h ∧ α ∉ A_feas i t' h

theorem stockPreserved_implies_resourceMenuPreserved
    (i : Agent) (t t' : Moment) (h : History)
    (h_pres : StockPreserved i t t' h) :
    ResourceMenuPreserved i t t' h := by
  intro α hα m
  exact le_trans (hα m) (h_pres m)

theorem stockPreserved_implies_no_feasibleMenuStripped
    (i : Agent) (t t' : Moment) (h : History)
    (h_pres : StockPreserved i t t' h) (α : Action) :
    ¬ FeasibleMenuStripped i t t' h α := by
  intro ⟨h_feas_t, h_cont_t', h_not_feas_t'⟩
  apply h_not_feas_t'
  rw [W.A_feas_coupling]
  refine ⟨h_cont_t', ?_⟩
  have h_res := (W.A_feas_coupling i t h α).mp h_feas_t |>.2
  exact stockPreserved_implies_resourceMenuPreserved i t t' h h_pres α h_res

theorem stockContractedAt_strips_tight_action
    (i : Agent) (t t' : Moment) (h : History)
    (m : Means) (α : Action)
    (h_contract : StockContractedAt i t t' h m)
    (h_feas : α ∈ A_feas i t h)
    (h_cont : α ∈ A_cont i t' h)
    (h_tight : use_means α m = omega i t h m) :
    FeasibleMenuStripped i t t' h α := by
  refine ⟨h_feas, h_cont, ?_⟩
  intro h_feas'
  have h_le := (W.A_feas_coupling i t' h α).mp h_feas' |>.2 m
  dsimp [StockContractedAt, use_means, omega] at *
  omega

/-- A pure Lockean homesteading action for means `m` uses zero units of `m`
and yields a positive quantity of `m`. -/
def IsLockeanHomesteading (α : Action) (m : Means) : Prop :=
  ¬ W.IsTradeAction α ∧ use_means α m = 0 ∧ 0 < yield_means α m

/-- A purposeful Lockean homesteading action is an enacted purposeful action
that is non-trade, uses zero units of means `m`, and yields a positive quantity of `m`. -/
def PurposefulLockeanHomesteading (i : Agent) (t : Moment) (h : History)
    (α : Action) (m : Means) : Prop :=
  PurposefulAct i t h α ∧ IsLockeanHomesteading α m

/-- Lockean homesteading by `i` strictly increases `i`'s stock of `m` while leaving
every passive bystander `j`'s stock and resource-feasible menu completely intact. -/
theorem lockean_homesteading_non_invasive
    {i j : Agent} {t t' : Moment} {h : History} {α : Action} {m : Means}
    (h_homestead : IsLockeanHomesteading α m)
    (h_exec_i : enacted i t h = α)
    (h_passive_j : enacted j t h = α₀)
    (h_next : IsNextMoment Precedence W.mem_hist t t' h) :
    omega i t h m < omega i t' h m ∧
    (∀ m', omega j t' h m' = omega j t h m') ∧
    ResourceMenuPreserved j t t' h := by
  have h_trans_i := W.law_in_re_transition i t t' h α m h_homestead.1 h_exec_i h_next
  have h_u : W.use_means α m = 0 := h_homestead.2.1
  have h_y : 0 < W.yield_means α m := h_homestead.2.2
  have h_strict_i : omega i t h m < omega i t' h m := by
    dsimp [omega, use_means, yield_means] at *
    omega
  have h_not_trade_0 : ¬ W.IsTradeAction α₀ := alpha_zero_not_trade
  have h_stock_j : ∀ m', omega j t' h m' = omega j t h m' := by
    intro m'
    have h_trans_j :=
      W.law_in_re_transition j t t' h α₀ m' h_not_trade_0 h_passive_j h_next
    have h_u0 := W.use_means_alpha_zero m'
    have h_y0 := W.yield_means_alpha_zero m'
    rw [h_u0, h_y0, Nat.add_zero, Nat.add_zero] at h_trans_j
    exact h_trans_j
  have h_pres_j : StockPreserved j t t' h := fun m' => by rw [h_stock_j m']
  exact ⟨h_strict_i, h_stock_j, stockPreserved_implies_resourceMenuPreserved j t t' h h_pres_j⟩

/-- Purposeful Lockean homesteading strictly improves `i`'s position over inertia,
strictly expands `i`'s physical stock, and leaves every passive bystander's
stock and feasible action menu unstripped. -/
theorem purposeful_lockean_homesteading_non_invasive
    {i j : Agent} {t t' : Moment} {h : History} {α : Action} {m : Means}
    (h_home : PurposefulLockeanHomesteading i t h α m)
    (h_passive_j : enacted j t h = α₀)
    (h_next : IsNextMoment Precedence W.mem_hist t t' h) :
    Preference i t h (End_of i α t h) (End_of i α₀ t h) ∧
    omega i t h m < omega i t' h m ∧
    (∀ m', omega j t' h m' = omega j t h m') ∧
    ResourceMenuPreserved j t t' h ∧
    ∀ γ, ¬ FeasibleMenuStripped j t t' h γ := by
  obtain ⟨h_purp, h_homestead⟩ := h_home
  have h_exec_i : enacted i t h = α := h_purp.2.1.2
  have h_ne_a0 : α ≠ α₀ := by
    rintro rfl
    have h_y0 := W.yield_means_alpha_zero m
    have h_pos := h_homestead.2.2
    dsimp [yield_means] at h_pos
    rw [h_y0] at h_pos
    exact Nat.lt_irrefl 0 h_pos
  have h_pref : Preference i t h (End_of i α t h) (End_of i α₀ t h) := by
    rcases h_purp.2.2.1 with rfl | h_p
    · contradiction
    · exact h_p
  obtain ⟨h_gain_i, h_stock_j, h_menu_j⟩ :=
    lockean_homesteading_non_invasive h_homestead h_exec_i h_passive_j h_next
  have h_pres_j : StockPreserved j t t' h := fun m' => by rw [h_stock_j m']
  refine ⟨h_pref, h_gain_i, h_stock_j, h_menu_j, ?_⟩
  intro γ
  exact stockPreserved_implies_no_feasibleMenuStripped j t t' h h_pres_j γ

/-- Simultaneous / Unowned Resource Edge Case:
When an unappropriated resource `m` is unowned at `t` (`omega i t h m = 0` and `omega j t h m = 0`),
any contemplated action `β` of `j` requiring `m` (`use_means β m > 0`) is already infeasible for `j`
at `t`. When agent `i` appropriates `m` via Lockean homesteading from `t` to `t'`, `j`'s stock and
feasible menu are uncontracted. Property protection attaches to `i` only at `t'`. -/
theorem unowned_resource_contemplation_not_feasible_and_first_appropriation_non_invasive
    {i j : Agent} {t t' : Moment} {h : History} {α β : Action} {m : Means}
    (h_unowned_j : omega j t h m = 0)
    (h_req_β : 0 < use_means β m)
    (h_homestead_i : IsLockeanHomesteading α m)
    (h_exec_i : enacted i t h = α)
    (h_passive_j : enacted j t h = α₀)
    (h_next : IsNextMoment Precedence W.mem_hist t t' h) :
    β ∉ A_feas j t h ∧
    omega i t h m < omega i t' h m ∧
    StockPreserved j t t' h ∧
    ResourceMenuPreserved j t t' h ∧
    ∀ γ, ¬ FeasibleMenuStripped j t t' h γ := by
  have h_infeas_β : β ∉ A_feas j t h := by
    intro h_feas
    have h_le := (W.A_feas_coupling j t h β).mp h_feas |>.2 m
    dsimp [omega, use_means] at *
    omega
  obtain ⟨h_gain_i, h_stock_j, h_menu_j⟩ :=
    lockean_homesteading_non_invasive h_homestead_i h_exec_i h_passive_j h_next
  have h_pres_j : StockPreserved j t t' h := fun m' => by rw [h_stock_j m']
  refine ⟨h_infeas_β, h_gain_i, h_pres_j, h_menu_j, ?_⟩
  intro γ
  exact stockPreserved_implies_no_feasibleMenuStripped j t t' h h_pres_j γ

end LockeanPropertyAndTitleTraces

section PropertyLedgerTraces

/-- Naive, single-moment reduction test: classifies any decrease in present physical
possession (`omega`) between moments `t` and `t'` as an invasion. -/
def IsPresentMomentReduction (a : W.Agent) (t t' : W.Moment) (h : W.History) (m : W.Means) : Prop :=
  W.omega a t' h m < W.omega a t h m

/-- Path-dependent clean title invasion test: an invasion occurs when an agent's clean title
is violated or when clean-title-backed possession is non-consensually reduced below title. -/
def IsPathDependentTitleInvasion (title : W.Agent → W.Means → ℕ)
    (a : W.Agent) (t t' : W.Moment) (h : W.History) (m : W.Means) : Prop :=
  W.omega a t' h m < title a m ∧ W.omega a t' h m < W.omega a t h m

/-- The Thief-and-Baker Theorem:
In a two-step operational trace where a thief seizes flour from a baker at t0 -> t1,
and the baker recovers it at t1 -> t2 without the thief's consent:
1. The naive present-moment test misclassifies the baker's recovery as an invasion of the thief.
2. The path-dependent test correctly classifies the theft (t0 -> t1) as an invasion of the baker,
   and the baker's recovery (t1 -> t2) as non-invasive restitution. -/
theorem baker_recovery_restitution_not_path_dependent_invasion
    (baker thief : W.Agent) (flour : W.Means) (q : ℕ)
    (_h_ne : thief ≠ baker)
    (t0 t1 t2 : W.Moment) (h : W.History)
    (title : W.Agent → W.Means → ℕ)
    (h_clean0 : ∀ a m, W.omega a t0 h m = title a m)
    (h_avail0 : q ≤ W.omega baker t0 h flour)
    (h_s1_baker : W.omega baker t1 h flour = W.omega baker t0 h flour - q)
    (h_s1_thief : W.omega thief t1 h flour = W.omega thief t0 h flour + q)
    (h_s2_thief : W.omega thief t2 h flour = W.omega thief t1 h flour - q)
    (h_s2_baker : W.omega baker t2 h flour = W.omega baker t1 h flour + q) :
    (0 < q → IsPathDependentTitleInvasion title baker t0 t1 h flour) ∧
    (0 < q → IsPresentMomentReduction thief t1 t2 h flour) ∧
    ¬ IsPathDependentTitleInvasion title thief t1 t2 h flour ∧
    W.omega baker t2 h flour = title baker flour := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h_pos_q
    dsimp [IsPathDependentTitleInvasion]
    have h_title_eq : title baker flour = W.omega baker t0 h flour := by
      rw [← h_clean0 baker flour]
    rw [h_s1_baker, h_title_eq]
    exact ⟨Nat.sub_lt_self h_pos_q h_avail0, Nat.sub_lt_self h_pos_q h_avail0⟩
  · intro h_pos_q
    dsimp [IsPresentMomentReduction]
    rw [h_s2_thief, h_s1_thief]
    omega
  · dsimp [IsPathDependentTitleInvasion]
    intro ⟨h_lt_title, _⟩
    have h_thief_title : title thief flour = W.omega thief t0 h flour := by
      rw [← h_clean0 thief flour]
    rw [h_thief_title, h_s2_thief, h_s1_thief] at h_lt_title
    omega
  · rw [h_s2_baker, h_s1_baker]
    have h_baker_clean : title baker flour = W.omega baker t0 h flour := by
      rw [← h_clean0 baker flour]
    rw [h_baker_clean]
    omega

end PropertyLedgerTraces

end Praxeology
