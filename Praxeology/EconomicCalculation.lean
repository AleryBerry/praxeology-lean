/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
-/
module

public import Praxeology.FiniteEconomy.Physical
public import Mathlib.Data.Fintype.Basic

/-!
# Economic calculation: observations, strategic reports, and institutional ledgers

The information theorem below is deliberately independent of any economic
institution. An application must derive its observation function and its
acceptable decisions from a specified institution. The protocol interfaces
then permit arbitrary private types and reports; they contain no field saying
that reports are truthful or that an outcome is efficient.
-/

@[expose] public section

namespace Praxeology
namespace EconomicCalculation

/-- A decision problem with a real state, an observation, and an independently
specified criterion for a decision to be acceptable in that state. -/
structure InformationProblem (State Record Decision : Type) where
  observe : State → Record
  acceptable : State → Decision → Prop

namespace InformationProblem

variable {State Record Decision : Type}

/-- A rule sees only the record. -/
def Solvable (P : InformationProblem State Record Decision) : Prop :=
  ∃ rule : Record → Decision, ∀ s, P.acceptable s (rule (P.observe s))

/-- The exact information condition: each record must admit one decision that
works for *every* state producing that record. No ownership assumption enters
this elementary theorem. -/
theorem solvable_iff_common_decision [Inhabited Decision]
    (P : InformationProblem State Record Decision) :
    P.Solvable ↔
      ∀ r, (∃ s, P.observe s = r) →
        ∃ d, ∀ s, P.observe s = r → P.acceptable s d := by
  classical
  constructor
  · rintro ⟨rule, hrule⟩ r ⟨s, hs⟩
    refine ⟨rule r, ?_⟩
    intro x hx
    rw [← hx]
    exact hrule x
  · intro h
    let rule : Record → Decision := fun r =>
      if hr : ∃ s, P.observe s = r then (h r hr).choose else default
    refine ⟨rule, ?_⟩
    intro s
    have hr : ∃ x, P.observe x = P.observe s := ⟨s, rfl⟩
    change P.acceptable s (if hr' : ∃ x, P.observe x = P.observe s then
      (h (P.observe s) hr').choose else default)
    simp only [hr, ↓reduceDIte]
    exact (h (P.observe s) hr).choose_spec s rfl

/-- Equal records alone cause no obstruction. The acceptable-decision sets
must also be disjoint; this is the burden of an economic application. -/
theorem unsolvable_of_conflicting_states
    (P : InformationProblem State Record Decision)
    (s t : State) (same : P.observe s = P.observe t)
    (conflict : ∀ d, ¬ (P.acceptable s d ∧ P.acceptable t d)) :
    ¬ P.Solvable := by
  rintro ⟨rule, hrule⟩
  apply conflict (rule (P.observe s))
  constructor
  · exact hrule s
  · rw [same]
    exact hrule t

/-- Supplying the full state as the record succeeds exactly when each state
has some acceptable decision. This control shows the role of observation. -/
theorem full_information_control [Inhabited Decision]
    (acceptable : State → Decision → Prop)
    (h : ∀ s, ∃ d, acceptable s d) :
    (InformationProblem.mk id acceptable).Solvable := by
  classical
  exact ⟨fun s => (h s).choose, fun s => (h s).choose_spec⟩

end InformationProblem

/-- A one-round institution. The instruction receives reports, while the
physical executor receives the true private profile. This type signature
keeps hidden facts out of the instruction function. -/
structure ReportingProtocol (Agent : Type) where
  Private : Agent → Type
  View : Agent → Type
  currentView : ∀ i, View i
  Report : Agent → Type
  Instruction : Type
  Outcome : Type
  instruct : (∀ i, Report i) → Instruction
  execute : (∀ i, Private i) → Instruction → Outcome
  feasible : (∀ i, Private i) → Outcome → Prop
  weaklyPrefers : (∀ i, Private i) → Agent → Outcome → Outcome → Prop
  weaklyPrefers_refl : ∀ types i x, weaklyPrefers types i x x
  weaklyPrefers_trans : ∀ types i x y z,
    weaklyPrefers types i x y → weaklyPrefers types i y z →
      weaklyPrefers types i x z

namespace ReportingProtocol

variable {Agent : Type} (P : ReportingProtocol Agent)

/-- Every type may choose any admissible report as a function of its own
private information and observed local history. -/
abbrev Strategy := ∀ i, P.Private i → P.View i → P.Report i

def reports (types : ∀ i, P.Private i) (s : P.Strategy) : ∀ i, P.Report i :=
  fun i => s i (types i) (P.currentView i)

def result (types : ∀ i, P.Private i) (s : P.Strategy) : P.Outcome :=
  P.execute types (P.instruct (P.reports types s))

def replace [DecidableEq Agent] (reports : ∀ i, P.Report i)
    (i : Agent) (alternative : P.Report i) : ∀ j, P.Report j := by
  intro j
  by_cases h : j = i
  · subst j
    exact alternative
  · exact reports j

/-- A profitable unilateral report deviation is checked at every true type
profile; no probability distribution or cardinal utility is involved. -/
def ExPostEquilibrium [DecidableEq Agent] (s : P.Strategy) : Prop :=
  ∀ types i alternative,
    P.weaklyPrefers types i (P.result types s)
      (P.execute types (P.instruct (P.replace (P.reports types s) i alternative)))

/-- The proposed truthful report is supplied separately and compared with
every unilateral alternative, holding every other report fixed. -/
def TruthfulDominant [DecidableEq Agent]
    (reveal : ∀ i, P.Private i → P.Report i) : Prop :=
  ∀ types (otherReports : ∀ i, P.Report i) i alternative,
    P.weaklyPrefers types i
      (P.execute types (P.instruct (P.replace otherReports i (reveal i (types i)))))
      (P.execute types (P.instruct (P.replace otherReports i alternative)))

def truthfulStrategy
    (reveal : ∀ i, P.Private i → P.Report i) : P.Strategy :=
  fun i priv _view => reveal i priv

/-- Dominant truthful reporting supplies an ex-post equilibrium. Efficiency
requires a separate theorem about the executed outcome. -/
theorem truthful_equilibrium_of_dominance [DecidableEq Agent]
    (reveal : ∀ i, P.Private i → P.Report i)
    (h : P.TruthfulDominant reveal) :
    P.ExPostEquilibrium (P.truthfulStrategy reveal) := by
  intro types i alternative
  have h_same : P.replace (P.reports types (P.truthfulStrategy reveal)) i
      (reveal i (types i)) = P.reports types (P.truthfulStrategy reveal) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [replace, reports, truthfulStrategy]
    · simp [replace, hji]
  have h_dominant := h types (P.reports types (P.truthfulStrategy reveal)) i alternative
  rw [h_same] at h_dominant
  exact h_dominant

def StrictlyPrefers (types : ∀ i, P.Private i) (i : Agent)
    (x y : P.Outcome) : Prop :=
  P.weaklyPrefers types i x y ∧ ¬ P.weaklyPrefers types i y x

/-- Efficiency is evaluated against physical possibilities in the common
economy, including possibilities an institution legally excludes. -/
def ParetoEfficient (types : ∀ i, P.Private i) (x : P.Outcome) : Prop :=
  P.feasible types x ∧
    ¬ ∃ y, P.feasible types y ∧
      (∀ i, P.weaklyPrefers types i y x) ∧
      (∃ i, P.StrictlyPrefers types i y x)

/-- Existence is part of the claim: a mechanism with no equilibrium does not
pass vacuously. -/
def FullyImplementsPareto [DecidableEq Agent] : Prop :=
  (∃ s : P.Strategy, P.ExPostEquilibrium s) ∧
    ∀ s : P.Strategy, P.ExPostEquilibrium s →
      ∀ types, P.ParetoEfficient types (P.result types s)

theorem implementation_requires_equilibrium [DecidableEq Agent]
    (h : P.FullyImplementsPareto) :
    ∃ s : P.Strategy, P.ExPostEquilibrium s := h.1

/-- An unverified report is payoff-insensitive when changing agent `i`'s report
leaves agent `i` indifferent among all resulting outcomes. -/
def ReportPayoffInsensitive [DecidableEq Agent] : Prop :=
  ∀ types (reports : ∀ i, P.Report i) i (r₁ r₂ : P.Report i),
    P.weaklyPrefers types i
      (P.execute types (P.instruct (P.replace reports i r₁)))
      (P.execute types (P.instruct (P.replace reports i r₂)))

/-- Every agent sends a fixed type-independent report. -/
def constantStrategy (constReport : ∀ i, P.Report i) : P.Strategy :=
  fun i _ _ => constReport i

/-- When pre-commitment reports do not affect an agent's personal outcome,
every type-independent babbling profile is an ex-post equilibrium. -/
theorem babbling_equilibrium_of_payoff_insensitive [DecidableEq Agent]
    (constReport : ∀ i, P.Report i) (h : P.ReportPayoffInsensitive) :
    P.ExPostEquilibrium (P.constantStrategy constReport) := by
  intro types i alternative
  have h_same :
      P.replace (P.reports types (P.constantStrategy constReport)) i (constReport i) =
        P.reports types (P.constantStrategy constReport) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [replace, reports, constantStrategy]
    · simp [replace, hji]
  have h_flat := h types (P.reports types (P.constantStrategy constReport)) i
    (constReport i) alternative
  rw [h_same] at h_flat
  exact h_flat

/-- When reports are payoff-insensitive, truthful reporting is never strictly
preferred to an arbitrary alternative report. -/
theorem not_strictly_prefers_truth_of_payoff_insensitive [DecidableEq Agent]
    (reveal : ∀ i, P.Private i → P.Report i)
    (h : P.ReportPayoffInsensitive)
    (types : ∀ i, P.Private i) (otherReports : ∀ i, P.Report i)
    (i : Agent) (alternative : P.Report i) :
    ¬ P.StrictlyPrefers types i
      (P.execute types (P.instruct (P.replace otherReports i (reveal i (types i)))))
      (P.execute types (P.instruct (P.replace otherReports i alternative))) := by
  intro hstrict
  exact hstrict.2 (h types otherReports i alternative (reveal i (types i)))

end ReportingProtocol

/-- Physical consumption and labor remain comparable across institutions.
Nominal certificate and cash balances are kept in the institutional ledgers,
not silently added into a common cardinal welfare sum. -/
structure RealOutcome (Person Good : Type) where
  consumed : Person → Good → ℕ
  laborHours : Person → ℕ
  residualStock : Good → ℕ

/-- State ownership remains operational: only an authorized task can use a
public input, and its output returns to the public stock. The manager's
private capacity limits execution, whatever capacity was reported. -/
structure PublicProduction (Manager Good Task : Type) where
  publicStock : Good → ℕ
  capacity : Manager → Task → ℕ
  input : Task → Good → ℕ
  output : Task → Good → ℕ
  laborHours : Task → ℕ
  authorized : Manager → Task → Prop

namespace PublicProduction

variable {Manager Good Task : Type}

def CanExecute (E : PublicProduction Manager Good Task)
    (manager : Manager) (task : Task) (runs : ℕ) : Prop :=
  E.authorized manager task ∧
  runs ≤ E.capacity manager task ∧
  ∀ good, runs * E.input task good ≤ E.publicStock good

/-- An expanded task menu, capacity, or stock preserves the feasibility of
old operations when their input recipes are unchanged. This says nothing
about whether the new opportunities are discovered or selected. -/
theorem canExecute_after_progress
    (old new : PublicProduction Manager Good Task)
    (hAuthorized : ∀ manager task, old.authorized manager task →
      new.authorized manager task)
    (hCapacity : ∀ manager task,
      old.capacity manager task ≤ new.capacity manager task)
    (hInput : ∀ task good, new.input task good = old.input task good)
    (hStock : ∀ good, old.publicStock good ≤ new.publicStock good)
    (manager : Manager) (task : Task) (runs : ℕ)
    (h : old.CanExecute manager task runs) :
    new.CanExecute manager task runs := by
  rcases h with ⟨ha, hc, hs⟩
  refine ⟨hAuthorized manager task ha,
    le_trans hc (hCapacity manager task), ?_⟩
  intro good
  rw [hInput task good]
  exact le_trans (hs good) (hStock good)

/-- The executable transition checks the actual capacity and public stock;
reports cannot change either. The input and output quantities are physical. -/
def execute [DecidableEq Good] [Fintype Good] [DecidableEq Task]
    (E : PublicProduction Manager Good Task)
    (manager : Manager) (task : Task) (runs : ℕ)
    [Decidable (E.CanExecute manager task runs)] : Good → ℕ :=
  if E.CanExecute manager task runs then
    fun good => E.publicStock good - runs * E.input task good +
      runs * E.output task good
  else E.publicStock

/-- Labor time required by a feasible run. Feasibility is not execution. -/
def potentialHours (E : PublicProduction Manager Good Task)
    (manager : Manager) (task : Task) (runs : ℕ)
    [Decidable (E.CanExecute manager task runs)] : ℕ :=
  if E.CanExecute manager task runs then runs * E.laborHours task else 0

theorem rejected_run_has_no_potential_hours
    (E : PublicProduction Manager Good Task)
    (manager : Manager) (task : Task) (runs : ℕ)
    [Decidable (E.CanExecute manager task runs)]
    (h : ¬ E.CanExecute manager task runs) :
    E.potentialHours manager task runs = 0 := by
  simp [potentialHours, h]

theorem rejected_execution_preserves_stock
    [DecidableEq Good] [Fintype Good] [DecidableEq Task]
    (E : PublicProduction Manager Good Task)
    (manager : Manager) (task : Task) (runs : ℕ)
    [Decidable (E.CanExecute manager task runs)]
    (h : ¬ E.CanExecute manager task runs) :
    E.execute manager task runs = E.publicStock := by
  simp [execute, h]

end PublicProduction

/-- Certificate balances are personal. A redemption burns certificates and
delivers existing goods; no transfer between persons is defined. -/
structure CertificateState (Person Good : Type) where
  balance : Person → ℕ
  stock : Good → ℕ
  consumed : Person → Good → ℕ

namespace CertificateState

variable {Person Good : Type} [DecidableEq Person]

/-- The deduction is applied to verified work, with overlarge deductions
clamped by natural subtraction. Issuance records do not certify work by
themselves; callers must provide the physical observation. -/
def issue (S : CertificateState Person Good)
    (person : Person) (verifiedHours deduction : ℕ) :
    CertificateState Person Good :=
  { S with
    balance := Function.update S.balance person
      (S.balance person + (verifiedHours - deduction)) }

theorem issue_other (S : CertificateState Person Good) (person other : Person)
    (verifiedHours deduction : ℕ) (h : other ≠ person) :
    (S.issue person verifiedHours deduction).balance other = S.balance other := by
  simp [issue, Function.update_of_ne h]

theorem issue_records_verified_net_hours
    (S : CertificateState Person Good) (person : Person)
    (verifiedHours deduction : ℕ) :
    (S.issue person verifiedHours deduction).balance person =
      S.balance person + (verifiedHours - deduction) := by
  simp [issue]

variable [DecidableEq Good]

/-- A work ledger joins the physical production state to the certificate
ledger. Remaining capacity is consumed when a run is executed. -/
structure WorkLedger (Task : Type) where
  production : PublicProduction Person Good Task
  certificates : CertificateState Person Good

/-- Execute a run and issue its certificates atomically. A run is rejected if
the public stock ledgers disagree or the actual capacity and input checks fail.
The updated capacity prevents the same available run from being spent twice. -/
def WorkLedger.executeAndIssue {Task : Type} [DecidableEq Task] [Fintype Good]
    (L : WorkLedger (Person := Person) (Good := Good) Task)
    (person : Person) (task : Task) (runs deduction : ℕ)
    [Decidable (L.production.CanExecute person task runs)]
    [Decidable (L.certificates.stock = L.production.publicStock)] :
    WorkLedger (Person := Person) (Good := Good) Task :=
  if L.certificates.stock = L.production.publicStock ∧
      L.production.CanExecute person task runs then
    let stock' := L.production.execute person task runs
    let certificates' := L.certificates.issue person
      (runs * L.production.laborHours task) deduction
    { production := { L.production with
        publicStock := stock'
        capacity := Function.update L.production.capacity person
          (Function.update (L.production.capacity person) task
            (L.production.capacity person task - runs)) }
      certificates := { certificates' with stock := stock' } }
  else L

/-- Rejected work leaves both the physical and certificate ledgers unchanged. -/
theorem WorkLedger.rejected_executeAndIssue {Task : Type} [DecidableEq Task]
    [Fintype Good] (L : WorkLedger (Person := Person) (Good := Good) Task)
    (person : Person) (task : Task) (runs deduction : ℕ)
    [Decidable (L.production.CanExecute person task runs)]
    [Decidable (L.certificates.stock = L.production.publicStock)]
    (h : ¬ (L.certificates.stock = L.production.publicStock ∧
      L.production.CanExecute person task runs)) :
    L.executeAndIssue person task runs deduction = L := by
  simp [WorkLedger.executeAndIssue, h]

/-- Successful work consumes the corresponding remaining task capacity. -/
theorem WorkLedger.executeAndIssue_capacity {Task : Type} [DecidableEq Task]
    [Fintype Good] (L : WorkLedger (Person := Person) (Good := Good) Task)
    (person : Person) (task : Task) (runs deduction : ℕ)
    [Decidable (L.production.CanExecute person task runs)]
    [Decidable (L.certificates.stock = L.production.publicStock)]
    (hstock : L.certificates.stock = L.production.publicStock)
    (hwork : L.production.CanExecute person task runs) :
    (L.executeAndIssue person task runs deduction).production.capacity person task =
      L.production.capacity person task - runs := by
  simp [WorkLedger.executeAndIssue, hstock, hwork]

/-- Once a positive run exhausts a task's remaining capacity, the same run
cannot be executed again from the resulting ledger. -/
theorem WorkLedger.exhausted_run_cannot_repeat {Task : Type} [DecidableEq Task]
    [Fintype Good] (L : WorkLedger (Person := Person) (Good := Good) Task)
    (person : Person) (task : Task) (runs deduction : ℕ)
    [Decidable (L.production.CanExecute person task runs)]
    [Decidable (L.certificates.stock = L.production.publicStock)]
    (hstock : L.certificates.stock = L.production.publicStock)
    (hwork : L.production.CanExecute person task runs)
    (hexhausts : runs = L.production.capacity person task)
    (hpositive : 0 < runs) :
    ¬ (L.executeAndIssue person task runs deduction).production.CanExecute
      person task runs := by
  have hcapacity := L.executeAndIssue_capacity person task runs deduction hstock hwork
  rw [← hexhausts, Nat.sub_self] at hcapacity
  intro hrepeat
  have hle := hrepeat.2.1
  rw [hcapacity] at hle
  exact (Nat.not_le_of_gt hpositive) hle

def redeem (S : CertificateState Person Good) (cost : Good → ℕ)
    (person : Person) (good : Good) (quantity : ℕ) :
    CertificateState Person Good :=
  if quantity ≤ S.stock good ∧ cost good * quantity ≤ S.balance person then
    { balance := Function.update S.balance person
        (S.balance person - cost good * quantity)
      stock := Function.update S.stock good (S.stock good - quantity)
      consumed := Function.update S.consumed person
        (Function.update (S.consumed person) good
          (S.consumed person good + quantity)) }
  else S

theorem redeem_preserves_stock_if_unfunded
    (S : CertificateState Person Good) (cost : Good → ℕ)
    (person : Person) (good : Good) (quantity : ℕ)
    (h : ¬ (quantity ≤ S.stock good ∧
      cost good * quantity ≤ S.balance person)) :
    S.redeem cost person good quantity = S := by
  simp [redeem, h]

theorem redeem_conserves_good
    (S : CertificateState Person Good) (cost : Good → ℕ)
    (person : Person) (good : Good) (quantity : ℕ)
    (h : quantity ≤ S.stock good ∧
      cost good * quantity ≤ S.balance person) :
    (S.redeem cost person good quantity).stock good +
      (S.redeem cost person good quantity).consumed person good =
      S.stock good + S.consumed person good := by
  simp [redeem, h]
  omega

theorem redeem_conserves_claim
    (S : CertificateState Person Good) (cost : Good → ℕ)
    (person : Person) (good : Good) (quantity : ℕ)
    (h : quantity ≤ S.stock good ∧
      cost good * quantity ≤ S.balance person) :
    (S.redeem cost person good quantity).balance person +
      cost good * quantity = S.balance person := by
  simp [redeem, h, Nat.sub_add_cancel h.2]

/-- Atomic certificate redemption updating both the certificate stock and the
synchronized public production stock when they match. -/
def WorkLedger.redeem {Task : Type}
    (L : WorkLedger (Person := Person) (Good := Good) Task)
    (cost : Good → ℕ) (person : Person) (good : Good) (quantity : ℕ)
    [Decidable (L.certificates.stock = L.production.publicStock)] :
    WorkLedger (Person := Person) (Good := Good) Task :=
  if L.certificates.stock = L.production.publicStock then
    let certificates' := L.certificates.redeem cost person good quantity
    { production := { L.production with publicStock := certificates'.stock }
      certificates := certificates' }
  else L

theorem WorkLedger.executeAndIssue_stock_sync {Task : Type} [DecidableEq Task]
    [Fintype Good] (L : WorkLedger (Person := Person) (Good := Good) Task)
    (person : Person) (task : Task) (runs deduction : ℕ)
    [Decidable (L.production.CanExecute person task runs)]
    [Decidable (L.certificates.stock = L.production.publicStock)]
    (hsync : L.certificates.stock = L.production.publicStock) :
    (L.executeAndIssue person task runs deduction).certificates.stock =
      (L.executeAndIssue person task runs deduction).production.publicStock := by
  by_cases hwork : L.production.CanExecute person task runs
  · simp [WorkLedger.executeAndIssue, hsync, hwork]
  · simp [WorkLedger.executeAndIssue, hsync, hwork]

theorem WorkLedger.redeem_stock_sync {Task : Type}
    (L : WorkLedger (Person := Person) (Good := Good) Task)
    (cost : Good → ℕ) (person : Person) (good : Good) (quantity : ℕ)
    [Decidable (L.certificates.stock = L.production.publicStock)]
    (hsync : L.certificates.stock = L.production.publicStock) :
    (L.redeem cost person good quantity).certificates.stock =
      (L.redeem cost person good quantity).production.publicStock := by
  simp [WorkLedger.redeem, hsync]

theorem WorkLedger.redeem_conserves_good {Task : Type}
    (L : WorkLedger (Person := Person) (Good := Good) Task)
    (cost : Good → ℕ) (person : Person) (good : Good) (quantity : ℕ)
    [Decidable (L.certificates.stock = L.production.publicStock)]
    (hsync : L.certificates.stock = L.production.publicStock)
    (h : quantity ≤ L.certificates.stock good ∧
      cost good * quantity ≤ L.certificates.balance person) :
    (L.redeem cost person good quantity).certificates.stock good +
      (L.redeem cost person good quantity).certificates.consumed person good =
      L.certificates.stock good + L.certificates.consumed person good := by
  simp only [WorkLedger.redeem, hsync, ↓reduceIte]
  rw [← hsync]
  exact L.certificates.redeem_conserves_good cost person good quantity h

end CertificateState

/-- The planning board owns the stock and changes an accounting price from
observed demand. A fixed price at a boundary does not imply market clearing. -/
structure AdministeredPriceState (Good : Type) where
  price : Good → ℕ
  stock : Good → ℕ

namespace AdministeredPriceState

variable {Good : Type}

def clear (S : AdministeredPriceState Good) (demand : Good → ℕ) : Prop :=
  ∀ good, demand good = S.stock good

def adjust (S : AdministeredPriceState Good) (ceiling : ℕ)
    (demand : Good → ℕ) : AdministeredPriceState Good :=
  { S with price := fun good =>
      if S.stock good < demand good then min ceiling (S.price good + 1)
      else if demand good < S.stock good then S.price good - 1
      else S.price good }

theorem balanced_price_stays (S : AdministeredPriceState Good)
    (ceiling : ℕ) (demand : Good → ℕ)
    (h : S.clear demand) :
    (S.adjust ceiling demand).price = S.price := by
  funext good
  have hgood : demand good = S.stock good := h good
  simp [adjust, hgood]

/-- Price stability at a cap can coexist with excess demand. The stopping
test must use clearing, not merely an unchanged quoted price. -/
theorem ceiling_stall (S : AdministeredPriceState Good)
    (ceiling : ℕ) (demand : Good → ℕ) (good : Good)
    (atCeiling : S.price good = ceiling)
    (excess : S.stock good < demand good) :
    (S.adjust ceiling demand).price good = S.price good ∧
      ¬ S.clear demand := by
  constructor
  · simp [adjust, excess, atCeiling]
  · intro h
    have heq := h good
    rw [heq] at excess
    exact Nat.lt_irrefl _ excess

end AdministeredPriceState

/-- A spot exchange uses both parties' chosen assent and checks actual stock
and cash. The price is a total payment for the stated quantity. -/
structure SpotState where
  sellerStock : ℕ
  buyerStock : ℕ
  buyerCash : ℕ
  sellerCash : ℕ

namespace SpotState

def settle (S : SpotState) (quantity payment : ℕ)
    (sellerOffers buyerAccepts : Bool) : SpotState :=
  if sellerOffers && buyerAccepts && decide (quantity ≤ S.sellerStock) &&
      decide (payment ≤ S.buyerCash) then
    { sellerStock := S.sellerStock - quantity
      buyerStock := S.buyerStock + quantity
      buyerCash := S.buyerCash - payment
      sellerCash := S.sellerCash + payment }
  else S

theorem refusal_preserves_state (S : SpotState) (quantity payment : ℕ)
    (buyerAccepts : Bool) :
    S.settle quantity payment false buyerAccepts = S := by
  simp [settle]

theorem acceptance_absent_preserves_state (S : SpotState) (quantity payment : ℕ)
    (sellerOffers : Bool) :
    S.settle quantity payment sellerOffers false = S := by
  simp [settle]

theorem successful_trade_conserves_goods (S : SpotState)
    (quantity payment : ℕ) (sellerOffers buyerAccepts : Bool)
    (h : (sellerOffers && buyerAccepts && decide (quantity ≤ S.sellerStock) &&
      decide (payment ≤ S.buyerCash)) = true) :
    (S.settle quantity payment sellerOffers buyerAccepts).sellerStock +
      (S.settle quantity payment sellerOffers buyerAccepts).buyerStock =
      S.sellerStock + S.buyerStock := by
  have hq : quantity ≤ S.sellerStock :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  unfold settle
  rw [h]
  dsimp
  omega

theorem successful_trade_conserves_cash (S : SpotState)
    (quantity payment : ℕ) (sellerOffers buyerAccepts : Bool)
    (h : (sellerOffers && buyerAccepts && decide (quantity ≤ S.sellerStock) &&
      decide (payment ≤ S.buyerCash)) = true) :
    (S.settle quantity payment sellerOffers buyerAccepts).buyerCash +
      (S.settle quantity payment sellerOffers buyerAccepts).sellerCash =
      S.buyerCash + S.sellerCash := by
  have hc : payment ≤ S.buyerCash :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  unfold settle
  rw [h]
  dsimp
  omega

end SpotState

end EconomicCalculation
end Praxeology
end
