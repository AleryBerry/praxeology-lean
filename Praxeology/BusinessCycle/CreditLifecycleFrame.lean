/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.Clusters
public import Praxeology.FirmWitness

/-!
# Multi-stage credit events on an ActionFrame

The finite frame has successive issuance, two advances, project completion,
two repayments, and maturity moments. Its side histories represent feasible
unilateral choices at each bilateral exchange.
-/

@[expose] public section

namespace Praxeology

namespace CreditLifecycleTree

abbrev Node := Fin 20
abbrev History := Fin 14

/-- The mainline moments: issue, two advances, completion, two repayments,
and maturity. -/
def mainMoment (stage : Fin 7) : Node :=
  ⟨stage.val, by omega⟩

def lifecycleLeaf (h : History) : Node :=
  ⟨h.val + 6, by omega⟩

def historyByIndex (index : Fin 14) : History := index

def mainHistory : History := historyByIndex 0
def issueRefusalHistory : History := historyByIndex 1

def lifecycleAncestor (t u : Node) : Prop :=
  match u.val with
  | 0 => t.val = 0
  | 1 => t.val ≤ 1
  | 2 => t.val ≤ 2
  | 3 => t.val ≤ 3
  | 4 => t.val ≤ 4
  | 5 => t.val ≤ 5
  | 6 => t.val ≤ 6
  | 7 => t.val = 0 ∨ t.val = 7
  | 8 | 9 | 10 => t.val = 0 ∨ t.val = 1 ∨ t = u
  | 11 | 12 | 13 => t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t = u
  | 14 | 15 | 16 => t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨
      t.val = 3 ∨ t.val = 4 ∨ t = u
  | _ => t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨
      t.val = 4 ∨ t.val = 5 ∨ t = u

def lifecyclePrecedence (t u : Node) : Prop := t ≠ u ∧ lifecycleAncestor t u

def lifecycleMemHist (t : Node) (h : History) : Prop :=
  lifecycleAncestor t (lifecycleLeaf h)

/-- Depth in the finite history tree. Every proper ancestor has lower depth,
and each selected next moment raises depth by exactly one. -/
def lifecycleDepth (t : Node) : ℕ :=
  if t.val = 7 then 1
  else if 8 ≤ t.val ∧ t.val ≤ 10 then 2
  else if 11 ≤ t.val ∧ t.val ≤ 13 then 3
  else if 14 ≤ t.val ∧ t.val ≤ 16 then 5
  else if 17 ≤ t.val ∧ t.val ≤ 19 then 6
  else t.val

instance (t u : Node) : Decidable (lifecycleAncestor t u) := by
  unfold lifecycleAncestor
  split <;> infer_instance

instance (t u : Node) : Decidable (lifecyclePrecedence t u) := by
  unfold lifecyclePrecedence
  infer_instance

instance (t : Node) (h : History) : Decidable (lifecycleMemHist t h) := by
  unfold lifecycleMemHist
  infer_instance

def issueMoment : Node := mainMoment 0
def firstAdvanceMoment : Node := mainMoment 1
def secondAdvanceMoment : Node := mainMoment 2
def projectCompletionMoment : Node := mainMoment 3
def firstRepaymentMoment : Node := mainMoment 4
def secondRepaymentMoment : Node := mainMoment 5
def maturityMoment : Node := mainMoment 6

def creditLifecycleMoney : WorkshopMeans := tokenMeans
def creditLifecycleCollateral : WorkshopMeans := rawMeans
def creditLifecycleReserve : WorkshopMeans := capacityMeans

def creditIssueAction : WorkshopAction := .produceIntermediate0

def firstAdvanceOffer : WorkshopAction :=
  .offer .operator .entrepreneur 1 creditLifecycleMoney 1 creditLifecycleCollateral
def firstAdvanceAccept : WorkshopAction :=
  .accept .entrepreneur .operator 1 creditLifecycleMoney 1 creditLifecycleCollateral
def secondAdvanceOffer : WorkshopAction :=
  .offer .operator .customer 1 creditLifecycleMoney 1 creditLifecycleCollateral
def secondAdvanceAccept : WorkshopAction :=
  .accept .customer .operator 1 creditLifecycleMoney 1 creditLifecycleCollateral
def firstRepaymentOffer : WorkshopAction :=
  .offer .entrepreneur .operator 2 creditLifecycleMoney 1 creditLifecycleCollateral
def firstRepaymentAccept : WorkshopAction :=
  .accept .operator .entrepreneur 2 creditLifecycleMoney 1 creditLifecycleCollateral
def secondRepaymentOffer : WorkshopAction :=
  .offer .customer .operator 2 creditLifecycleMoney 1 creditLifecycleCollateral
def secondRepaymentAccept : WorkshopAction :=
  .accept .operator .customer 2 creditLifecycleMoney 1 creditLifecycleCollateral

def eventMenu (α : WorkshopAction) : Finset WorkshopAction := {.idle, α}

theorem eventMenu_mem_cases {α β : WorkshopAction} (h : α ∈ eventMenu β) :
    α = .idle ∨ α = β := by
  change α ∈ insert WorkshopAction.idle {β} at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  exact h

def creditLifecycleChoice (i : WorkshopAgent) (t : Node) : WorkshopAction :=
  match t.val, i with
  | 0, .operator => creditIssueAction
  | 1, .operator => firstAdvanceOffer
  | 1, .entrepreneur => firstAdvanceAccept
  | 2, .operator => secondAdvanceOffer
  | 2, .customer => secondAdvanceAccept
  | 4, .entrepreneur => firstRepaymentOffer
  | 4, .operator => firstRepaymentAccept
  | 5, .customer => secondRepaymentOffer
  | 5, .operator => secondRepaymentAccept
  | _, _ => .idle

def creditLifecycleActionsAt (i : WorkshopAgent) (t : Node) : Finset WorkshopAction :=
  eventMenu (creditLifecycleChoice i t)

def lifecycleProfile (base : ℕ) (h : History) : ℕ :=
  if (lifecycleLeaf h).val = base then 1
  else if (lifecycleLeaf h).val = base + 1 then 2
  else if (lifecycleLeaf h).val = base + 2 then 3
  else 0

def lifecycleProfileHistory (base profile : ℕ) : History :=
  if base = 8 then
    if profile = 0 then mainHistory
    else if profile = 1 then historyByIndex 2
    else if profile = 2 then historyByIndex 3
    else historyByIndex 4
  else if base = 11 then
    if profile = 0 then mainHistory
    else if profile = 1 then historyByIndex 5
    else if profile = 2 then historyByIndex 6
    else historyByIndex 7
  else if base = 14 then
    if profile = 0 then mainHistory
    else if profile = 1 then historyByIndex 8
    else if profile = 2 then historyByIndex 9
    else historyByIndex 10
  else
    if profile = 0 then mainHistory
    else if profile = 1 then historyByIndex 11
    else if profile = 2 then historyByIndex 12
    else historyByIndex 13

def issueRefusalMoment : Node := ⟨7, by omega⟩

def lifecycleNextMoment (t : Node) (h : History) : Node :=
  match t.val with
  | 0 => if h.val = 1 then issueRefusalMoment else mainMoment 1
  | 1 => if 2 ≤ h.val ∧ h.val ≤ 4 then lifecycleLeaf h else mainMoment 2
  | 2 => if 5 ≤ h.val ∧ h.val ≤ 7 then lifecycleLeaf h else mainMoment 3
  | 3 => mainMoment 4
  | 4 => if 8 ≤ h.val ∧ h.val ≤ 10 then lifecycleLeaf h else mainMoment 5
  | 5 => if 11 ≤ h.val ∧ h.val ≤ 13 then lifecycleLeaf h else mainMoment 6
  | _ => t

def lifecycleEnactedByNext (i : WorkshopAgent) (t next : Node) : WorkshopAction :=
  match t.val, i with
  | 0, .operator => if next.val = 7 then .idle else creditIssueAction
  | 1, .operator => if next.val = 8 ∨ next.val = 10 then .idle else firstAdvanceOffer
  | 1, .entrepreneur => if next.val = 9 ∨ next.val = 10 then .idle else firstAdvanceAccept
  | 2, .operator => if next.val = 11 ∨ next.val = 13 then .idle else secondAdvanceOffer
  | 2, .customer => if next.val = 12 ∨ next.val = 13 then .idle else secondAdvanceAccept
  | 4, .entrepreneur => if next.val = 14 ∨ next.val = 16 then .idle else firstRepaymentOffer
  | 4, .operator => if next.val = 15 ∨ next.val = 16 then .idle else firstRepaymentAccept
  | 5, .customer => if next.val = 17 ∨ next.val = 19 then .idle else secondRepaymentOffer
  | 5, .operator => if next.val = 18 ∨ next.val = 19 then .idle else secondRepaymentAccept
  | _, _ => .idle

def lifecycleEnacted (i : WorkshopAgent) (t : Node) (h : History) : WorkshopAction :=
  lifecycleEnactedByNext i t (lifecycleNextMoment t h)

/-- Agents other than the issuer stay idle at the issuance decision, regardless
of which history follows it. -/
theorem lifecycle_nonissuer_idle_at_issue (i : WorkshopAgent)
    (hi : i ≠ .operator) (h : History) :
    lifecycleEnacted i issueMoment h = .idle := by
  cases i with
  | operator => exact (hi rfl).elim
  | entrepreneur =>
      simp [lifecycleEnacted, lifecycleEnactedByNext,
        issueMoment, mainMoment]
  | customer =>
      simp [lifecycleEnacted, lifecycleEnactedByNext,
        issueMoment, mainMoment]

def lifecycleEventMomentForBase (base : ℕ) : Node :=
  if base = 8 then firstAdvanceMoment
  else if base = 11 then secondAdvanceMoment
  else if base = 14 then firstRepaymentMoment
  else if base = 17 then secondRepaymentMoment
  else issueMoment

def lifecycleEventOffererForBase (base : ℕ) : WorkshopAgent :=
  if base = 8 then .operator
  else if base = 11 then .operator
  else if base = 14 then .entrepreneur
  else if base = 17 then .customer
  else .operator

def lifecycleEventAcceptorForBase (base : ℕ) : WorkshopAgent :=
  if base = 8 then .entrepreneur
  else if base = 11 then .customer
  else if base = 14 then .operator
  else if base = 17 then .operator
  else .operator

def lifecycleEventOfferForBase (base : ℕ) : WorkshopAction :=
  if base = 8 then firstAdvanceOffer
  else if base = 11 then secondAdvanceOffer
  else if base = 14 then firstRepaymentOffer
  else if base = 17 then secondRepaymentOffer
  else .idle

def lifecycleEventAcceptForBase (base : ℕ) : WorkshopAction :=
  if base = 8 then firstAdvanceAccept
  else if base = 11 then secondAdvanceAccept
  else if base = 14 then firstRepaymentAccept
  else if base = 17 then secondRepaymentAccept
  else .idle

theorem lifecycle_profile_history_event_laws (base profile : ℕ)
    (hbase : base = 8 ∨ base = 11 ∨ base = 14 ∨ base = 17)
    (hprofile : profile < 4) :
    lifecycleMemHist (lifecycleEventMomentForBase base)
        (lifecycleProfileHistory base profile) ∧
      lifecycleEnacted (lifecycleEventOffererForBase base)
        (lifecycleEventMomentForBase base) (lifecycleProfileHistory base profile) =
          (if profile = 0 ∨ profile = 2 then
            lifecycleEventOfferForBase base else .idle) ∧
      lifecycleEnacted (lifecycleEventAcceptorForBase base)
        (lifecycleEventMomentForBase base) (lifecycleProfileHistory base profile) =
          (if profile = 0 ∨ profile = 1 then
            lifecycleEventAcceptForBase base else .idle) := by
  rcases hbase with rfl | rfl | rfl | rfl
  all_goals
    by_cases hp0 : profile = 0
    · subst profile
      decide
    · by_cases hp1 : profile = 1
      · subst profile
        decide
      · by_cases hp2 : profile = 2
        · subst profile
          decide
        · have hp3 : profile = 3 := by omega
          subst profile
          decide

def lifecycleEventAt (t : Node) : Option (ℕ × WorkshopAgent × WorkshopAgent) :=
  match t.val with
  | 1 => some (8, .operator, .entrepreneur)
  | 2 => some (11, .operator, .customer)
  | 4 => some (14, .entrepreneur, .operator)
  | 5 => some (17, .customer, .operator)
  | _ => none

def lifecycleProfileNumber (offererActive acceptorActive : Bool) : ℕ :=
  if offererActive then if acceptorActive then 0 else 2
  else if acceptorActive then 1 else 3

theorem lifecycle_profile_number_event_laws (base : ℕ)
    (hbase : base = 8 ∨ base = 11 ∨ base = 14 ∨ base = 17)
    (offererActive acceptorActive : Bool) :
    lifecycleMemHist (lifecycleEventMomentForBase base)
        (lifecycleProfileHistory base
          (lifecycleProfileNumber offererActive acceptorActive)) ∧
      lifecycleEnacted (lifecycleEventOffererForBase base)
        (lifecycleEventMomentForBase base)
        (lifecycleProfileHistory base
          (lifecycleProfileNumber offererActive acceptorActive)) =
          (if offererActive then lifecycleEventOfferForBase base else .idle) ∧
      lifecycleEnacted (lifecycleEventAcceptorForBase base)
        (lifecycleEventMomentForBase base)
        (lifecycleProfileHistory base
          (lifecycleProfileNumber offererActive acceptorActive)) =
          (if acceptorActive then lifecycleEventAcceptForBase base else .idle) := by
  have hprof : lifecycleProfileNumber offererActive acceptorActive < 4 := by
    cases offererActive <;> cases acceptorActive <;> decide
  have hlaw := lifecycle_profile_history_event_laws base
    (lifecycleProfileNumber offererActive acceptorActive) hbase hprof
  rcases hlaw with ⟨hm, ho, ha⟩
  refine ⟨hm, ?_, ?_⟩
  · cases offererActive <;> cases acceptorActive <;>
      simpa [lifecycleProfileNumber] using ho
  · cases offererActive <;> cases acceptorActive <;>
      simpa [lifecycleProfileNumber] using ha

theorem lifecycle_event_at_matches (t : Node) :
    match lifecycleEventAt t with
    | none => True
    | some (base, offerer, acceptor) =>
        (base = 8 ∨ base = 11 ∨ base = 14 ∨ base = 17) ∧
        t = lifecycleEventMomentForBase base ∧
        offerer = lifecycleEventOffererForBase base ∧
        acceptor = lifecycleEventAcceptorForBase base := by
  fin_cases t <;>
    simp [lifecycleEventAt, lifecycleEventMomentForBase,
      lifecycleEventOffererForBase, lifecycleEventAcceptorForBase,
      firstAdvanceMoment, secondAdvanceMoment, firstRepaymentMoment,
      secondRepaymentMoment, mainMoment]

theorem lifecycle_profile_number_event_at_laws (t : Node) (base : ℕ)
    (offerer acceptor : WorkshopAgent)
    (hevent : lifecycleEventAt t = some (base, offerer, acceptor))
    (offererActive acceptorActive : Bool) :
    lifecycleMemHist t
        (lifecycleProfileHistory base
          (lifecycleProfileNumber offererActive acceptorActive)) ∧
      lifecycleEnacted offerer t
        (lifecycleProfileHistory base
          (lifecycleProfileNumber offererActive acceptorActive)) =
          (if offererActive then lifecycleEventOfferForBase base else .idle) ∧
      lifecycleEnacted acceptor t
        (lifecycleProfileHistory base
          (lifecycleProfileNumber offererActive acceptorActive)) =
          (if acceptorActive then lifecycleEventAcceptForBase base else .idle) := by
  have hmatch := lifecycle_event_at_matches t
  rw [hevent] at hmatch
  rcases hmatch with ⟨hbase, rfl, rfl, rfl⟩
  exact lifecycle_profile_number_event_laws base hbase offererActive acceptorActive

theorem lifecycle_event_choice_roles (base : ℕ)
    (hbase : base = 8 ∨ base = 11 ∨ base = 14 ∨ base = 17) :
    creditLifecycleChoice (lifecycleEventOffererForBase base)
        (lifecycleEventMomentForBase base) = lifecycleEventOfferForBase base ∧
      creditLifecycleChoice (lifecycleEventAcceptorForBase base)
        (lifecycleEventMomentForBase base) = lifecycleEventAcceptForBase base ∧
      ∀ i, i ≠ lifecycleEventOffererForBase base →
        i ≠ lifecycleEventAcceptorForBase base →
          creditLifecycleChoice i (lifecycleEventMomentForBase base) = .idle := by
  rcases hbase with rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · simp [creditLifecycleChoice, lifecycleEventMomentForBase,
        lifecycleEventOffererForBase, lifecycleEventOfferForBase,
        firstAdvanceMoment, secondAdvanceMoment, firstRepaymentMoment,
        secondRepaymentMoment, mainMoment]
    · simp [creditLifecycleChoice, lifecycleEventMomentForBase,
        lifecycleEventAcceptorForBase, lifecycleEventAcceptForBase,
        firstAdvanceMoment, secondAdvanceMoment, firstRepaymentMoment,
        secondRepaymentMoment, mainMoment]
    · intro i hi ho
      cases i <;> simp_all [creditLifecycleChoice,
        lifecycleEventMomentForBase, lifecycleEventOffererForBase,
        lifecycleEventAcceptorForBase, firstAdvanceMoment,
        secondAdvanceMoment, firstRepaymentMoment, secondRepaymentMoment,
        mainMoment]

theorem lifecycle_event_outsider_idle (base : ℕ)
    (hbase : base = 8 ∨ base = 11 ∨ base = 14 ∨ base = 17)
    (i : WorkshopAgent)
    (ho : i ≠ lifecycleEventOffererForBase base)
    (ha : i ≠ lifecycleEventAcceptorForBase base) (h : History) :
    lifecycleEnacted i (lifecycleEventMomentForBase base) h = .idle := by
  rcases hbase with rfl | rfl | rfl | rfl
  all_goals
    cases i <;>
      simp_all [lifecycleEnacted, lifecycleEnactedByNext,
        lifecycleEventMomentForBase, lifecycleEventOffererForBase,
        lifecycleEventAcceptorForBase,
        firstAdvanceMoment, secondAdvanceMoment, firstRepaymentMoment,
        secondRepaymentMoment, mainMoment]

theorem lifecycle_enacted_in_menu (i : WorkshopAgent) (t : Node) (h : History) :
    lifecycleEnacted i t h = .idle ∨
      lifecycleEnacted i t h = creditLifecycleChoice i t := by
  have hall : ∀ i : WorkshopAgent, ∀ t : Node, ∀ h : History,
      lifecycleEnacted i t h = .idle ∨
        lifecycleEnacted i t h = creditLifecycleChoice i t := by
    decide
  exact hall i t h

def lifecycleSigma (i : WorkshopAgent) (t : Node) (α : WorkshopAction)
    (h : History) : History :=
  if lifecycleEnacted i t h = α then h
  else if t.val = 0 then
    if i = .operator then
      if α = .idle then issueRefusalHistory else mainHistory
    else h
  else
    match lifecycleEventAt t with
    | none => h
    | some (base, offerer, acceptor) =>
        let oa : Bool := if i = offerer then decide (α ≠ .idle)
          else decide (lifecycleEnacted offerer t h ≠ .idle)
        let aa : Bool := if i = acceptor then decide (α ≠ .idle)
          else decide (lifecycleEnacted acceptor t h ≠ .idle)
        lifecycleProfileHistory base (lifecycleProfileNumber oa aa)

theorem lifecycle_event_offer_ne_idle (base : ℕ)
    (hbase : base = 8 ∨ base = 11 ∨ base = 14 ∨ base = 17) :
    lifecycleEventOfferForBase base ≠ .idle := by
  rcases hbase with rfl | rfl | rfl | rfl <;>
    simp [lifecycleEventOfferForBase, firstAdvanceOffer,
      secondAdvanceOffer, firstRepaymentOffer, secondRepaymentOffer]

theorem lifecycle_event_accept_ne_idle (base : ℕ)
    (hbase : base = 8 ∨ base = 11 ∨ base = 14 ∨ base = 17) :
    lifecycleEventAcceptForBase base ≠ .idle := by
  rcases hbase with rfl | rfl | rfl | rfl <;>
    simp [lifecycleEventAcceptForBase, firstAdvanceAccept,
      secondAdvanceAccept, firstRepaymentAccept, secondRepaymentAccept]

theorem lifecycle_sigma_event_menu_action (i : WorkshopAgent) (t : Node)
    (h : History) (α : WorkshopAction) (base : ℕ)
    (offerer acceptor : WorkshopAgent)
    (hevent : lifecycleEventAt t = some (base, offerer, acceptor))
    (hmenu : α = .idle ∨ α = creditLifecycleChoice i t)
    (hneq : lifecycleEnacted i t h ≠ α) :
    lifecycleMemHist t (lifecycleSigma i t α h) ∧
      lifecycleEnacted i t (lifecycleSigma i t α h) = α := by
  have hmatch := lifecycle_event_at_matches t
  rw [hevent] at hmatch
  rcases hmatch with ⟨hbase, rfl, rfl, rfl⟩
  have hnotzero : (lifecycleEventMomentForBase base).val ≠ 0 := by
    rcases hbase with rfl | rfl | rfl | rfl <;> decide
  have hrole : i = lifecycleEventOffererForBase base ∨
      i = lifecycleEventAcceptorForBase base := by
    by_contra hnot
    have hiO : i ≠ lifecycleEventOffererForBase base := by
      intro hi
      exact hnot (Or.inl hi)
    have hiA : i ≠ lifecycleEventAcceptorForBase base := by
      intro hi
      exact hnot (Or.inr hi)
    have hIdle := lifecycle_event_outsider_idle base hbase i hiO hiA h
    have hαIdle : α = .idle := by
      rcases hmenu with hIdle' | hChoice
      · exact hIdle'
      · rw [(lifecycle_event_choice_roles base hbase).2.2 i hiO hiA] at hChoice
        exact hChoice
    apply hneq
    rw [hIdle, hαIdle]
  let offererActive : Bool := if i = lifecycleEventOffererForBase base then
      decide (α ≠ .idle) else
      decide (lifecycleEnacted (lifecycleEventOffererForBase base)
        (lifecycleEventMomentForBase base) h ≠ .idle)
  let acceptorActive : Bool := if i = lifecycleEventAcceptorForBase base then
      decide (α ≠ .idle) else
      decide (lifecycleEnacted (lifecycleEventAcceptorForBase base)
        (lifecycleEventMomentForBase base) h ≠ .idle)
  have hprofile := lifecycle_profile_number_event_at_laws
    (lifecycleEventMomentForBase base) base
    (lifecycleEventOffererForBase base) (lifecycleEventAcceptorForBase base)
    (by rcases hbase with rfl | rfl | rfl | rfl <;> rfl)
    offererActive acceptorActive
  have hsigma : lifecycleSigma i (lifecycleEventMomentForBase base) α h =
      lifecycleProfileHistory base
        (lifecycleProfileNumber offererActive acceptorActive) := by
    rcases hbase with rfl | rfl | rfl | rfl <;>
      (simp only [lifecycleSigma]
       rw [ite_eq_right hneq, ite_eq_right hnotzero]
       simp [lifecycleEventAt, lifecycleEventMomentForBase,
         lifecycleEventOffererForBase, lifecycleEventAcceptorForBase,
         offererActive, acceptorActive, firstAdvanceMoment,
         secondAdvanceMoment, firstRepaymentMoment, secondRepaymentMoment,
         mainMoment])
  rcases hprofile with ⟨hmem, hoffer, haccept⟩
  refine ⟨?_, ?_⟩
  · rw [hsigma]
    exact hmem
  · rw [hsigma]
    rcases hrole with hOfferer | hAcceptor
    · subst i
      have hpreferred :
          (if α ≠ .idle then lifecycleEventOfferForBase base else .idle) = α := by
        rcases hmenu with hIdle | hChoice
        · subst α
          simp
        · rw [hChoice, (lifecycle_event_choice_roles base hbase).1]
          simp [lifecycle_event_offer_ne_idle base hbase]
      rw [hoffer]
      simpa [offererActive] using hpreferred
    · subst i
      have hpreferred :
          (if α ≠ .idle then lifecycleEventAcceptForBase base else .idle) = α := by
        rcases hmenu with hIdle | hChoice
        · subst α
          simp
        · rw [hChoice, (lifecycle_event_choice_roles base hbase).2.1]
          simp [lifecycle_event_accept_ne_idle base hbase]
      rw [haccept]
      simpa [acceptorActive] using hpreferred

theorem lifecycle_sigma_event_coagency (i j : WorkshopAgent) (t : Node)
    (h : History) (α : WorkshopAction) (base : ℕ)
    (offerer acceptor : WorkshopAgent)
    (hevent : lifecycleEventAt t = some (base, offerer, acceptor))
    (hmenu : α = .idle ∨ α = creditLifecycleChoice i t)
    (hij : i ≠ j) (hneq : lifecycleEnacted i t h ≠ α) :
    lifecycleEnacted j t (lifecycleSigma i t α h) = lifecycleEnacted j t h := by
  have hmatch := lifecycle_event_at_matches t
  rw [hevent] at hmatch
  rcases hmatch with ⟨hbase, rfl, rfl, rfl⟩
  have hnotzero : (lifecycleEventMomentForBase base).val ≠ 0 := by
    rcases hbase with rfl | rfl | rfl | rfl <;> decide
  let offererActive : Bool := if i = lifecycleEventOffererForBase base then
      decide (α ≠ .idle) else
      decide (lifecycleEnacted (lifecycleEventOffererForBase base)
        (lifecycleEventMomentForBase base) h ≠ .idle)
  let acceptorActive : Bool := if i = lifecycleEventAcceptorForBase base then
      decide (α ≠ .idle) else
      decide (lifecycleEnacted (lifecycleEventAcceptorForBase base)
        (lifecycleEventMomentForBase base) h ≠ .idle)
  have hprofile := lifecycle_profile_number_event_at_laws
    (lifecycleEventMomentForBase base) base
    (lifecycleEventOffererForBase base) (lifecycleEventAcceptorForBase base)
    (by rcases hbase with rfl | rfl | rfl | rfl <;> rfl)
    offererActive acceptorActive
  have hsigma : lifecycleSigma i (lifecycleEventMomentForBase base) α h =
      lifecycleProfileHistory base
        (lifecycleProfileNumber offererActive acceptorActive) := by
    rcases hbase with rfl | rfl | rfl | rfl <;>
      (simp only [lifecycleSigma]
       rw [ite_eq_right hneq, ite_eq_right hnotzero]
       simp [lifecycleEventAt, lifecycleEventMomentForBase,
         lifecycleEventOffererForBase, lifecycleEventAcceptorForBase,
         offererActive, acceptorActive, firstAdvanceMoment,
         secondAdvanceMoment, firstRepaymentMoment, secondRepaymentMoment,
         mainMoment])
  rcases hprofile with ⟨_, hoffer, haccept⟩
  by_cases hjO : j = lifecycleEventOffererForBase base
  · have hiO : i ≠ lifecycleEventOffererForBase base := by
      intro hi
      exact hij (hi.trans hjO.symm)
    subst j
    rcases lifecycle_enacted_in_menu
        (lifecycleEventOffererForBase base)
        (lifecycleEventMomentForBase base) h with hIdle | hChoice
    · rw [hsigma, hIdle, hoffer]
      simp [offererActive, hiO, hIdle]
    · rw [hsigma, hChoice, hoffer,
        (lifecycle_event_choice_roles base hbase).1]
      have hactive : lifecycleEnacted
          (lifecycleEventOffererForBase base)
          (lifecycleEventMomentForBase base) h ≠ .idle := by
        rw [hChoice, (lifecycle_event_choice_roles base hbase).1]
        exact lifecycle_event_offer_ne_idle base hbase
      have hactiveBool : offererActive = true := by
        simp [offererActive, hiO, hactive]
      rw [hactiveBool]
      rfl
  · by_cases hjA : j = lifecycleEventAcceptorForBase base
    · have hiA : i ≠ lifecycleEventAcceptorForBase base := by
        intro hi
        exact hij (hi.trans hjA.symm)
      subst j
      rcases lifecycle_enacted_in_menu
          (lifecycleEventAcceptorForBase base)
          (lifecycleEventMomentForBase base) h with hIdle | hChoice
      · rw [hsigma, hIdle, haccept]
        simp [acceptorActive, hiA, hIdle]
      · rw [hsigma, hChoice, haccept,
          (lifecycle_event_choice_roles base hbase).2.1]
        have hactive : lifecycleEnacted
            (lifecycleEventAcceptorForBase base)
            (lifecycleEventMomentForBase base) h ≠ .idle := by
          rw [hChoice, (lifecycle_event_choice_roles base hbase).2.1]
          exact lifecycle_event_accept_ne_idle base hbase
        have hactiveBool : acceptorActive = true := by
          simp [acceptorActive, hiA, hactive]
        rw [hactiveBool]
        rfl
    · have hOld := lifecycle_event_outsider_idle base hbase j hjO hjA h
      rw [hsigma]
      rw [lifecycle_event_outsider_idle base hbase j hjO hjA]
      exact hOld.symm

theorem lifecycle_sigma_menu_action (i : WorkshopAgent) (t : Node)
    (h : History) (α : WorkshopAction)
    (hmem : lifecycleMemHist t h)
    (hmenu : α = .idle ∨ α = creditLifecycleChoice i t) :
    lifecycleMemHist t (lifecycleSigma i t α h) ∧
      lifecycleEnacted i t (lifecycleSigma i t α h) = α := by
  by_cases hsame : lifecycleEnacted i t h = α
  · refine ⟨?_, ?_⟩
    · simpa [lifecycleSigma, hsame] using hmem
    · simp [lifecycleSigma, hsame]
  · by_cases htzero : t.val = 0
    · have ht : t = issueMoment := Fin.ext htzero
      subst t
      cases i with
      | operator =>
          rcases hmenu with hIdle | hChoice
          · subst α
            have hsigma : lifecycleSigma .operator issueMoment .idle h =
                issueRefusalHistory := by
              unfold lifecycleSigma
              rw [ite_eq_right hsame]
              simp [issueMoment, mainMoment]
            refine ⟨?_, ?_⟩
            · rw [hsigma]
              decide
            · rw [hsigma]
              decide
          · have hchoice : creditLifecycleChoice .operator issueMoment =
                creditIssueAction := by
              simp [creditLifecycleChoice, issueMoment, mainMoment,
                creditIssueAction]
            rw [hchoice] at hChoice
            subst α
            have hsigma : lifecycleSigma .operator issueMoment
                creditIssueAction h = mainHistory := by
              unfold lifecycleSigma
              rw [ite_eq_right hsame]
              simp [issueMoment, mainMoment, creditIssueAction]
            refine ⟨?_, ?_⟩
            · rw [hsigma]
              decide
            · rw [hsigma]
              decide
      | entrepreneur =>
          have hEnacted : lifecycleEnacted .entrepreneur issueMoment h = .idle := by
            simp [lifecycleEnacted, lifecycleEnactedByNext,
              issueMoment, mainMoment]
          have hChoice : creditLifecycleChoice .entrepreneur issueMoment = .idle := by
            simp [creditLifecycleChoice, issueMoment, mainMoment]
          rcases hmenu with hIdle | hChoice'
          · subst α
            exact (hsame (by simpa using hEnacted)).elim
          · rw [hChoice] at hChoice'
            subst α
            exact (hsame (by simpa using hEnacted)).elim
      | customer =>
          have hEnacted : lifecycleEnacted .customer issueMoment h = .idle := by
            simp [lifecycleEnacted, lifecycleEnactedByNext,
              issueMoment, mainMoment]
          have hChoice : creditLifecycleChoice .customer issueMoment = .idle := by
            simp [creditLifecycleChoice, issueMoment, mainMoment]
          rcases hmenu with hIdle | hChoice'
          · subst α
            exact (hsame (by simpa using hEnacted)).elim
          · rw [hChoice] at hChoice'
            subst α
            exact (hsame (by simpa using hEnacted)).elim
    · cases hevent : lifecycleEventAt t with
      | some event =>
          rcases event with ⟨base, offerer, acceptor⟩
          exact lifecycle_sigma_event_menu_action i t h α base offerer acceptor
            hevent hmenu hsame
      | none =>
          have hEnacted : lifecycleEnacted i t h = .idle := by
            fin_cases t <;>
              simp_all [lifecycleEnacted, lifecycleEnactedByNext,
                lifecycleNextMoment, lifecycleEventAt,
                mainMoment, issueRefusalMoment]
          have hChoice : creditLifecycleChoice i t = .idle := by
            fin_cases t <;>
              simp_all [creditLifecycleChoice, lifecycleEventAt]
          have hαIdle : α = .idle := by
            rcases hmenu with hIdle | hChoice'
            · exact hIdle
            · rw [hChoice] at hChoice'
              exact hChoice'
          exact (hsame (by rw [hEnacted, hαIdle])).elim

theorem lifecycle_sigma_menu_coagency (i j : WorkshopAgent) (t : Node)
    (h : History) (α : WorkshopAction)
    (hmenu : α = .idle ∨ α = creditLifecycleChoice i t)
    (hij : i ≠ j) :
    lifecycleEnacted j t (lifecycleSigma i t α h) =
      lifecycleEnacted j t h := by
  by_cases hsame : lifecycleEnacted i t h = α
  · simp [lifecycleSigma, hsame]
  · by_cases htzero : t.val = 0
    · have ht : t = issueMoment := Fin.ext htzero
      subst t
      cases i with
      | operator =>
          have hj : j ≠ .operator := by
            intro hj
            exact hij hj.symm
          calc
            lifecycleEnacted j issueMoment
                (lifecycleSigma .operator issueMoment α h) =
                .idle := lifecycle_nonissuer_idle_at_issue j hj _
            _ = lifecycleEnacted j issueMoment h :=
              (lifecycle_nonissuer_idle_at_issue j hj h).symm
      | entrepreneur =>
          have hαidle : α = .idle := by
            rcases hmenu with hIdle | hChoice
            · exact hIdle
            · simpa [creditLifecycleChoice, issueMoment, mainMoment] using hChoice
          have hnow : lifecycleEnacted .entrepreneur issueMoment h = .idle := by
            simp [lifecycleEnacted, lifecycleEnactedByNext,
              issueMoment, mainMoment]
          exact hsame (by rw [hnow, hαidle]) |>.elim
      | customer =>
          have hαidle : α = .idle := by
            rcases hmenu with hIdle | hChoice
            · exact hIdle
            · simpa [creditLifecycleChoice, issueMoment, mainMoment] using hChoice
          have hnow : lifecycleEnacted .customer issueMoment h = .idle := by
            simp [lifecycleEnacted, lifecycleEnactedByNext,
              issueMoment, mainMoment]
          exact hsame (by rw [hnow, hαidle]) |>.elim
    · cases hevent : lifecycleEventAt t with
      | some event =>
          rcases event with ⟨base, offerer, acceptor⟩
          exact lifecycle_sigma_event_coagency i j t h α base offerer acceptor
            hevent hmenu hij hsame
      | none =>
          simp [lifecycleSigma, hsame, htzero, hevent]

set_option maxHeartbeats 1000000 in
-- Exhaustive finite case split across CreditLifecycleFrame moments and histories
theorem lifecycle_sigma_realizes_idle :
    ∀ i t h, lifecycleMemHist t h →
      lifecycleMemHist t (lifecycleSigma i t .idle h) ∧
        lifecycleEnacted i t (lifecycleSigma i t .idle h) = .idle := by
  intro i t h hmem
  exact lifecycle_sigma_menu_action i t h .idle hmem (Or.inl rfl)

set_option maxHeartbeats 1000000 in
-- Exhaustive finite case split across CreditLifecycleFrame moments and histories
theorem lifecycle_sigma_realizes_choice :
    ∀ i t h, lifecycleMemHist t h →
      lifecycleMemHist t (lifecycleSigma i t (creditLifecycleChoice i t) h) ∧
        lifecycleEnacted i t
          (lifecycleSigma i t (creditLifecycleChoice i t) h) =
            creditLifecycleChoice i t := by
  intro i t h hmem
  exact lifecycle_sigma_menu_action i t h (creditLifecycleChoice i t)
    hmem (Or.inr rfl)

set_option maxHeartbeats 1000000 in
-- Exhaustive finite case split across CreditLifecycleFrame moments and histories
theorem lifecycle_sigma_co_agency_idle :
    ∀ i j t h, i ≠ j → lifecycleMemHist t h →
      lifecycleEnacted j t (lifecycleSigma i t .idle h) =
        lifecycleEnacted j t h := by
  intro i j t h hij hmem
  exact lifecycle_sigma_menu_coagency i j t h .idle (Or.inl rfl) hij

set_option maxHeartbeats 1000000 in
-- Exhaustive finite case split across CreditLifecycleFrame moments and histories
theorem lifecycle_sigma_co_agency_choice :
    ∀ i j t h, i ≠ j → lifecycleMemHist t h →
      lifecycleEnacted j t
        (lifecycleSigma i t (creditLifecycleChoice i t) h) =
          lifecycleEnacted j t h := by
  intro i j t h hij hmem
  exact lifecycle_sigma_menu_coagency i j t h (creditLifecycleChoice i t)
    (Or.inr rfl) hij

def lifecycleBaseStage (t : Node) : ℕ :=
  match t.val with
  | 7 => 0
  | 8 | 9 | 10 => 1
  | 11 | 12 | 13 => 2
  | 14 | 15 | 16 => 4
  | 17 | 18 | 19 => 5
  | n => n

def lifecycleBalance (i : WorkshopAgent) (stage : ℕ) (m : WorkshopMeans) : ℕ :=
  if m = creditLifecycleMoney then
    match i with
    | .operator =>
        if stage = 1 then 2 else if stage = 2 then 1
        else if stage = 5 then 2 else if stage = 6 then 4 else 0
    | .entrepreneur =>
        if stage ≤ 1 then 2 else if stage ≤ 4 then 3 else 1
    | .customer =>
        if stage ≤ 2 then 2 else if stage ≤ 5 then 3 else 1
  else if m = creditLifecycleCollateral then
    match i with
    | .operator =>
        if stage ≤ 1 then 0 else if stage ≤ 2 then 1
        else if stage ≤ 4 then 2 else if stage = 5 then 1 else 0
    | .entrepreneur =>
        if stage ≤ 1 then 1 else if stage ≤ 4 then 0 else 1
    | .customer =>
        if stage ≤ 2 then 1 else if stage ≤ 5 then 0 else 1
  else 0

def lifecycleOmega (i : WorkshopAgent) (t : Node) (_h : History)
    (m : WorkshopMeans) : ℕ := lifecycleBalance i (lifecycleBaseStage t) m

def creditLifecycleUseMeans (α : WorkshopAction) (m : WorkshopMeans) : ℕ :=
  match α with
  | .offer _ _ qA mA _ _ => if m = mA then qA else 0
  | .accept _ _ _ _ qB mB => if m = mB then qB else 0
  | _ => 0

def creditLifecycleYieldMeans (α : WorkshopAction) (m : WorkshopMeans) : ℕ :=
  match α with
  | .produceIntermediate0 => if m = creditLifecycleMoney then 2 else 0
  | .offer _ _ _ _ qB mB => if m = mB then qB else 0
  | .accept _ _ qA mA _ _ => if m = mA then qA else 0
  | _ => 0

theorem creditLifecycle_use_feasible (i : WorkshopAgent) (t : Node)
    (h : History) (α : WorkshopAction)
    (hα : α ∈ creditLifecycleActionsAt i t) :
    ∀ m, creditLifecycleUseMeans α m ≤ lifecycleOmega i t h m := by
  rcases eventMenu_mem_cases hα with hIdle | hChoice
  · subst α
    intro m
    simp [creditLifecycleUseMeans]
  · subst α
    intro m
    change creditLifecycleUseMeans (creditLifecycleChoice i t) m ≤
      lifecycleBalance i (lifecycleBaseStage t) m
    fin_cases i <;> fin_cases t <;> fin_cases m <;> decide

theorem lifecycle_precedence_source_lt_six :
    ∀ t u : Node, lifecyclePrecedence t u → t.val < 6 := by
  intro t u h
  rcases h with ⟨hne, hanc⟩
  have hneval : t.val ≠ u.val := by
    intro heq
    exact hne (Fin.ext heq)
  fin_cases u <;>
    simp_all [lifecycleAncestor] <;> omega

theorem lifecycle_precedence_depth :
    ∀ t u : Node, lifecyclePrecedence t u → lifecycleDepth t < lifecycleDepth u := by
  intro t u h
  rcases h with ⟨hne, hanc⟩
  have hneval : t.val ≠ u.val := by
    intro heq
    exact hne (Fin.ext heq)
  fin_cases u <;>
    simp_all [lifecycleAncestor, lifecycleDepth] <;>
    split_ifs <;> omega

theorem lifecycle_next_depth (t : Node) (h : History) (ht : t.val < 6) :
    lifecycleDepth (lifecycleNextMoment t h) = lifecycleDepth t + 1 := by
  have hleafval : (lifecycleLeaf h).val = h.val + 6 := rfl
  fin_cases t <;>
    simp_all [lifecycleDepth, lifecycleNextMoment,
      issueRefusalMoment, mainMoment] <;>
    split_ifs <;> omega

theorem lifecycle_next_mem (t : Node) (h : History) (ht : t.val < 6)
    (hmem : lifecycleMemHist t h) :
    lifecycleMemHist (lifecycleNextMoment t h) h := by
  rcases t with ⟨tv, htv⟩
  change tv < 6 at ht
  have hstage : tv = 0 ∨ tv = 1 ∨ tv = 2 ∨ tv = 3 ∨ tv = 4 ∨ tv = 5 := by omega
  rcases hstage with hstage | hstage | hstage | hstage | hstage | hstage <;>
    subst tv <;> fin_cases h <;>
    simp_all [lifecycleMemHist, lifecycleAncestor, lifecycleNextMoment,
      lifecycleLeaf, issueRefusalMoment, mainMoment]

theorem lifecycle_next_moment_val_gt (t : Node) (h : History)
    (ht : t.val < 6) : t.val < (lifecycleNextMoment t h).val := by
  rcases t with ⟨tv, htv⟩
  change tv < 6 at ht
  have hstage : tv = 0 ∨ tv = 1 ∨ tv = 2 ∨ tv = 3 ∨ tv = 4 ∨ tv = 5 := by omega
  have hleafval : (lifecycleLeaf h).val = h.val + 6 := rfl
  rcases hstage with hstage | hstage | hstage | hstage | hstage | hstage
  · subst tv
    change 0 < (if h.val = 1 then issueRefusalMoment else mainMoment 1).val
    split_ifs <;> decide
  · subst tv
    change 1 < (if 2 ≤ h.val ∧ h.val ≤ 4 then lifecycleLeaf h else mainMoment 2).val
    split_ifs
    · rw [hleafval]
      omega
    · decide
  · subst tv
    change 2 < (if 5 ≤ h.val ∧ h.val ≤ 7 then lifecycleLeaf h else mainMoment 3).val
    split_ifs
    · rw [hleafval]
      omega
    · decide
  · subst tv
    change 3 < (mainMoment 4).val
    decide
  · subst tv
    change 4 < (if 8 ≤ h.val ∧ h.val ≤ 10 then lifecycleLeaf h else mainMoment 5).val
    split_ifs
    · rw [hleafval]
      omega
    · decide
  · subst tv
    change 5 < (if 11 ≤ h.val ∧ h.val ≤ 13 then lifecycleLeaf h else mainMoment 6).val
    split_ifs
    · rw [hleafval]
      omega
    · decide

/-- Arithmetic characterization of the frame's finite ancestor relation. -/
def lifecycleAncestorByValue (t u : Node) : Prop :=
  (u.val ≤ 6 ∧ t.val ≤ u.val) ∨
  (u.val = 7 ∧ (t.val = 0 ∨ t.val = 7)) ∨
  (8 ≤ u.val ∧ u.val ≤ 10 ∧
    (t.val = 0 ∨ t.val = 1 ∨ t.val = u.val)) ∨
  (11 ≤ u.val ∧ u.val ≤ 13 ∧
    (t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = u.val)) ∨
  (14 ≤ u.val ∧ u.val ≤ 16 ∧
    (t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨ t.val = 4 ∨
      t.val = u.val)) ∨
  (17 ≤ u.val ∧ u.val ≤ 19 ∧
    (t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨ t.val = 4 ∨
      t.val = 5 ∨ t.val = u.val))

instance (t u : Node) : Decidable (lifecycleAncestorByValue t u) := by
  unfold lifecycleAncestorByValue
  infer_instance

theorem lifecycleAncestor_iff_by_value (t u : Node) :
    lifecycleAncestor t u ↔ lifecycleAncestorByValue t u := by
  revert t u
  decide

theorem lifecycle_ancestor_of_shared_future_val_lt {u v w : Node}
    (huw : lifecycleAncestor u w) (hvw : lifecycleAncestor v w)
    (hval : u.val < v.val) : lifecycleAncestor u v := by
  rw [lifecycleAncestor_iff_by_value] at huw hvw ⊢
  unfold lifecycleAncestorByValue at *
  omega

theorem lifecycle_next_precedes (t : Node) (h : History) (ht : t.val < 6)
    (hmem : lifecycleMemHist t h) :
    lifecyclePrecedence t (lifecycleNextMoment t h) := by
  have hnextmem := lifecycle_next_mem t h ht hmem
  change lifecycleAncestor t (lifecycleLeaf h) at hmem
  change lifecycleAncestor (lifecycleNextMoment t h) (lifecycleLeaf h) at hnextmem
  have hgt := lifecycle_next_moment_val_gt t h ht
  have hanc := lifecycle_ancestor_of_shared_future_val_lt hmem hnextmem hgt
  refine ⟨?_, hanc⟩
  intro heq
  have heqval := congrArg Fin.val heq
  omega

theorem lifecycleNextMoment_is_next (t : Node) (h : History)
    (htlt : t.val < 6) (ht : lifecycleMemHist t h) :
    IsNextMoment lifecyclePrecedence lifecycleMemHist t
      (lifecycleNextMoment t h) h := by
  refine ⟨ht, lifecycle_next_mem t h htlt ht,
    lifecycle_next_precedes t h htlt ht, ?_⟩
  intro τ hτ hbetween
  rcases hbetween with ⟨htτ, hτnext⟩
  have hdepth₁ := lifecycle_precedence_depth t τ htτ
  have hdepth₂ := lifecycle_precedence_depth τ (lifecycleNextMoment t h) hτnext
  have hnext := lifecycle_next_depth t h htlt
  omega

set_option maxHeartbeats 1000000 in
-- Exhaustive finite case split across CreditLifecycleFrame moments and histories
theorem lifecycle_ancestor_trans {u v w : Node}
    (huv : lifecycleAncestor u v) (hvw : lifecycleAncestor v w) :
    lifecycleAncestor u w := by
  rw [lifecycleAncestor_iff_by_value] at huv hvw ⊢
  unfold lifecycleAncestorByValue at *
  omega

theorem lifecycle_ancestor_backward_linear {u v w : Node}
    (huw : lifecycleAncestor u w) (hvw : lifecycleAncestor v w) :
    lifecyclePrecedence u v ∨ u = v ∨ lifecyclePrecedence v u := by
  by_cases heq : u = v
  · exact Or.inr (Or.inl heq)
  · by_cases hlt : u.val < v.val
    · exact Or.inl ⟨heq, lifecycle_ancestor_of_shared_future_val_lt huw hvw hlt⟩
    · right
      right
      have hvalneq : u.val ≠ v.val := by
        intro hval
        exact heq (Fin.ext hval)
      have hgt : v.val < u.val := by omega
      exact ⟨fun h => heq h.symm,
        lifecycle_ancestor_of_shared_future_val_lt hvw huw hgt⟩

theorem lifecycle_precedence_trans {u v w : Node}
    (huv : lifecyclePrecedence u v) (hvw : lifecyclePrecedence v w) :
    lifecyclePrecedence u w := by
  have hdepth₁ := lifecycle_precedence_depth u v huv
  have hdepth₂ := lifecycle_precedence_depth v w hvw
  refine ⟨?_, lifecycle_ancestor_trans huv.2 hvw.2⟩
  intro heq
  subst w
  omega

theorem lifecycle_mem_of_precedes {u v : Node} {h : History}
    (huv : lifecyclePrecedence u v) (hv : lifecycleMemHist v h) :
    lifecycleMemHist u h := by
  rcases huv with ⟨_, huv⟩
  exact lifecycle_ancestor_trans huv hv

theorem lifecycle_leaf_mem (h : History) : lifecycleMemHist (lifecycleLeaf h) h := by
  have hall : ∀ h : History, lifecycleMemHist (lifecycleLeaf h) h := by decide
  exact hall h

theorem lifecycle_leaf_mem_iff (h₁ h₂ : History) :
    lifecycleMemHist (lifecycleLeaf h₁) h₂ ↔ h₁ = h₂ := by
  have hall : ∀ h₁ h₂ : History,
      lifecycleMemHist (lifecycleLeaf h₁) h₂ ↔ h₁ = h₂ := by decide
  exact hall h₁ h₂

theorem lifecycle_leaf_no_future (h : History) (u : Node) :
    ¬ lifecyclePrecedence (lifecycleLeaf h) u := by
  have hall : ∀ h : History, ∀ u : Node,
      ¬ lifecyclePrecedence (lifecycleLeaf h) u := by decide
  exact hall h u

theorem lifecycle_mem_eq_or_precedes_leaf (t : Node) (h : History)
    (ht : lifecycleMemHist t h) :
    t = lifecycleLeaf h ∨ lifecyclePrecedence t (lifecycleLeaf h) := by
  have hall : ∀ t : Node, ∀ h : History,
      lifecycleMemHist t h →
      t = lifecycleLeaf h ∨ lifecyclePrecedence t (lifecycleLeaf h) := by decide
  exact hall t h ht

theorem lifecycle_history_linear (h : History) {u v : Node}
    (hu : lifecycleMemHist u h) (hv : lifecycleMemHist v h) :
    lifecyclePrecedence u v ∨ u = v ∨ lifecyclePrecedence v u := by
  exact lifecycle_ancestor_backward_linear hu hv

theorem lifecycle_history_maximal_linear (h : History) :
    IsMaximalLinearChain lifecyclePrecedence {t | lifecycleMemHist t h} := by
  refine ⟨?_, ?_⟩
  · intro u v hu hv
    exact lifecycle_history_linear h hu hv
  · intro s hs hsub t ht
    have hleaf : lifecycleLeaf h ∈ s := hsub (lifecycle_leaf_mem h)
    rcases hs ht hleaf with htl | heq | hlt
    · exact htl.2
    · rw [heq]
      exact lifecycle_leaf_mem h
    · exact (lifecycle_leaf_no_future h t hlt).elim

theorem lifecycle_histories_extensional (h₁ h₂ : History)
    (hsame : ∀ t : Node, lifecycleMemHist t h₁ ↔ lifecycleMemHist t h₂) :
    h₁ = h₂ := by
  apply Fin.ext
  have hmem := (hsame (lifecycleLeaf h₁)).mp (lifecycle_leaf_mem h₁)
  have heq := (lifecycle_leaf_mem_iff h₁ h₂).mp hmem
  exact congrArg Fin.val heq

theorem lifecycle_divergent_futures (t : Node) (h₁ h₂ : History)
    (ht₁ : lifecycleMemHist t h₁) (ht₂ : lifecycleMemHist t h₂)
    (hne : h₁ ≠ h₂) :
    ∃ u v : Node,
      lifecycleMemHist u h₁ ∧ lifecycleMemHist v h₂ ∧
      lifecyclePrecedence t u ∧ lifecyclePrecedence t v ∧
      ¬ lifecyclePrecedence u v ∧ u ≠ v ∧ ¬ lifecyclePrecedence v u := by
  have hterminal₁ := lifecycle_mem_eq_or_precedes_leaf t h₁ ht₁
  have hterminal₂ := lifecycle_mem_eq_or_precedes_leaf t h₂ ht₂
  have ht₁' : lifecyclePrecedence t (lifecycleLeaf h₁) := by
    rcases hterminal₁ with heq | hprec
    · subst t
      exact (hne ((lifecycle_leaf_mem_iff h₁ h₂).mp ht₂)).elim
    · exact hprec
  have ht₂' : lifecyclePrecedence t (lifecycleLeaf h₂) := by
    rcases hterminal₂ with heq | hprec
    · subst t
      exact (hne ((lifecycle_leaf_mem_iff h₂ h₁).mp ht₁).symm).elim
    · exact hprec
  have hleaf_ne : lifecycleLeaf h₁ ≠ lifecycleLeaf h₂ := by
    intro heq
    apply hne
    apply Fin.ext
    have hval := congrArg Fin.val heq
    change h₁.val + 6 = h₂.val + 6 at hval
    omega
  exact ⟨lifecycleLeaf h₁, lifecycleLeaf h₂,
    lifecycle_leaf_mem h₁, lifecycle_leaf_mem h₂,
    ht₁', ht₂', lifecycle_leaf_no_future h₁ (lifecycleLeaf h₂),
    hleaf_ne, lifecycle_leaf_no_future h₂ (lifecycleLeaf h₁)⟩

theorem lifecycle_next_precedes_future {t u : Node} {h : History}
    (hnext : IsNextMoment lifecyclePrecedence lifecycleMemHist t
      (lifecycleNextMoment t h) h)
    (htu : lifecyclePrecedence t u) (hu : lifecycleMemHist u h) :
    lifecycleNextMoment t h = u ∨
      lifecyclePrecedence (lifecycleNextMoment t h) u := by
  rcases hnext with ⟨_, hchild, htc, hno⟩
  rcases (lifecycle_history_maximal_linear h).1 hchild hu with
    hchild_u | heq | hu_child
  · exact Or.inr hchild_u
  · exact Or.inl heq
  · exact (hno u hu ⟨htu, hu_child⟩).elim

theorem lifecycle_next_same_on_shared_future {t u : Node} {h₁ h₂ : History}
    (ht₁ : lifecycleMemHist t h₁) (ht₂ : lifecycleMemHist t h₂)
    (htu : lifecyclePrecedence t u)
    (hu₁ : lifecycleMemHist u h₁) (hu₂ : lifecycleMemHist u h₂) :
    lifecycleNextMoment t h₁ = lifecycleNextMoment t h₂ := by
  let n₁ := lifecycleNextMoment t h₁
  let n₂ := lifecycleNextMoment t h₂
  have htlt := lifecycle_precedence_source_lt_six t u htu
  have hn₁ := lifecycleNextMoment_is_next t h₁ htlt ht₁
  have hn₂ := lifecycleNextMoment_is_next t h₂ htlt ht₂
  have hn₁_future := lifecycle_next_precedes_future hn₁ htu hu₁
  have hn₂_future := lifecycle_next_precedes_future hn₂ htu hu₂
  have hn₁_mem₂ : lifecycleMemHist n₁ h₂ := by
    rcases hn₁_future with heq | hprec
    · change lifecycleMemHist (lifecycleNextMoment t h₁) h₂
      rw [heq]
      exact hu₂
    · exact lifecycle_mem_of_precedes hprec hu₂
  have hn₂_mem₁ : lifecycleMemHist n₂ h₁ := by
    rcases hn₂_future with heq | hprec
    · change lifecycleMemHist (lifecycleNextMoment t h₂) h₁
      rw [heq]
      exact hu₁
    · exact lifecycle_mem_of_precedes hprec hu₁
  rcases hn₁ with ⟨_, hn₁_mem₁, htn₁, hno₁⟩
  rcases hn₂ with ⟨_, hn₂_mem₂, htn₂, hno₂⟩
  rcases lifecycle_history_linear h₁ hn₁_mem₁ hn₂_mem₁ with
    h₁₂ | heq | h₂₁
  · exact (hno₂ n₁ hn₁_mem₂ ⟨htn₁, h₁₂⟩).elim
  · exact heq
  · exact (hno₁ n₂ hn₂_mem₁ ⟨htn₂, h₂₁⟩).elim

theorem lifecycle_next_moment_unique {t u v : Node} {h : History}
    (hu : IsNextMoment lifecyclePrecedence lifecycleMemHist t u h)
    (hv : IsNextMoment lifecyclePrecedence lifecycleMemHist t v h) : u = v := by
  rcases hu with ⟨_, hu, htu, hno⟩
  rcases hv with ⟨_, hv, htv, hno'⟩
  rcases (lifecycle_history_maximal_linear h).1 hu hv with
    h | h | h
  · exact (hno' u hu ⟨htu, h⟩).elim
  · exact h
  · exact (hno v hv ⟨htv, h⟩).elim

theorem lifecycle_next_moment_eq {t t' : Node} {h : History}
    (hnext : IsNextMoment lifecyclePrecedence lifecycleMemHist t t' h)
    (_ht : lifecycleMemHist t h) : t' = lifecycleNextMoment t h := by
  have htlt := lifecycle_precedence_source_lt_six t t' hnext.2.2.1
  exact lifecycle_next_moment_unique hnext
    (lifecycleNextMoment_is_next t h htlt hnext.1)

def lifecycleWitness (t : Node) : History :=
  if ht : t.val ≤ 6 then mainHistory
  else historyByIndex ⟨t.val - 6, by
    have htlt : t.val < 20 := t.isLt
    omega⟩

inductive CreditLifecycleEnd where
  | bundle (b : WorkshopMeans → ℕ)
  | timed (e : CreditLifecycleEnd) (t : Node)
  | quantity (m : WorkshopMeans) (q : ℕ)
  deriving DecidableEq

def creditLifecycleRequirement (e : CreditLifecycleEnd) (m : WorkshopMeans) : ℕ :=
  match e with
  | .quantity good q => if good = m then q else 0
  | _ => 0

def creditLifecycleValuedEnd (i : WorkshopAgent) (t : Node)
    (_h : History) (e : CreditLifecycleEnd) : Prop :=
  match e with
  | .quantity good q =>
      (i = .operator ∧ t.val = 0 ∧ good = creditLifecycleMoney ∧ q = 2) ∨
      (i = .operator ∧ t.val = 1 ∧ good = creditLifecycleCollateral ∧ q = 1) ∨
      (i = .entrepreneur ∧ t.val = 1 ∧ good = creditLifecycleMoney ∧ q = 3) ∨
      (i = .operator ∧ t.val = 2 ∧ good = creditLifecycleCollateral ∧ q = 2) ∨
      (i = .customer ∧ t.val = 2 ∧ good = creditLifecycleMoney ∧ q = 3) ∨
      (i = .entrepreneur ∧ t.val = 4 ∧ good = creditLifecycleCollateral ∧ q = 1) ∨
      (i = .operator ∧ t.val = 4 ∧ good = creditLifecycleMoney ∧ q = 2) ∨
      (i = .customer ∧ t.val = 5 ∧ good = creditLifecycleCollateral ∧ q = 1) ∨
      (i = .operator ∧ t.val = 5 ∧ good = creditLifecycleMoney ∧ q = 4)
  | _ => False

def creditLifecycleOutcome (i : WorkshopAgent) (_α : WorkshopAction)
    (_t τ : Node) (h : History) : CreditLifecycleEnd :=
  .bundle (lifecycleOmega i τ h)

def creditLifecyclePreference (i : WorkshopAgent) (t : Node) (h : History)
    (e₁ e₂ : CreditLifecycleEnd) : Prop :=
  match e₁, e₂ with
  | .bundle b₁, .bundle b₂ =>
      SubjectiveTeleologicalDominates creditLifecycleRequirement
        (creditLifecycleValuedEnd i t h) b₁ b₂
  | _, _ => False

def creditLifecycleMaturation (_i : WorkshopAgent) (_α : WorkshopAction)
    (t : Node) (h : History) : Node := lifecycleNextMoment t h

def creditLifecycleEnd (i : WorkshopAgent) (α : WorkshopAction) (t : Node)
    (_h : History) : CreditLifecycleEnd :=
  let selected := lifecycleSigma i t α (lifecycleWitness t)
  creditLifecycleOutcome i α t (creditLifecycleMaturation i α t selected) selected

/-- Trade actions are exactly the two matched-contract constructors. -/
def creditLifecycleTradeAction (α : WorkshopAction) : Prop :=
  (∃ i j qA mA qB mB,
    α = WorkshopAction.offer i j qA mA qB mB) ∨
  (∃ j i qA mA qB mB,
    α = WorkshopAction.accept j i qA mA qB mB)

theorem lifecycle_enacted_ne_inactive_actions :
    ∀ i t h, lifecycleEnacted i t h ≠ .proposeScope ∧
      lifecycleEnacted i t h ≠ .acceptScope ∧
      lifecycleEnacted i t h ≠ .refuseScope ∧
      lifecycleEnacted i t h ≠ .instruct0 ∧
      lifecycleEnacted i t h ≠ .instruct1 ∧
      lifecycleEnacted i t h ≠ .produceIntermediate1 := by
  decide

theorem lifecycle_idle_balance_transition :
    ∀ i t h m, lifecycleEnacted i t h = .idle →
      lifecycleOmega i (lifecycleNextMoment t h) h m =
        lifecycleOmega i t h m := by
  decide

def isOfferFromTo (α : WorkshopAction) (i j : WorkshopAgent) : Bool :=
  match α with
  | .offer i' j' _ _ _ _ => i' == i && j' == j
  | _ => false

def isAcceptFromTo (α : WorkshopAction) (j i : WorkshopAgent) : Bool :=
  match α with
  | .accept j' i' _ _ _ _ => j' == j && i' == i
  | _ => false

def isMatchingTrade (α β : WorkshopAction) (i j : WorkshopAgent) : Bool :=
  match α, β with
  | .offer i1 j1 qA1 mA1 qB1 mB1, .accept j2 i2 qA2 mA2 qB2 mB2 =>
      i1 == i && j1 == j && j2 == j && i2 == i &&
      qA1 == qA2 && mA1 == mA2 && qB1 == qB2 && mB1 == mB2
  | _, _ => false

theorem matchingTrade_implies_accept {i j : WorkshopAgent} {qA : ℕ} {mA : WorkshopMeans}
    {qB : ℕ} {mB : WorkshopMeans} {β : WorkshopAction} :
    isMatchingTrade (.offer i j qA mA qB mB) β i j →
    β = .accept j i qA mA qB mB := by
  cases β with
  | accept j2 i2 qA2 mA2 qB2 mB2 =>
      dsimp [isMatchingTrade]
      simp only [beq_iff_eq, Bool.and_eq_true, beq_self_eq_true, true_and]
      rintro ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      rfl
  | _ => intro h; contradiction

theorem matchingTrade_implies_offer {i j : WorkshopAgent} {qA : ℕ} {mA : WorkshopMeans}
    {qB : ℕ} {mB : WorkshopMeans} {α : WorkshopAction} :
    isMatchingTrade α (.accept j i qA mA qB mB) i j →
    α = .offer i j qA mA qB mB := by
  cases α with
  | offer i1 j1 qA1 mA1 qB1 mB1 =>
      dsimp [isMatchingTrade]
      simp only [beq_iff_eq, Bool.and_eq_true, beq_self_eq_true, and_true]
      rintro ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      rfl
  | _ => intro h; contradiction

theorem lifecycle_trade_balance_transition :
    ∀ i j t h m,
      isMatchingTrade (lifecycleEnacted i t h) (lifecycleEnacted j t h) i j →
      lifecycleOmega i (lifecycleNextMoment t h) h m +
          creditLifecycleUseMeans (lifecycleEnacted i t h) m =
        lifecycleOmega i t h m +
          creditLifecycleYieldMeans (lifecycleEnacted i t h) m := by
  decide

theorem lifecycle_trade_acceptor_balance_transition :
    ∀ i j t h m,
      isMatchingTrade (lifecycleEnacted i t h) (lifecycleEnacted j t h) i j →
      lifecycleOmega j (lifecycleNextMoment t h) h m +
          creditLifecycleUseMeans (lifecycleEnacted j t h) m =
        lifecycleOmega j t h m +
          creditLifecycleYieldMeans (lifecycleEnacted j t h) m := by
  decide

theorem lifecycle_unilateral_offer_balance_transition :
    ∀ i j t h m,
      isOfferFromTo (lifecycleEnacted i t h) i j →
      ¬ isMatchingTrade (lifecycleEnacted i t h) (lifecycleEnacted j t h) i j →
      lifecycleOmega i (lifecycleNextMoment t h) h m =
        lifecycleOmega i t h m := by
  decide

theorem lifecycle_unilateral_accept_balance_transition :
    ∀ j i t h m,
      isAcceptFromTo (lifecycleEnacted j t h) j i →
      ¬ isMatchingTrade (lifecycleEnacted i t h) (lifecycleEnacted j t h) i j →
      lifecycleOmega j (lifecycleNextMoment t h) h m =
        lifecycleOmega j t h m := by
  decide

theorem lifecycle_expected_maturation_mem_future (t : Node) (h : History)
    (ht : lifecycleMemHist t h) :
    lifecycleMemHist (lifecycleNextMoment t h) h ∧
    (t = lifecycleNextMoment t h ∨ lifecyclePrecedence t (lifecycleNextMoment t h)) := by
  have hall : ∀ t h, lifecycleMemHist t h →
      lifecycleMemHist (lifecycleNextMoment t h) h ∧
      (t = lifecycleNextMoment t h ∨ lifecyclePrecedence t (lifecycleNextMoment t h)) := by
    decide
  exact hall t h ht

theorem lifecycle_issue_balance_transition :
    ∀ i t h m, lifecycleEnacted i t h = .produceIntermediate0 →
      lifecycleOmega i (lifecycleNextMoment t h) h m +
          creditLifecycleUseMeans .produceIntermediate0 m =
        lifecycleOmega i t h m +
          creditLifecycleYieldMeans .produceIntermediate0 m := by
  decide

@[instance_reducible]
def creditLifecycleActionFrame : ActionFrame := by
  exact {
    Agent := WorkshopAgent
    Moment := Node
    History := History
    Action := WorkshopAction
    Means := WorkshopMeans
    Ends := CreditLifecycleEnd
    alpha_zero := .idle
    Precedence := lifecyclePrecedence
    moment_lt_irrefl := by
      intro t ht
      exact ht.1 rfl
    moment_lt_trans := by
      intro t₁ t₂ t₃ h₁ h₂
      exact lifecycle_precedence_trans h₁ h₂
    backward_linearity := by
      intro t₁ t₂ t₃ h₁ h₂
      exact lifecycle_ancestor_backward_linear h₁.2 h₂.2
    mem_hist := lifecycleMemHist
    moment_in_history := by
      intro t
      have hall : ∀ t : Node, ∃ h : History, lifecycleMemHist t h := by decide
      exact hall t
    histories_maximal_linear := by
      intro h
      exact lifecycle_history_maximal_linear h
    histories_extensional := by
      intro h₁ h₂ hsame
      exact lifecycle_histories_extensional h₁ h₂ hsame
    divergent_futures_witness := by
      intro t h₁ h₂ ht₁ ht₂ hne
      exact lifecycle_divergent_futures t h₁ h₂ ht₁ ht₂ hne
    A_cont := fun i t _ => creditLifecycleActionsAt i t
    A_cont_bundle_invariant := by intro _ _ _ _ _ _; rfl
    alpha_zero_cont := by
      intro i t h
      simp [creditLifecycleActionsAt, eventMenu]
    omega := lifecycleOmega
    omega_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
    use_means := creditLifecycleUseMeans
    yield_means := creditLifecycleYieldMeans
    use_means_alpha_zero := by intro m; rfl
    yield_means_alpha_zero := by intro m; rfl
    A_feas := fun i t _ => creditLifecycleActionsAt i t
    A_feas_coupling := by
      intro i t h α
      constructor
      · intro hα
        exact ⟨hα, creditLifecycle_use_feasible i t h α hα⟩
      · intro hα
        exact hα.1
    enacted := lifecycleEnacted
    enacted_in_A_feas := by
      intro i t h ht
      change lifecycleEnacted i t h ∈ eventMenu (creditLifecycleChoice i t)
      rcases lifecycle_enacted_in_menu i t h with hIdle | hChoice
      · simp [eventMenu, hIdle]
      · simp [eventMenu, hChoice]
    no_choice_between_undivided := by
      intro i t u h₁ h₂ ht₁ ht₂ htu hu₁ hu₂
      have hnext := lifecycle_next_same_on_shared_future ht₁ ht₂ htu hu₁ hu₂
      exact congrArg (lifecycleEnactedByNext i t) hnext
    sigma := lifecycleSigma
    sigma_realization := by
      intro i t h h' α ht hα hh'
      change α ∈ creditLifecycleActionsAt i t at hα
      rcases eventMenu_mem_cases hα with hIdle | hChoice
      · subst α
        exact lifecycle_sigma_realizes_idle i t h' hh'
      · subst α
        exact lifecycle_sigma_realizes_choice i t h' hh'
    sigma_centering := by
      intro i t h α ht hα
      simp [lifecycleSigma, hα]
    sigma_co_agency := by
      intro i j t h h' α hij ht hα hh'
      change α ∈ creditLifecycleActionsAt i t at hα
      rcases eventMenu_mem_cases hα with hIdle | hChoice
      · subst α
        exact lifecycle_sigma_co_agency_idle i j t h' hij hh'
      · subst α
        exact lifecycle_sigma_co_agency_choice i j t h' hij hh'
    Offer := WorkshopAction.offer
    Accept := WorkshopAction.accept
    offer_inj := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact WorkshopAction.offer.inj h
    accept_inj := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact WorkshopAction.accept.inj h
    offer_ne_accept := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
    alpha_zero_ne_offer := by intro _ _ _ _ _ _ h; cases h
    alpha_zero_ne_accept := by intro _ _ _ _ _ _ h; cases h
    use_means_offer := by intro _ _ _ _ _ _ _; rfl
    yield_means_offer := by intro _ _ _ _ _ _ _; rfl
    use_means_accept := by intro _ _ _ _ _ _ _; rfl
    yield_means_accept := by intro _ _ _ _ _ _ _; rfl
    IsTradeAction := creditLifecycleTradeAction
    is_trade_action_def := by intro α; rfl
    law_in_re_transition := by
      intro i t t' h α m hnot hα hnext
      rw [lifecycle_next_moment_eq hnext hnext.1]
      cases α with
      | idle =>
          simp only [creditLifecycleUseMeans, creditLifecycleYieldMeans]
          exact lifecycle_idle_balance_transition i t h m hα
      | proposeScope => exact (lifecycle_enacted_ne_inactive_actions i t h).1 hα |>.elim
      | acceptScope => exact (lifecycle_enacted_ne_inactive_actions i t h).2.1 hα |>.elim
      | refuseScope => exact (lifecycle_enacted_ne_inactive_actions i t h).2.2.1 hα |>.elim
      | instruct0 => exact (lifecycle_enacted_ne_inactive_actions i t h).2.2.2.1 hα |>.elim
      | instruct1 => exact (lifecycle_enacted_ne_inactive_actions i t h).2.2.2.2.1 hα |>.elim
      | produceIntermediate0 =>
          exact lifecycle_issue_balance_transition i t h m hα
      | produceIntermediate1 =>
          exact (lifecycle_enacted_ne_inactive_actions i t h).2.2.2.2.2 hα |>.elim
      | offer issuer borrower qA goodA qB goodB =>
          exact (hnot (Or.inl ⟨issuer, borrower, qA, goodA, qB, goodB, rfl⟩)).elim
      | accept borrower issuer qA goodA qB goodB =>
          exact (hnot (Or.inr ⟨borrower, issuer, qA, goodA, qB, goodB, rfl⟩)).elim
    unilateral_offer_noop := by
      intro i j qA mA qB mB t t' h m h_offer h_not_accept hnext
      rw [lifecycle_next_moment_eq hnext hnext.1]
      have hIsOffer : isOfferFromTo (lifecycleEnacted i t h) i j = true := by
        rw [h_offer]
        dsimp [isOfferFromTo]
        simp only [beq_self_eq_true, Bool.and_self]
      have hNotMatched :
          ¬ isMatchingTrade (lifecycleEnacted i t h) (lifecycleEnacted j t h) i j = true := by
        intro hMatched
        rw [h_offer] at hMatched
        have hAccept := matchingTrade_implies_accept hMatched
        exact h_not_accept hAccept
      exact lifecycle_unilateral_offer_balance_transition i j t h m hIsOffer hNotMatched
    unilateral_accept_noop := by
      intro j i qA mA qB mB t t' h m h_accept h_not_offer hnext
      rw [lifecycle_next_moment_eq hnext hnext.1]
      have hIsAccept : isAcceptFromTo (lifecycleEnacted j t h) j i = true := by
        rw [h_accept]
        dsimp [isAcceptFromTo]
        simp only [beq_self_eq_true, Bool.and_self]
      have hNotMatched :
          ¬ isMatchingTrade (lifecycleEnacted i t h) (lifecycleEnacted j t h) i j = true := by
        intro hMatched
        rw [h_accept] at hMatched
        have hOffer := matchingTrade_implies_offer hMatched
        exact h_not_offer hOffer
      exact lifecycle_unilateral_accept_balance_transition j i t h m hIsAccept hNotMatched
    bilateral_transfer_law := by
      intro i j qA mA qB mB t t' h m hij h_offer h_accept hnext
      rw [lifecycle_next_moment_eq hnext hnext.1]
      have hMatched :
          isMatchingTrade (lifecycleEnacted i t h) (lifecycleEnacted j t h) i j = true := by
        rw [h_offer, h_accept]
        dsimp [isMatchingTrade]
        simp only [beq_self_eq_true, Bool.and_self]
      have h1 := lifecycle_trade_balance_transition i j t h m hMatched
      have h2 := lifecycle_trade_acceptor_balance_transition i j t h m hMatched
      rw [h_offer] at h1
      rw [h_accept] at h2
      dsimp only [creditLifecycleUseMeans, creditLifecycleYieldMeans] at h1 h2
      exact ⟨h1, h2⟩
    MinPlausible := fun _ t => {lifecycleWitness t}
    min_plausible_nonempty := by
      intro i t
      exact ⟨lifecycleWitness t, Set.mem_singleton _⟩
    tau := fun _ t _ => t
    min_plausible_node_incidence := by
      intro i t h' hh'
      have heq : h' = lifecycleWitness t := Set.mem_singleton_iff.mp hh'
      subst h'
      fin_cases t <;> decide
    tau_centering := by intro _ _ _ _; rfl
    requirement := creditLifecycleRequirement
    ValuedEnd := creditLifecycleValuedEnd
    valued_end_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
    OutcomeOf := creditLifecycleOutcome
    ExpectedMaturation := creditLifecycleMaturation
    expected_maturation_mem_future := by
      intro i α t h ht _
      exact lifecycle_expected_maturation_mem_future t h ht
    End_of := creditLifecycleEnd
    End_of_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
    Preference := creditLifecyclePreference
    Preference_bundle_invariant := by intro _ _ _ _ _ _; rfl
    pref_asymm := by
      intro i t h e₁ e₂ h₁₂ h₂₁
      cases e₁ <;> cases e₂ <;>
        simp only [creditLifecyclePreference] at h₁₂ h₂₁
      rcases h₁₂ with ⟨_, ⟨S, hS, h_att, h_not⟩⟩
      exact h_not (h₂₁.1 S hS h_att)
    doxastic_sure_thing_bridge := by
      intro i α β t h _ _ hstrict
      rcases hstrict with ⟨h', hh', hpref⟩
      have heq : h' = lifecycleWitness t := Set.mem_singleton_iff.mp hh'
      subst h'
      simpa [creditLifecycleEnd, creditLifecycleOutcome,
        creditLifecycleMaturation] using hpref
    doxastic_plausible_support := by
      intro i α β t h _ hpref
      refine ⟨lifecycleWitness t, Set.mem_singleton _, ?_⟩
      simpa [creditLifecycleEnd, creditLifecycleOutcome,
        creditLifecycleMaturation] using hpref
    BundleEnd := CreditLifecycleEnd.bundle
    teleological_bundle_dominance_induces_preference := by
      intro i t h b₁ b₂ hdom
      exact hdom
    TimedEnd := CreditLifecycleEnd.timed
    QuantityEnd := CreditLifecycleEnd.quantity
    timed_end_inj := by intro _ _ _ _ h; exact CreditLifecycleEnd.timed.inj h
    quantity_end_inj := by intro _ _ _ _ h; exact CreditLifecycleEnd.quantity.inj h
  }

/-- A concrete one-unit collateralized loan in the finite lifecycle frame.
The loan terms are read from the already enacted advance and repayment events. -/
def entrepreneurLoanTerms : PawnLoanTerms creditLifecycleActionFrame where
  lender := .operator
  borrower := .entrepreneur
  money := creditLifecycleMoney
  collateral := creditLifecycleCollateral
  principal := 1
  promisedRepayment := 2
  collateralQuantity := 1
  maturity := maturityMoment
  distinctAgents := by decide
  distinctGoods := by decide
  principalPositive := by decide
  collateralPositive := by decide

local instance : ActionFrame := creditLifecycleActionFrame

def entrepreneurAdvanceOutsideOption : WorkshopMeans → ℕ :=
  lifecycleOmega .entrepreneur (lifecycleLeaf (historyByIndex 3)) (historyByIndex 3)

def operatorAdvanceOutsideOption : WorkshopMeans → ℕ :=
  lifecycleOmega .operator (lifecycleLeaf (historyByIndex 2)) (historyByIndex 2)

/-- The operator's enacted advance outcome is the post-transfer inventory on
the main history. -/
theorem entrepreneur_advance_operator_end :
    creditLifecycleEnd .operator firstAdvanceOffer firstAdvanceMoment mainHistory =
      .bundle (lifecycleOmega .operator secondAdvanceMoment mainHistory) := by
  have hsigma : lifecycleSigma .operator firstAdvanceMoment firstAdvanceOffer
      (lifecycleWitness firstAdvanceMoment) = mainHistory := by decide
  unfold creditLifecycleEnd
  rw [hsigma]
  simp [creditLifecycleOutcome, creditLifecycleMaturation,
    lifecycleNextMoment, mainHistory, historyByIndex,
    firstAdvanceMoment, secondAdvanceMoment, mainMoment]

/-- The operator's no-offer outcome leaves the actual entrepreneur's
acceptance unmatched on the corresponding finite history. -/
theorem entrepreneur_advance_operator_idle_end :
    creditLifecycleEnd .operator .idle firstAdvanceMoment mainHistory =
      .bundle operatorAdvanceOutsideOption := by
  have hsigma : lifecycleSigma .operator firstAdvanceMoment .idle
      (lifecycleWitness firstAdvanceMoment) = historyByIndex 2 := by decide
  unfold creditLifecycleEnd
  rw [hsigma]
  simp [creditLifecycleOutcome, creditLifecycleMaturation,
    operatorAdvanceOutsideOption, lifecycleNextMoment, lifecycleLeaf,
    historyByIndex, firstAdvanceMoment, mainMoment]

/-- The entrepreneur's accepted advance outcome is the post-transfer
inventory on the main history. -/
theorem entrepreneur_advance_borrower_end :
    creditLifecycleEnd .entrepreneur firstAdvanceAccept firstAdvanceMoment mainHistory =
      .bundle (lifecycleOmega .entrepreneur secondAdvanceMoment mainHistory) := by
  have hsigma : lifecycleSigma .entrepreneur firstAdvanceMoment firstAdvanceAccept
      (lifecycleWitness firstAdvanceMoment) = mainHistory := by decide
  unfold creditLifecycleEnd
  rw [hsigma]
  simp [creditLifecycleOutcome, creditLifecycleMaturation,
    lifecycleNextMoment, mainHistory, historyByIndex,
    firstAdvanceMoment, secondAdvanceMoment, mainMoment]

/-- The entrepreneur's no-acceptance outcome leaves the operator's advance
offer unmatched on the corresponding finite history. -/
theorem entrepreneur_advance_borrower_idle_end :
    creditLifecycleEnd .entrepreneur .idle firstAdvanceMoment mainHistory =
      .bundle entrepreneurAdvanceOutsideOption := by
  have hsigma : lifecycleSigma .entrepreneur firstAdvanceMoment .idle
      (lifecycleWitness firstAdvanceMoment) = historyByIndex 3 := by decide
  unfold creditLifecycleEnd
  rw [hsigma]
  simp [creditLifecycleOutcome, creditLifecycleMaturation,
    entrepreneurAdvanceOutsideOption, lifecycleNextMoment, lifecycleLeaf,
    historyByIndex, firstAdvanceMoment, mainMoment]

/-- Under the frame's stated preference relation, the operator prefers the
actual advance because it attains the valued collateral end absent at idling. -/
theorem operator_prefers_collateralized_advance :
    creditLifecyclePreference .operator firstAdvanceMoment mainHistory
      (creditLifecycleEnd .operator firstAdvanceOffer firstAdvanceMoment mainHistory)
      (creditLifecycleEnd .operator .idle firstAdvanceMoment mainHistory) := by
  rw [entrepreneur_advance_operator_end, entrepreneur_advance_operator_idle_end]
  change SubjectiveTeleologicalDominates creditLifecycleRequirement
    (creditLifecycleValuedEnd .operator firstAdvanceMoment mainHistory)
    (lifecycleOmega .operator secondAdvanceMoment mainHistory)
    operatorAdvanceOutsideOption
  apply subjective_teleological_dominates_of_unique_valued_end
    creditLifecycleRequirement
    (creditLifecycleValuedEnd .operator firstAdvanceMoment mainHistory)
    (.quantity creditLifecycleCollateral 1)
    (lifecycleOmega .operator secondAdvanceMoment mainHistory)
    operatorAdvanceOutsideOption
  · intro e' he'
    cases e' with
    | bundle b => simp [creditLifecycleValuedEnd] at he'
    | timed e t => simp [creditLifecycleValuedEnd] at he'
    | quantity good q =>
        have hvalues : good = creditLifecycleCollateral ∧ q = 1 := by
          simpa [creditLifecycleValuedEnd, firstAdvanceMoment, mainMoment,
            creditLifecycleMoney, creditLifecycleCollateral] using he'
        rcases hvalues with ⟨rfl, rfl⟩
        rfl
  · simp [creditLifecycleValuedEnd, firstAdvanceMoment, mainMoment,
      creditLifecycleCollateral]
  · intro m
    by_cases hm : m = creditLifecycleCollateral
    · subst m
      norm_num [JointlyAttains, creditLifecycleRequirement, lifecycleOmega,
        lifecycleBalance, lifecycleBaseStage, secondAdvanceMoment, mainMoment]
    · have hmc : creditLifecycleCollateral ≠ m := fun he => hm he.symm
      simp [creditLifecycleRequirement, hmc]
  · intro h
    have hc := h creditLifecycleCollateral
    norm_num [JointlyAttains, creditLifecycleRequirement, operatorAdvanceOutsideOption,
      lifecycleOmega, lifecycleBalance, lifecycleBaseStage, lifecycleLeaf,
      historyByIndex, creditLifecycleCollateral] at hc
    norm_num [creditLifecycleMoney, creditLifecycleCollateral,
      tokenMeans, rawMeans] at hc

/-- Under the same preference relation, the entrepreneur accepts because the
advance attains the valued three-unit money end absent at idling. -/
theorem entrepreneur_prefers_advance :
    creditLifecyclePreference .entrepreneur firstAdvanceMoment mainHistory
      (creditLifecycleEnd .entrepreneur firstAdvanceAccept firstAdvanceMoment mainHistory)
      (creditLifecycleEnd .entrepreneur .idle firstAdvanceMoment mainHistory) := by
  rw [entrepreneur_advance_borrower_end, entrepreneur_advance_borrower_idle_end]
  change SubjectiveTeleologicalDominates creditLifecycleRequirement
    (creditLifecycleValuedEnd .entrepreneur firstAdvanceMoment mainHistory)
    (lifecycleOmega .entrepreneur secondAdvanceMoment mainHistory)
    entrepreneurAdvanceOutsideOption
  apply subjective_teleological_dominates_of_unique_valued_end
    creditLifecycleRequirement
    (creditLifecycleValuedEnd .entrepreneur firstAdvanceMoment mainHistory)
    (.quantity creditLifecycleMoney 3)
    (lifecycleOmega .entrepreneur secondAdvanceMoment mainHistory)
    entrepreneurAdvanceOutsideOption
  · intro e' he'
    cases e' with
    | bundle b => simp [creditLifecycleValuedEnd] at he'
    | timed e t => simp [creditLifecycleValuedEnd] at he'
    | quantity good q =>
        have hvalues : good = creditLifecycleMoney ∧ q = 3 := by
          simpa [creditLifecycleValuedEnd, firstAdvanceMoment, mainMoment,
            creditLifecycleMoney, creditLifecycleCollateral] using he'
        rcases hvalues with ⟨rfl, rfl⟩
        rfl
  · simp [creditLifecycleValuedEnd, firstAdvanceMoment, mainMoment,
      creditLifecycleMoney]
  · intro m
    by_cases hm : m = creditLifecycleMoney
    · subst m
      norm_num [JointlyAttains, creditLifecycleRequirement, lifecycleOmega,
        lifecycleBalance, lifecycleBaseStage, secondAdvanceMoment, mainMoment]
    · have hmc : creditLifecycleMoney ≠ m := fun he => hm he.symm
      simp [creditLifecycleRequirement, hmc]
  · intro h
    have hc := h creditLifecycleMoney
    norm_num [JointlyAttains, creditLifecycleRequirement, entrepreneurAdvanceOutsideOption,
      lifecycleOmega, lifecycleBalance, lifecycleBaseStage, lifecycleLeaf,
      historyByIndex, creditLifecycleMoney] at hc

/-- The finite ActionFrame menus contain only inaction and the specified
advance for each participant at this decision node. -/
theorem operator_advance_menu (β : WorkshopAction)
    (hβ : β ∈ A_feas .operator firstAdvanceMoment mainHistory) :
    β = alpha_zero ∨ β = firstAdvanceOffer := by
  have hcont : β ∈ A_cont .operator firstAdvanceMoment mainHistory :=
    (creditLifecycleActionFrame.A_feas_coupling
      WorkshopAgent.operator firstAdvanceMoment mainHistory β).mp hβ |>.1
  change β ∈ creditLifecycleActionsAt .operator firstAdvanceMoment at hcont
  rcases eventMenu_mem_cases hcont with hIdle | hOffer
  · exact Or.inl hIdle
  · right
    simpa [creditLifecycleChoice, firstAdvanceMoment, mainMoment,
      firstAdvanceOffer, creditLifecycleMoney, creditLifecycleCollateral] using hOffer

theorem entrepreneur_advance_menu (β : WorkshopAction)
    (hβ : β ∈ A_feas .entrepreneur firstAdvanceMoment mainHistory) :
    β = alpha_zero ∨ β = firstAdvanceAccept := by
  have hcont : β ∈ A_cont .entrepreneur firstAdvanceMoment mainHistory :=
    (creditLifecycleActionFrame.A_feas_coupling
      WorkshopAgent.entrepreneur firstAdvanceMoment mainHistory β).mp hβ |>.1
  change β ∈ creditLifecycleActionsAt .entrepreneur firstAdvanceMoment at hcont
  rcases eventMenu_mem_cases hcont with hIdle | hAccept
  · exact Or.inl hIdle
  · right
    simpa [creditLifecycleChoice, firstAdvanceMoment, mainMoment,
      firstAdvanceAccept, creditLifecycleMoney, creditLifecycleCollateral] using hAccept

theorem operator_advance_purposeful :
    PurposefulAct .operator firstAdvanceMoment mainHistory firstAdvanceOffer := by
  have hpref := operator_prefers_collateralized_advance
  have hfeasible : firstAdvanceOffer ∈ A_feas .operator firstAdvanceMoment mainHistory := by
    decide
  have hexec : Exec WorkshopAgent.operator firstAdvanceMoment
      firstAdvanceOffer mainHistory := by
    unfold Exec ChoicePartition
    change creditLifecycleActionFrame.mem_hist firstAdvanceMoment mainHistory ∧
      lifecycleEnacted WorkshopAgent.operator firstAdvanceMoment mainHistory = firstAdvanceOffer
    constructor
    · change lifecycleMemHist firstAdvanceMoment mainHistory
      decide
    · decide
  refine ⟨hfeasible, hexec, Or.inr hpref, ?_⟩
  intro β hβ hreverse
  rcases operator_advance_menu β hβ with hidle | hoff
  · rw [hidle] at hreverse
    exact (pref_asymm WorkshopAgent.operator firstAdvanceMoment mainHistory hpref hreverse).elim
  · subst β
    exact (pref_irrefl WorkshopAgent.operator firstAdvanceMoment mainHistory _ hreverse).elim

theorem entrepreneur_accept_purposeful :
    PurposefulAct .entrepreneur firstAdvanceMoment mainHistory firstAdvanceAccept := by
  have hpref := entrepreneur_prefers_advance
  have hfeasible : firstAdvanceAccept ∈ A_feas .entrepreneur firstAdvanceMoment mainHistory := by
    decide
  have hexec : Exec WorkshopAgent.entrepreneur firstAdvanceMoment
      firstAdvanceAccept mainHistory := by
    unfold Exec ChoicePartition
    change creditLifecycleActionFrame.mem_hist firstAdvanceMoment mainHistory ∧
      lifecycleEnacted WorkshopAgent.entrepreneur
        firstAdvanceMoment mainHistory = firstAdvanceAccept
    constructor
    · change lifecycleMemHist firstAdvanceMoment mainHistory
      decide
    · decide
  refine ⟨hfeasible, hexec, Or.inr hpref, ?_⟩
  intro β hβ hreverse
  rcases entrepreneur_advance_menu β hβ with hidle | haccept
  · rw [hidle] at hreverse
    exact (pref_asymm WorkshopAgent.entrepreneur firstAdvanceMoment mainHistory hpref hreverse).elim
  · subst β
    exact (pref_irrefl WorkshopAgent.entrepreneur firstAdvanceMoment mainHistory _ hreverse).elim

/-- The concrete advance is the generic purposeful bilateral exchange already
present in the frame's event table. -/
theorem entrepreneurAdvance_is_bilateral_exchange :
    BilateralExchange .operator .entrepreneur firstAdvanceMoment mainHistory
      1 creditLifecycleMoney 1 creditLifecycleCollateral := by
  exact ricardian_bilateral_exchange_purposeful WorkshopAgent.operator WorkshopAgent.entrepreneur
    firstAdvanceMoment mainHistory creditLifecycleMoney creditLifecycleCollateral
    1 1 (by decide) (by decide) operator_advance_purposeful (by decide)
    entrepreneur_accept_purposeful (by decide)

/-- The frame's actual first advance satisfies the generic loan-advance
interface, including strict ordering before the frame's maturity node. -/
def entrepreneurCreditAdvance : CreditAdvance entrepreneurLoanTerms where
  history := mainHistory
  moment := firstAdvanceMoment
  nextMoment := secondAdvanceMoment
  successor := by
    change IsNextMoment lifecyclePrecedence lifecycleMemHist
      firstAdvanceMoment secondAdvanceMoment mainHistory
    exact lifecycleNextMoment_is_next firstAdvanceMoment mainHistory (by decide) (by decide)
  advanceBeforeMaturity := by
    change lifecyclePrecedence secondAdvanceMoment maturityMoment
    decide
  maturityOnHistory := by
    change lifecycleMemHist maturityMoment mainHistory
    decide
  purposefulExchange := entrepreneurAdvance_is_bilateral_exchange

def operatorRepaymentOutsideOption : WorkshopMeans → ℕ :=
  lifecycleOmega .operator (lifecycleLeaf (historyByIndex 9)) (historyByIndex 9)

def entrepreneurRepaymentOutsideOption : WorkshopMeans → ℕ :=
  lifecycleOmega .entrepreneur (lifecycleLeaf (historyByIndex 8)) (historyByIndex 8)

/-- The entrepreneur's matched repayment outcome is the post-transfer
inventory on the main history. -/
theorem entrepreneur_repayment_end :
    creditLifecycleEnd .entrepreneur firstRepaymentOffer firstRepaymentMoment mainHistory =
      .bundle (lifecycleOmega .entrepreneur secondRepaymentMoment mainHistory) := by
  have hsigma : lifecycleSigma .entrepreneur firstRepaymentMoment firstRepaymentOffer
      (lifecycleWitness firstRepaymentMoment) = mainHistory := by decide
  unfold creditLifecycleEnd
  rw [hsigma]
  simp [creditLifecycleOutcome, creditLifecycleMaturation, lifecycleNextMoment,
    firstRepaymentMoment, secondRepaymentMoment, mainHistory, historyByIndex, mainMoment]

/-- The lender's matched repayment outcome is the post-transfer inventory on
the main history. -/
theorem operator_repayment_end :
    creditLifecycleEnd .operator firstRepaymentAccept firstRepaymentMoment mainHistory =
      .bundle (lifecycleOmega .operator secondRepaymentMoment mainHistory) := by
  have hsigma : lifecycleSigma .operator firstRepaymentMoment firstRepaymentAccept
      (lifecycleWitness firstRepaymentMoment) = mainHistory := by decide
  unfold creditLifecycleEnd
  rw [hsigma]
  simp [creditLifecycleOutcome, creditLifecycleMaturation, lifecycleNextMoment,
    firstRepaymentMoment, secondRepaymentMoment, mainHistory, historyByIndex, mainMoment]

/-- Without the entrepreneur's offer, the operator's acceptance is unmatched. -/
theorem entrepreneur_repayment_idle_end :
    creditLifecycleEnd .entrepreneur .idle firstRepaymentMoment mainHistory =
      .bundle entrepreneurRepaymentOutsideOption := by
  have hsigma : lifecycleSigma .entrepreneur firstRepaymentMoment .idle
      (lifecycleWitness firstRepaymentMoment) = historyByIndex 8 := by decide
  unfold creditLifecycleEnd
  rw [hsigma]
  simp [creditLifecycleOutcome, creditLifecycleMaturation,
    entrepreneurRepaymentOutsideOption, lifecycleNextMoment, lifecycleLeaf,
    historyByIndex, firstRepaymentMoment, mainMoment]

/-- Without the lender's acceptance, the entrepreneur's offer is unmatched. -/
theorem operator_repayment_idle_end :
    creditLifecycleEnd .operator .idle firstRepaymentMoment mainHistory =
      .bundle operatorRepaymentOutsideOption := by
  have hsigma : lifecycleSigma .operator firstRepaymentMoment .idle
      (lifecycleWitness firstRepaymentMoment) = historyByIndex 9 := by decide
  unfold creditLifecycleEnd
  rw [hsigma]
  simp [creditLifecycleOutcome, creditLifecycleMaturation,
    operatorRepaymentOutsideOption, lifecycleNextMoment, lifecycleLeaf,
    historyByIndex, firstRepaymentMoment, mainMoment]

/-- The entrepreneur offers the repayment to regain the valued collateral end;
the unmatched-offer outcome does not attain it. -/
theorem borrower_prefers_repayment :
    creditLifecyclePreference .entrepreneur firstRepaymentMoment mainHistory
      (creditLifecycleEnd .entrepreneur firstRepaymentOffer firstRepaymentMoment mainHistory)
      (creditLifecycleEnd .entrepreneur .idle firstRepaymentMoment mainHistory) := by
  rw [entrepreneur_repayment_end, entrepreneur_repayment_idle_end]
  change SubjectiveTeleologicalDominates creditLifecycleRequirement
    (creditLifecycleValuedEnd .entrepreneur firstRepaymentMoment mainHistory)
    (lifecycleOmega .entrepreneur secondRepaymentMoment mainHistory)
    entrepreneurRepaymentOutsideOption
  apply subjective_teleological_dominates_of_unique_valued_end
    creditLifecycleRequirement
    (creditLifecycleValuedEnd .entrepreneur firstRepaymentMoment mainHistory)
    (.quantity creditLifecycleCollateral 1)
    (lifecycleOmega .entrepreneur secondRepaymentMoment mainHistory)
    entrepreneurRepaymentOutsideOption
  · intro e' he'
    cases e' with
    | bundle b => simp [creditLifecycleValuedEnd] at he'
    | timed e t => simp [creditLifecycleValuedEnd] at he'
    | quantity good q =>
        have hvalues : good = creditLifecycleCollateral ∧ q = 1 := by
          simpa [creditLifecycleValuedEnd, firstRepaymentMoment, mainMoment,
            creditLifecycleMoney, creditLifecycleCollateral] using he'
        rcases hvalues with ⟨rfl, rfl⟩
        rfl
  · simp [creditLifecycleValuedEnd, firstRepaymentMoment, mainMoment,
      creditLifecycleCollateral]
  · intro m
    by_cases hm : m = creditLifecycleCollateral
    · subst m
      norm_num [JointlyAttains, creditLifecycleRequirement, lifecycleOmega,
        lifecycleBalance, lifecycleBaseStage, secondRepaymentMoment, mainMoment]
    · have hmc : creditLifecycleCollateral ≠ m := fun he => hm he.symm
      simp [creditLifecycleRequirement, hmc]
  · intro h
    have hc := h creditLifecycleCollateral
    norm_num [JointlyAttains, creditLifecycleRequirement, entrepreneurRepaymentOutsideOption,
      lifecycleOmega, lifecycleBalance, lifecycleBaseStage, lifecycleLeaf,
      historyByIndex, creditLifecycleCollateral] at hc
    norm_num [creditLifecycleMoney, creditLifecycleCollateral,
      tokenMeans, rawMeans] at hc

/-- The operator accepts repayment because the transfer attains the valued
two-unit money end, which is absent under an unmatched acceptance. -/
theorem operator_prefers_repayment :
    creditLifecyclePreference .operator firstRepaymentMoment mainHistory
      (creditLifecycleEnd .operator firstRepaymentAccept firstRepaymentMoment mainHistory)
      (creditLifecycleEnd .operator .idle firstRepaymentMoment mainHistory) := by
  rw [operator_repayment_end, operator_repayment_idle_end]
  change SubjectiveTeleologicalDominates creditLifecycleRequirement
    (creditLifecycleValuedEnd .operator firstRepaymentMoment mainHistory)
    (lifecycleOmega .operator secondRepaymentMoment mainHistory)
    operatorRepaymentOutsideOption
  apply subjective_teleological_dominates_of_unique_valued_end
    creditLifecycleRequirement
    (creditLifecycleValuedEnd .operator firstRepaymentMoment mainHistory)
    (.quantity creditLifecycleMoney 2)
    (lifecycleOmega .operator secondRepaymentMoment mainHistory)
    operatorRepaymentOutsideOption
  · intro e' he'
    cases e' with
    | bundle b => simp [creditLifecycleValuedEnd] at he'
    | timed e t => simp [creditLifecycleValuedEnd] at he'
    | quantity good q =>
        have hvalues : good = creditLifecycleMoney ∧ q = 2 := by
          simpa [creditLifecycleValuedEnd, firstRepaymentMoment, mainMoment,
            creditLifecycleMoney, creditLifecycleCollateral] using he'
        rcases hvalues with ⟨rfl, rfl⟩
        rfl
  · simp [creditLifecycleValuedEnd, firstRepaymentMoment, mainMoment,
      creditLifecycleMoney]
  · intro m
    by_cases hm : m = creditLifecycleMoney
    · subst m
      norm_num [JointlyAttains, creditLifecycleRequirement, lifecycleOmega,
        lifecycleBalance, lifecycleBaseStage, secondRepaymentMoment, mainMoment]
    · have hmc : creditLifecycleMoney ≠ m := fun he => hm he.symm
      simp [creditLifecycleRequirement, hmc]
  · intro h
    have hc := h creditLifecycleMoney
    norm_num [JointlyAttains, creditLifecycleRequirement, operatorRepaymentOutsideOption,
      lifecycleOmega, lifecycleBalance, lifecycleBaseStage, lifecycleLeaf,
      historyByIndex, creditLifecycleMoney] at hc

/-- Each participant's feasible repayment menu contains only inaction and its
specified repayment action. -/
theorem entrepreneur_repayment_menu (β : WorkshopAction)
    (hβ : β ∈ A_feas .entrepreneur firstRepaymentMoment mainHistory) :
    β = alpha_zero ∨ β = firstRepaymentOffer := by
  have hcont : β ∈ A_cont .entrepreneur firstRepaymentMoment mainHistory :=
    (creditLifecycleActionFrame.A_feas_coupling
      WorkshopAgent.entrepreneur firstRepaymentMoment mainHistory β).mp hβ |>.1
  change β ∈ creditLifecycleActionsAt .entrepreneur firstRepaymentMoment at hcont
  rcases eventMenu_mem_cases hcont with hIdle | hOffer
  · exact Or.inl hIdle
  · right
    simpa [creditLifecycleChoice, firstRepaymentMoment, mainMoment,
      firstRepaymentOffer, firstAdvanceOffer, creditLifecycleMoney,
      creditLifecycleCollateral] using hOffer

theorem operator_repayment_menu (β : WorkshopAction)
    (hβ : β ∈ A_feas .operator firstRepaymentMoment mainHistory) :
    β = alpha_zero ∨ β = firstRepaymentAccept := by
  have hcont : β ∈ A_cont .operator firstRepaymentMoment mainHistory :=
    (creditLifecycleActionFrame.A_feas_coupling
      WorkshopAgent.operator firstRepaymentMoment mainHistory β).mp hβ |>.1
  change β ∈ creditLifecycleActionsAt .operator firstRepaymentMoment at hcont
  rcases eventMenu_mem_cases hcont with hIdle | hAccept
  · exact Or.inl hIdle
  · right
    simpa [creditLifecycleChoice, firstRepaymentMoment, mainMoment,
      firstRepaymentAccept, firstAdvanceAccept, creditLifecycleMoney,
      creditLifecycleCollateral] using hAccept

theorem entrepreneur_repayment_purposeful :
    PurposefulAct .entrepreneur firstRepaymentMoment mainHistory firstRepaymentOffer := by
  have hpref := borrower_prefers_repayment
  have hfeasible : firstRepaymentOffer ∈
      A_feas .entrepreneur firstRepaymentMoment mainHistory := by decide
  have hexec : Exec WorkshopAgent.entrepreneur firstRepaymentMoment
      firstRepaymentOffer mainHistory := by
    unfold Exec ChoicePartition
    change creditLifecycleActionFrame.mem_hist firstRepaymentMoment mainHistory ∧
      lifecycleEnacted WorkshopAgent.entrepreneur
        firstRepaymentMoment mainHistory = firstRepaymentOffer
    constructor
    · change lifecycleMemHist firstRepaymentMoment mainHistory
      decide
    · decide
  refine ⟨hfeasible, hexec, Or.inr hpref, ?_⟩
  intro β hβ hreverse
  rcases entrepreneur_repayment_menu β hβ with hidle | hoff
  · rw [hidle] at hreverse
    exact (pref_asymm WorkshopAgent.entrepreneur firstRepaymentMoment mainHistory
      hpref hreverse).elim
  · subst β
    exact (pref_irrefl WorkshopAgent.entrepreneur firstRepaymentMoment mainHistory _
      hreverse).elim

theorem operator_repayment_purposeful :
    PurposefulAct .operator firstRepaymentMoment mainHistory firstRepaymentAccept := by
  have hpref := operator_prefers_repayment
  have hfeasible : firstRepaymentAccept ∈
      A_feas .operator firstRepaymentMoment mainHistory := by decide
  have hexec : Exec WorkshopAgent.operator firstRepaymentMoment
      firstRepaymentAccept mainHistory := by
    unfold Exec ChoicePartition
    change creditLifecycleActionFrame.mem_hist firstRepaymentMoment mainHistory ∧
      lifecycleEnacted WorkshopAgent.operator
        firstRepaymentMoment mainHistory = firstRepaymentAccept
    constructor
    · change lifecycleMemHist firstRepaymentMoment mainHistory
      decide
    · decide
  refine ⟨hfeasible, hexec, Or.inr hpref, ?_⟩
  intro β hβ hreverse
  rcases operator_repayment_menu β hβ with hidle | haccept
  · rw [hidle] at hreverse
    exact (pref_asymm WorkshopAgent.operator firstRepaymentMoment mainHistory
      hpref hreverse).elim
  · subst β
    exact (pref_irrefl WorkshopAgent.operator firstRepaymentMoment mainHistory _
      hreverse).elim

theorem entrepreneur_repayment_is_bilateral_exchange :
    BilateralExchange .entrepreneur .operator firstRepaymentMoment mainHistory
      2 creditLifecycleMoney 1 creditLifecycleCollateral := by
  exact ricardian_bilateral_exchange_purposeful WorkshopAgent.entrepreneur
    WorkshopAgent.operator firstRepaymentMoment mainHistory creditLifecycleMoney
    creditLifecycleCollateral 2 1 (by decide) (by decide)
    entrepreneur_repayment_purposeful (by decide) operator_repayment_purposeful (by decide)

/-- The finite frame's actual first repayment fills the generic contract's
repayment interface after advance and strictly before maturity. -/
def entrepreneurCreditRepayment : CreditRepayment entrepreneurCreditAdvance where
  moment := firstRepaymentMoment
  nextMoment := secondRepaymentMoment
  successor := by
    change IsNextMoment lifecyclePrecedence lifecycleMemHist
      firstRepaymentMoment secondRepaymentMoment mainHistory
    exact lifecycleNextMoment_is_next firstRepaymentMoment mainHistory (by decide) (by decide)
  afterAdvance := by
    change lifecyclePrecedence secondAdvanceMoment firstRepaymentMoment
    decide
  beforeMaturity := by
    change lifecyclePrecedence firstRepaymentMoment maturityMoment
    decide
  purposefulExchange := entrepreneur_repayment_is_bilateral_exchange

end CreditLifecycleTree

end Praxeology

end
