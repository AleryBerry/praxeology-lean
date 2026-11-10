/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Catallactics
public import Praxeology.FirmBoundary
public import Praxeology.Production

/-!
# State Monopoly: The Praxeology of the State and Monopoly of Violence

This module formalizes the political economy of the state, hegemonic relations,
taxation, fiscal class partition, hoppean time-preference extraction,
judicial monopoly paradoxes, and statutory monopoly calculation blindness.
-/

@[expose] public section

namespace Praxeology


structure TerritorialMonopoly [W : ActionFrame] where
  ruler : W.Agent
  subjects : Finset W.Agent
  arbiter : W.Agent → W.Agent → W.Agent
  judge_in_own_cause : ∀ s ∈ subjects, arbiter s ruler = ruler


-- Section 1: Taxation and Voluntary Exchange


def IsEconomicMeans [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : Prop :=
  IsVoluntaryExchange i j t h α_i α_j

def IsPoliticalMeans [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_state : W.Action) : Prop :=
  IsCoerciveExtortion i j t h α_i α_state

/-- Classifies a physically invasive tax interaction under the stated
preference and public-good assumptions. -/
theorem physically_invasive_tax_with_public_good_classification
    [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_comply α_tax : W.Action)
    (public_good : W.Action → W.Action → ℕ)
    (h_service : 0 < public_good α_comply α_tax)
    (h_invasive : EndogenouslyInvasiveJ i j t h α_tax)
    (h_comply_beats_prison :
      W.Preference i t h (jointEndI i j t h α_comply α_tax)
        (jointEndI i j t h W.alpha_zero α_tax))
    (h_dissent :
      W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
        (jointEndI i j t h α_comply α_tax))
    (h_state_gains :
      W.Preference j t h (jointEndJ i j t h α_comply α_tax)
        (jointEndJ i j t h W.alpha_zero W.alpha_zero)) :
    IsPoliticalMeans i j t h α_comply α_tax ∧
    ¬ IsEconomicMeans i j t h α_comply α_tax ∧
    PurposefulResponseI i j t h α_comply α_tax ∧
    0 < public_good α_comply α_tax := by
  refine ⟨⟨h_invasive, h_comply_beats_prison, h_dissent, h_state_gains⟩,
    ?_, h_comply_beats_prison, h_service⟩
  exact fun h_econ => h_econ.2.1 h_invasive

/-- Majoritarian voting does not transmute coercive tax extraction into economic means:
even if an extraction policy is enacted by a winning coalition j, if it is physically invasive
of taxpayer i's endowment, it is classified strictly as political means (coercive extortion)
and strictly fails to be voluntary exchange (economic means). -/
theorem majoritarian_coalition_tax_is_political_means
    [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_comply α_tax : W.Action)
    (h_invasive : EndogenouslyInvasiveJ i j t h α_tax)
    (h_comply_beats_punishment :
      W.Preference i t h (jointEndI i j t h α_comply α_tax)
        (jointEndI i j t h W.alpha_zero α_tax))
    (h_taxpayer_dissent :
      W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
        (jointEndI i j t h α_comply α_tax))
    (h_coalition_gains :
      W.Preference j t h (jointEndJ i j t h α_comply α_tax)
        (jointEndJ i j t h W.alpha_zero W.alpha_zero)) :
    IsPoliticalMeans i j t h α_comply α_tax ∧
    ¬ IsEconomicMeans i j t h α_comply α_tax := by
  refine ⟨⟨h_invasive, h_comply_beats_punishment, h_taxpayer_dissent, h_coalition_gains⟩, ?_⟩
  exact fun h_econ => h_econ.2.1 h_invasive


-- Section 2: Taxpayers and Tax-Consumers


structure FiscalTransferSystem (W : ActionFrame) where
  Cohort : Finset W.Agent
  ω_pre : W.Agent → ℕ
  ω_post : W.Agent → ℕ
  deadweight_loss : ℕ
  h_conservation : (∑ a ∈ Cohort, ω_post a) + deadweight_loss = ∑ a ∈ Cohort, ω_pre a

/-- A cohort member whose post-transfer endowment exceeds the pre-transfer endowment. -/
def IsNetTaxConsumer [W : ActionFrame]
    (F : FiscalTransferSystem W) (a : W.Agent) : Prop :=
  a ∈ F.Cohort ∧ F.ω_pre a < F.ω_post a

/-- A cohort member whose post-transfer endowment is below the pre-transfer endowment. -/
def IsNetTaxpayer [W : ActionFrame]
    (F : FiscalTransferSystem W) (a : W.Agent) : Prop :=
  a ∈ F.Cohort ∧ F.ω_post a < F.ω_pre a


theorem no_universal_fiscal_dividend [W : ActionFrame]
    (F : FiscalTransferSystem W)
    (s : W.Agent) (hs_consumer : IsNetTaxConsumer F s)
    (h_all_weak_gain : ∀ a ∈ F.Cohort, F.ω_pre a ≤ F.ω_post a) :
    False := by
  have h_sum_lt : (∑ a ∈ F.Cohort, F.ω_pre a) < ∑ a ∈ F.Cohort, F.ω_post a := by
    apply Finset.sum_lt_sum
    · intro a ha
      exact h_all_weak_gain a ha
    · exact ⟨s, hs_consumer.1, hs_consumer.2⟩
  have h_le : (∑ a ∈ F.Cohort, F.ω_post a) ≤ ∑ a ∈ F.Cohort, F.ω_pre a := by
    have h := F.h_conservation
    exact h ▸ Nat.le_add_right (∑ a ∈ F.Cohort, F.ω_post a) F.deadweight_loss
  exact Nat.not_le_of_gt h_sum_lt h_le

/-- Tullock rent-seeking dissipation: when positive resources are consumed in the contest
or collection process (deadweight_loss > 0), the aggregate post-transfer physical endowment
of the cohort is strictly less than the initial pre-transfer endowment. -/
theorem rent_seeking_dissipation_depletes_cohort [W : ActionFrame]
    (F : FiscalTransferSystem W)
    (h_dwl_pos : 0 < F.deadweight_loss) :
    (∑ a ∈ F.Cohort, F.ω_post a) < ∑ a ∈ F.Cohort, F.ω_pre a := by
  have h := F.h_conservation
  omega


theorem calhoun_fiscal_class_partition [W : ActionFrame]
    (F : FiscalTransferSystem W)
    (s : W.Agent) (hs_consumer : IsNetTaxConsumer F s) :
    ∃ b : W.Agent, IsNetTaxpayer F b := by
  by_contra h_none
  have h_all_weak_gain : ∀ a ∈ F.Cohort, F.ω_pre a ≤ F.ω_post a := by
    intro a ha
    apply Nat.le_of_not_gt
    intro h_gain
    exact h_none ⟨a, ha, h_gain⟩
  exact no_universal_fiscal_dividend F s hs_consumer h_all_weak_gain

/-- A nonempty cohort cannot have every member strictly gain. -/
theorem no_universal_net_subsidy [W : ActionFrame]
    (F : FiscalTransferSystem W) (hne : ∃ s, s ∈ F.Cohort) :
    ¬ ∀ a ∈ F.Cohort, F.ω_pre a < F.ω_post a := by
  intro hall
  obtain ⟨s, hs⟩ := hne
  exact no_universal_fiscal_dividend F s ⟨hs, hall s hs⟩
    (fun a ha => Nat.le_of_lt (hall a ha))

/-- Total endowment and use equal prior endowment and yield across the cohort. -/
theorem finsetSum_law_in_re_transition
    [W : ActionFrame] (Cohort : Finset W.Agent) (t t' : W.Moment) (h : W.History) (m : W.Means)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_nontrade : ∀ a ∈ Cohort, ¬ W.IsTradeAction (W.enacted a t h)) :
    (∑ a ∈ Cohort, W.omega a t' h m) +
      ∑ a ∈ Cohort, W.use_means (W.enacted a t h) m =
    (∑ a ∈ Cohort, W.omega a t h m) +
      ∑ a ∈ Cohort, W.yield_means (W.enacted a t h) m := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact W.law_in_re_transition a t t' h (W.enacted a t h) m
    (h_nontrade a ha) rfl h_next


def FiscalTransferSystem.ofTransition
    [W : ActionFrame]
    (Cohort : Finset W.Agent) (t t' : W.Moment) (h : W.History) (m : W.Means)
    (deadweight_loss : ℕ)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_nontrade : ∀ a ∈ Cohort, ¬ W.IsTradeAction (W.enacted a t h))
    (h_transfer_balance : (∑ a ∈ Cohort, W.yield_means (W.enacted a t h) m) + deadweight_loss =
      ∑ a ∈ Cohort, W.use_means (W.enacted a t h) m) :
    FiscalTransferSystem W where
  Cohort := Cohort
  ω_pre := fun a => W.omega a t h m
  ω_post := fun a => W.omega a t' h m
  deadweight_loss := deadweight_loss
  h_conservation := by
    have h_trans := finsetSum_law_in_re_transition Cohort t t' h m h_next h_nontrade
    omega


theorem calhoun_action_frame_class_partition
    [W : ActionFrame]
    (Cohort : Finset W.Agent) (t t' : W.Moment) (h : W.History) (m : W.Means)
    (deadweight_loss : ℕ)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_nontrade : ∀ a ∈ Cohort, ¬ W.IsTradeAction (W.enacted a t h))
    (h_transfer_balance : (∑ a ∈ Cohort, W.yield_means (W.enacted a t h) m) + deadweight_loss =
      ∑ a ∈ Cohort, W.use_means (W.enacted a t h) m)
    (s : W.Agent) (hs_mem : s ∈ Cohort)
    (hs_gain : W.omega s t h m < W.omega s t' h m) :
    ∃ b : W.Agent, b ∈ Cohort ∧ W.omega b t' h m < W.omega b t h m := by
  let F := FiscalTransferSystem.ofTransition Cohort t t' h m deadweight_loss
    h_next h_nontrade h_transfer_balance
  have hs_cons : IsNetTaxConsumer F s := ⟨hs_mem, hs_gain⟩
  obtain ⟨b, hb_payer⟩ := calhoun_fiscal_class_partition F s hs_cons
  exact ⟨b, hb_payer.1, hb_payer.2⟩

/-- Calhoun extraction strips feasible menu: an action requiring the taxpayer's
full initial stock of `m` is stripped from their feasible menu by state extraction. -/
theorem calhoun_taxpayer_menu_stripped
    [W : ActionFrame]
    (Cohort : Finset W.Agent) (t t' : W.Moment) (h : W.History) (m : W.Means)
    (deadweight_loss : ℕ)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_nontrade : ∀ a ∈ Cohort, ¬ W.IsTradeAction (W.enacted a t h))
    (h_transfer_balance : (∑ a ∈ Cohort, W.yield_means (W.enacted a t h) m) + deadweight_loss =
      ∑ a ∈ Cohort, W.use_means (W.enacted a t h) m)
    (s : W.Agent) (hs_mem : s ∈ Cohort)
    (hs_gain : W.omega s t h m < W.omega s t' h m) :
    ∃ b ∈ Cohort, ∀ α : W.Action,
      α ∈ W.A_feas b t h →
      α ∈ W.A_cont b t' h →
      W.use_means α m = W.omega b t h m →
      FeasibleMenuStripped b t t' h α := by
  obtain ⟨b, hb_mem, hb_lt⟩ :=
    calhoun_action_frame_class_partition Cohort t t' h m deadweight_loss
      h_next h_nontrade h_transfer_balance s hs_mem hs_gain
  refine ⟨b, hb_mem, ?_⟩
  intro α h_feas h_cont h_tight
  have h_contract : StockContractedAt b t t' h m := hb_lt
  exact stockContractedAt_strips_tight_action b t t' h m α h_contract h_feas h_cont h_tight

/-- A title-anchored cohort transfer system tracking both physical possession
and legitimate title across a cohort of agents. -/
structure TitleAnchoredCohortTransfer (W : ActionFrame) where
  Cohort : Finset W.Agent
  pos_pre : W.Agent → ℕ
  pos_post : W.Agent → ℕ
  title : W.Agent → ℕ
  deadweight_loss : ℕ
  h_conservation : (∑ a ∈ Cohort, pos_post a) + deadweight_loss = ∑ a ∈ Cohort, pos_pre a

/-- A transfer is restitution if it returns physical possession from a wrongful
possessor (`title src < pos_pre src`) to a legitimate clean title holder
(`pos_pre dst < title dst`). -/
def IsRestitutionTransfer [W : ActionFrame]
    (T : TitleAnchoredCohortTransfer W) (src dst : W.Agent) : Prop :=
  src ∈ T.Cohort ∧ dst ∈ T.Cohort ∧
  T.title src < T.pos_pre src ∧
  T.pos_pre dst < T.title dst ∧
  T.pos_post src < T.pos_pre src ∧
  T.pos_pre dst < T.pos_post dst

/-- A transfer is extractive (taxation / state aggression) if it contracts the physical possession
of an agent holding no more than legitimate clean title (`pos_pre a ≤ title a`),
forcing their possession strictly below title (`pos_post a < title a`). -/
def IsExtractiveTransfer [W : ActionFrame]
    (T : TitleAnchoredCohortTransfer W) (taxpayer : W.Agent) : Prop :=
  taxpayer ∈ T.Cohort ∧
  T.pos_pre taxpayer ≤ T.title taxpayer ∧
  T.pos_post taxpayer < T.pos_pre taxpayer

/-- Restitution preserves clean title holders: it never contracts any agent who is
at or below legitimate title. -/
def PreservesCleanHolders [W : ActionFrame]
    (T : TitleAnchoredCohortTransfer W) : Prop :=
  ∀ a ∈ T.Cohort, T.pos_pre a ≤ T.title a → T.pos_pre a ≤ T.pos_post a

theorem extractive_transfer_breaks_clean_title [W : ActionFrame]
    (T : TitleAnchoredCohortTransfer W) (taxpayer : W.Agent)
    (h_ext : IsExtractiveTransfer T taxpayer) :
    T.pos_post taxpayer < T.title taxpayer := by
  have h1 := h_ext.2.1
  have h2 := h_ext.2.2
  omega

theorem extractive_transfer_incompatible_with_clean_preservation [W : ActionFrame]
    (T : TitleAnchoredCohortTransfer W) (taxpayer : W.Agent)
    (h_ext : IsExtractiveTransfer T taxpayer) :
    ¬ PreservesCleanHolders T := by
  intro h_pres
  have h_le := h_pres taxpayer h_ext.1 h_ext.2.1
  have h_lt := h_ext.2.2
  omega

theorem calhoun_title_partition [W : ActionFrame]
    (T : TitleAnchoredCohortTransfer W)
    (h_clean_init : ∀ a ∈ T.Cohort, T.pos_pre a = T.title a)
    (beneficiary : W.Agent) (h_ben_mem : beneficiary ∈ T.Cohort)
    (h_ben_gain : T.pos_pre beneficiary < T.pos_post beneficiary) :
    ∃ taxpayer : W.Agent, IsExtractiveTransfer T taxpayer := by
  have h_exists_payer : ∃ b ∈ T.Cohort, T.pos_post b < T.pos_pre b := by
    by_contra h_none
    have h_all_ge : ∀ a ∈ T.Cohort, T.pos_pre a ≤ T.pos_post a := by
      intro a ha
      apply Nat.le_of_not_gt
      intro h_contra
      exact h_none ⟨a, ha, h_contra⟩
    have h_sum_lt : (∑ a ∈ T.Cohort, T.pos_pre a) < ∑ a ∈ T.Cohort, T.pos_post a := by
      apply Finset.sum_lt_sum
      · intro a ha
        exact h_all_ge a ha
      · exact ⟨beneficiary, h_ben_mem, h_ben_gain⟩
    have h_le : (∑ a ∈ T.Cohort, T.pos_post a) ≤ ∑ a ∈ T.Cohort, T.pos_pre a := by
      have h := T.h_conservation
      exact h ▸ Nat.le_add_right (∑ a ∈ T.Cohort, T.pos_post a) T.deadweight_loss
    exact Nat.not_le_of_gt h_sum_lt h_le
  obtain ⟨b, hb_mem, hb_lt⟩ := h_exists_payer
  refine ⟨b, hb_mem, ?_, hb_lt⟩
  rw [h_clean_init b hb_mem]


theorem finsetSum_inventory_balance
    [W : ActionFrame] [BilateralExchangeFrame W]
    (Cohort : Finset W.Agent) {t u : W.Moment} {h : W.History}
    (runs : (a : W.Agent) → InventoryRun W a h t u) (m : W.Means) :
    (∑ a ∈ Cohort, W.omega a u h m) + ∑ a ∈ Cohort, (runs a).totalUse m =
    (∑ a ∈ Cohort, W.omega a t h m) + ∑ a ∈ Cohort, (runs a).totalYield m := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact (runs a).inventory_balance m


def FiscalTransferSystem.ofRun
    [W : ActionFrame] [BilateralExchangeFrame W]
    (Cohort : Finset W.Agent) {t u : W.Moment} {h : W.History}
    (runs : (a : W.Agent) → InventoryRun W a h t u) (m : W.Means)
    (deadweight_loss : ℕ)
    (h_run_balance : (∑ a ∈ Cohort, (runs a).totalYield m) + deadweight_loss =
      ∑ a ∈ Cohort, (runs a).totalUse m) :
    FiscalTransferSystem W where
  Cohort := Cohort
  ω_pre := fun a => W.omega a t h m
  ω_post := fun a => W.omega a u h m
  deadweight_loss := deadweight_loss
  h_conservation := by
    have h_trans := finsetSum_inventory_balance Cohort runs m
    omega


theorem calhoun_action_frame_run_class_partition
    [W : ActionFrame] [BilateralExchangeFrame W]
    (Cohort : Finset W.Agent) {t u : W.Moment} {h : W.History}
    (runs : (a : W.Agent) → InventoryRun W a h t u) (m : W.Means)
    (deadweight_loss : ℕ)
    (h_run_balance : (∑ a ∈ Cohort, (runs a).totalYield m) + deadweight_loss =
      ∑ a ∈ Cohort, (runs a).totalUse m)
    (s : W.Agent) (hs_mem : s ∈ Cohort)
    (hs_gain : W.omega s t h m < W.omega s u h m) :
    ∃ b : W.Agent, b ∈ Cohort ∧ W.omega b u h m < W.omega b t h m := by
  let F := FiscalTransferSystem.ofRun Cohort runs m deadweight_loss h_run_balance
  have hs_cons : IsNetTaxConsumer F s := ⟨hs_mem, hs_gain⟩
  obtain ⟨b, hb_payer⟩ := calhoun_fiscal_class_partition F s hs_cons
  exact ⟨b, hb_payer.1, hb_payer.2⟩


-- Section 3: Taxation and Production

/-- Production beats the leisure benchmark when gross output exceeds the
benchmark plus the tax claim. -/
def ProductionBeatsLeisure (Y T V_aut : ℕ) : Prop := V_aut + T < Y

/-- Leisure weakly beats production when the benchmark plus tax claim covers
gross output. -/
def ProductionAtOrBelowLeisure (Y T V_aut : ℕ) : Prop := Y ≤ V_aut + T

theorem production_score_partition (Y T V_aut : ℕ) :
    ProductionBeatsLeisure Y T V_aut ∨ ProductionAtOrBelowLeisure Y T V_aut := by
  dsimp [ProductionBeatsLeisure, ProductionAtOrBelowLeisure]
  omega

section FiscalDecisions

variable [W : ActionFrame]

structure TeleologicalBinaryChoice (i : Agent) (t : Moment) (h : History) where
  act : Action
  active_ne : act ≠ α₀
  feasible : act ∈ A_feas i t h
  baseline_feasible : α₀ ∈ A_feas i t h
  menu : ∀ β ∈ A_feas i t h, β = act ∨ β = α₀

theorem TeleologicalBinaryChoice.purposeful_act_of_pref
    {i : Agent} {t : Moment} {h : History}
    (D : TeleologicalBinaryChoice i t h)
    (he : Exec i t D.act h)
    (hpref : Preference i t h (End_of i D.act t h) (End_of i α₀ t h)) :
    PurposefulAct i t h D.act := by
  refine ⟨D.feasible, he, Or.inr hpref, ?_⟩
  intro β hβ
  rcases D.menu β hβ with rfl | rfl
  · exact pref_irrefl i t h _
  · exact pref_asymm i t h hpref

theorem TeleologicalBinaryChoice.not_purposeful_act_of_baseline_pref
    {i : Agent} {t : Moment} {h : History}
    (D : TeleologicalBinaryChoice i t h)
    (hpref : Preference i t h (End_of i α₀ t h) (End_of i D.act t h)) :
    ¬ PurposefulAct i t h D.act := by
  intro hp
  exact hp.2.2.2 α₀ D.baseline_feasible hpref

theorem TeleologicalBinaryChoice.purposeful_baseline_of_pref
    {i : Agent} {t : Moment} {h : History}
    (D : TeleologicalBinaryChoice i t h)
    (he : Exec i t α₀ h)
    (hpref : Preference i t h (End_of i α₀ t h) (End_of i D.act t h)) :
    PurposefulAct i t h α₀ := by
  refine ⟨D.baseline_feasible, he, Or.inl rfl, ?_⟩
  intro β hβ
  rcases D.menu β hβ with rfl | rfl
  · intro hp
    exact pref_asymm i t h hpref hp
  · exact pref_irrefl i t h _

theorem TeleologicalBinaryChoice.not_purposeful_baseline_of_active_pref
    {i : Agent} {t : Moment} {h : History}
    (D : TeleologicalBinaryChoice i t h)
    (hpref : Preference i t h (End_of i D.act t h) (End_of i α₀ t h)) :
    ¬ PurposefulAct i t h α₀ := by
  intro hp
  exact hp.2.2.2 D.act D.feasible hpref

/-- Production requires both enactment and strict preference over leisure. -/
theorem purposeful_production_of_pref
    {i : Agent} {t : Moment} {h : History}
    (D : TeleologicalBinaryChoice i t h)
    (he : Exec i t D.act h)
    (hpref : Preference i t h (End_of i D.act t h) (End_of i α₀ t h)) :
    PurposefulAct i t h D.act :=
  D.purposeful_act_of_pref he hpref

theorem production_shutdown_boundary
    {i : Agent} {t : Moment} {h : History}
    (D : TeleologicalBinaryChoice i t h)
    (hpref : Preference i t h (End_of i α₀ t h) (End_of i D.act t h)) :
    ¬ PurposefulAct i t h D.act ∧
    (∀ β, PurposefulAct i t h β → β = α₀) := by
  have hstop := D.not_purposeful_act_of_baseline_pref hpref
  refine ⟨hstop, ?_⟩
  intro β hp
  rcases D.menu β hp.1 with rfl | heq
  · exact False.elim (hstop hp)
  · exact heq

/-- Downsian rational non-pivotality: if a voter strictly prefers the abstention baseline
to voting action `D.act ≠ α₀`, the voting act cannot be purposeful under the action frame. -/
theorem voter_non_pivotality_blocks_purposefulness
    {i : Agent} {t : Moment} {h : History}
    (D : TeleologicalBinaryChoice i t h)
    (hpref : Preference i t h (End_of i α₀ t h) (End_of i D.act t h)) :
    ¬ PurposefulAct i t h D.act :=
  D.not_purposeful_act_of_baseline_pref hpref

/-- Direct action-frame non-pivotality: if an active choice α ≠ α₀ yields an identical end
to the baseline α₀ (such that the voter is completely non-pivotal to the outcome),
enacting α cannot be purposeful due to strict irreflexivity of preference. -/
theorem action_non_pivotality_not_purposeful
    (i : Agent) (t : Moment) (h : History) (α : Action)
    (h_ne : α ≠ α₀)
    (h_same_end : End_of i α t h = End_of i α₀ t h) :
    ¬ PurposefulAct i t h α := by
  intro hp
  rcases hp.2.2.1 with rfl | h_pref
  · exact h_ne rfl
  · rw [h_same_end] at h_pref
    exact pref_irrefl i t h (End_of i α₀ t h) h_pref

end FiscalDecisions

/-- Inputs for the two-agent ruler time-preference comparison. -/
structure RulerTimePreferenceComparison [W : ActionFrame] where
  stationary : Agent
  caretaker : Agent
  moment : Moment
  history : History
  stationaryChoice : TeleologicalBinaryChoice (W := W) stationary moment history
  caretakerChoice : TeleologicalBinaryChoice (W := W) caretaker moment history
  stationaryIdleExecuted : Exec stationary moment α₀ history
  caretakerActionExecuted : Exec caretaker moment caretakerChoice.act history
  stationary_prefers_baseline :
    Preference stationary moment history
      (End_of stationary α₀ moment history)
      (End_of stationary stationaryChoice.act moment history)
  caretaker_prefers_extraction :
    Preference caretaker moment history
      (End_of caretaker caretakerChoice.act moment history)
      (End_of caretaker α₀ moment history)

/-- Named behavioral consequences of the ruler extraction comparison. -/
structure RulerTimePreferenceConclusion [W : ActionFrame]
    (S : RulerTimePreferenceComparison (W := W)) : Prop where
  stationaryIdlePurposeful : PurposefulAct S.stationary S.moment S.history α₀
  stationaryExtractionNotPurposeful :
    ¬ PurposefulAct S.stationary S.moment S.history S.stationaryChoice.act
  caretakerExtractionPurposeful :
    PurposefulAct S.caretaker S.moment S.history S.caretakerChoice.act
  caretakerIdleNotPurposeful : ¬ PurposefulAct S.caretaker S.moment S.history α₀

/-- Derive the ruler's horizon and purposeful-action comparison. -/
theorem RulerTimePreferenceComparison.conclusion [W : ActionFrame]
    (S : RulerTimePreferenceComparison (W := W)) : RulerTimePreferenceConclusion S := by
  refine ⟨
    S.stationaryChoice.purposeful_baseline_of_pref
      S.stationaryIdleExecuted S.stationary_prefers_baseline,
    S.stationaryChoice.not_purposeful_act_of_baseline_pref
      S.stationary_prefers_baseline,
    S.caretakerChoice.purposeful_act_of_pref
      S.caretakerActionExecuted S.caretaker_prefers_extraction,
    S.caretakerChoice.not_purposeful_baseline_of_active_pref
      S.caretaker_prefers_extraction
  ⟩

/-- Ground ruler time-preference comparison directly in subjective teleological bundle dominance. -/
def RulerTimePreferenceComparison.ofBundleDominance [W : ActionFrame]
    (stationary caretaker : Agent) (moment : Moment) (history : History)
    (stationaryChoice : TeleologicalBinaryChoice (W := W) stationary moment history)
    (caretakerChoice : TeleologicalBinaryChoice (W := W) caretaker moment history)
    (stationaryIdleExecuted : Exec stationary moment α₀ history)
    (caretakerActionExecuted : Exec caretaker moment caretakerChoice.act history)
    (b_stat_idle b_stat_act b_care_act b_care_idle : W.Means → ℕ)
    (h_stat_idle : End_of stationary α₀ moment history = W.BundleEnd b_stat_idle)
    (h_stat_act : End_of stationary stationaryChoice.act moment history = W.BundleEnd b_stat_act)
    (h_care_act : End_of caretaker caretakerChoice.act moment history = W.BundleEnd b_care_act)
    (h_care_idle : End_of caretaker α₀ moment history = W.BundleEnd b_care_idle)
    (h_stat_dom : SubjectiveTeleologicalDominates W.requirement
      (W.ValuedEnd stationary moment history) b_stat_idle b_stat_act)
    (h_care_dom : SubjectiveTeleologicalDominates W.requirement
      (W.ValuedEnd caretaker moment history) b_care_act b_care_idle) :
    RulerTimePreferenceComparison (W := W) where
  stationary := stationary
  caretaker := caretaker
  moment := moment
  history := history
  stationaryChoice := stationaryChoice
  caretakerChoice := caretakerChoice
  stationaryIdleExecuted := stationaryIdleExecuted
  caretakerActionExecuted := caretakerActionExecuted
  stationary_prefers_baseline := by
    rw [h_stat_idle, h_stat_act]
    exact W.teleological_bundle_dominance_induces_preference
      stationary moment history b_stat_idle b_stat_act h_stat_dom
  caretaker_prefers_extraction := by
    rw [h_care_act, h_care_idle]
    exact W.teleological_bundle_dominance_induces_preference
      caretaker moment history b_care_act b_care_idle h_care_dom

-- Section 4: Judicial Authority


section JudicialMonopoly

variable [W : ActionFrame]


theorem judicial_monopoly_self_exoneration
    (S : Agent) (t : Moment) (h : History)
    (α_self_limit α_expand_power : Action)
    (h_feas_expand : α_expand_power ∈ A_feas S t h)
    (h_pref_expand : Preference S t h (End_of S α_expand_power t h) (End_of S α_self_limit t h)) :
    ¬ PurposefulAct S t h α_self_limit := by
  intro h_purp_limit
  have h_undom := h_purp_limit.2.2.2 α_expand_power h_feas_expand
  exact h_undom h_pref_expand

end JudicialMonopoly

/-- A preference for expansion rules out purposeful action by the arbiter. -/
theorem territorial_judicial_monopoly_self_exoneration [W : ActionFrame]
    (M : TerritorialMonopoly) (s : Agent) (hs : s ∈ M.subjects)
    (t : Moment) (h : History) (α_limit α_expand : Action)
    (hfeas : α_expand ∈ A_feas M.ruler t h)
    (hpref : Preference M.ruler t h
      (End_of M.ruler α_expand t h) (End_of M.ruler α_limit t h)) :
    ¬ PurposefulAct (M.arbiter s M.ruler) t h α_limit := by
  rw [M.judge_in_own_cause s hs]
  exact judicial_monopoly_self_exoneration M.ruler t h α_limit α_expand hfeas hpref

-- Section 5: Entry Barriers and Price Information


/-- The entry penalty reverses the comparison between the two uncertainty costs. -/
theorem statutory_monopoly_calculation_bounds
    (upstream_blur joint_cost_blur ext_opp_loss W_int grid_step Δz_abs statutory_penalty : ℕ)
    (h_pos_vol : 0 < Δz_abs)
    (h_blind : W_int + grid_step < upstream_blur + joint_cost_blur + ext_opp_loss)
    (h_ban : (upstream_blur + joint_cost_blur + ext_opp_loss) * Δz_abs <
             (W_int + grid_step) * Δz_abs + statutory_penalty) :
    SpotMarketUncertainty W_int grid_step Δz_abs <
      InternalFirmUncertainty upstream_blur joint_cost_blur ext_opp_loss Δz_abs ∧
    InternalFirmUncertainty upstream_blur joint_cost_blur ext_opp_loss Δz_abs <
      SpotMarketUncertainty W_int grid_step Δz_abs + statutory_penalty := by
  refine ⟨?_, ?_⟩
  · dsimp [SpotMarketUncertainty, InternalFirmUncertainty]
    exact Nat.mul_lt_mul_of_pos_right h_blind h_pos_vol
  · dsimp [SpotMarketUncertainty, InternalFirmUncertainty]
    exact h_ban


structure StatutoryMonopolyCalculationScenario [W : ActionFrame] where
  upstream : ℕ
  joint : ℕ
  external : ℕ
  width : ℕ
  gridStep : ℕ
  volume : ℕ
  penalty : ℕ
  volumePositive : 0 < volume
  internalBlindness : width + gridStep < upstream + joint + external
  statutoryPenalty : (upstream + joint + external) * volume <
    (width + gridStep) * volume + penalty
  operator : Agent
  entrant : Agent
  moment : Moment
  history : History
  operatorChoice : TeleologicalBinaryChoice (W := W) operator moment history
  entrantChoice : TeleologicalBinaryChoice (W := W) entrant moment history
  operatorExecution : Exec operator moment operatorChoice.act history
  operator_prefers_act :
    Preference operator moment history
      (End_of operator operatorChoice.act moment history)
      (End_of operator α₀ moment history)
  entrant_prefers_baseline :
    Preference entrant moment history
      (End_of entrant α₀ moment history)
      (End_of entrant entrantChoice.act moment history)

/-- Named price and action consequences for the statutory entry barrier. -/
structure StatutoryMonopolyCalculationConclusion [W : ActionFrame]
    (S : StatutoryMonopolyCalculationScenario (W := W)) : Prop where
  spotMarketNarrower : SpotMarketUncertainty S.width S.gridStep S.volume <
    InternalFirmUncertainty S.upstream S.joint S.external S.volume
  operatorPurposeful : PurposefulAct S.operator S.moment
    S.history S.operatorChoice.act
  entrantNotPurposeful : ¬ PurposefulAct S.entrant S.moment
    S.history S.entrantChoice.act

theorem statutory_cost_and_choice_classification [W : ActionFrame]
    (S : StatutoryMonopolyCalculationScenario (W := W)) :
    StatutoryMonopolyCalculationConclusion S := by
  have hblind' : SpotMarketUncertainty S.width S.gridStep S.volume <
      InternalFirmUncertainty S.upstream S.joint S.external S.volume := by
    dsimp [SpotMarketUncertainty, InternalFirmUncertainty]
    exact Nat.mul_lt_mul_of_pos_right S.internalBlindness S.volumePositive
  refine ⟨hblind',
    S.operatorChoice.purposeful_act_of_pref S.operatorExecution S.operator_prefers_act,
    S.entrantChoice.not_purposeful_act_of_baseline_pref S.entrant_prefers_baseline⟩

/-- Ground statutory monopoly calculation scenario directly in subjective
teleological bundle dominance. -/
def StatutoryMonopolyCalculationScenario.ofBundleDominance [W : ActionFrame]
    (upstream joint external width gridStep volume penalty : ℕ)
    (volumePositive : 0 < volume)
    (internalBlindness : width + gridStep < upstream + joint + external)
    (statutoryPenalty : (upstream + joint + external) * volume <
      (width + gridStep) * volume + penalty)
    (operator entrant : Agent) (moment : Moment) (history : History)
    (operatorChoice : TeleologicalBinaryChoice (W := W) operator moment history)
    (entrantChoice : TeleologicalBinaryChoice (W := W) entrant moment history)
    (operatorExecution : Exec operator moment operatorChoice.act history)
    (b_op_act b_op_idle b_ent_idle b_ent_act : W.Means → ℕ)
    (h_op_act : End_of operator operatorChoice.act moment history = W.BundleEnd b_op_act)
    (h_op_idle : End_of operator α₀ moment history = W.BundleEnd b_op_idle)
    (h_ent_idle : End_of entrant α₀ moment history = W.BundleEnd b_ent_idle)
    (h_ent_act : End_of entrant entrantChoice.act moment history = W.BundleEnd b_ent_act)
    (h_op_dom : SubjectiveTeleologicalDominates W.requirement
      (W.ValuedEnd operator moment history) b_op_act b_op_idle)
    (h_ent_dom : SubjectiveTeleologicalDominates W.requirement
      (W.ValuedEnd entrant moment history) b_ent_idle b_ent_act) :
    StatutoryMonopolyCalculationScenario (W := W) where
  upstream := upstream
  joint := joint
  external := external
  width := width
  gridStep := gridStep
  volume := volume
  penalty := penalty
  volumePositive := volumePositive
  internalBlindness := internalBlindness
  statutoryPenalty := statutoryPenalty
  operator := operator
  entrant := entrant
  moment := moment
  history := history
  operatorChoice := operatorChoice
  entrantChoice := entrantChoice
  operatorExecution := operatorExecution
  operator_prefers_act := by
    rw [h_op_act, h_op_idle]
    exact W.teleological_bundle_dominance_induces_preference
      operator moment history b_op_act b_op_idle h_op_dom
  entrant_prefers_baseline := by
    rw [h_ent_idle, h_ent_act]
    exact W.teleological_bundle_dominance_induces_preference
      entrant moment history b_ent_idle b_ent_act h_ent_dom


structure StatutoryMonopolyFiscalIncidenceEvidence [W : ActionFrame]
    [BilateralExchangeFrame W] (S : StatutoryMonopolyCalculationScenario (W := W)) where
  next : Moment
  cohort : Finset Agent
  inventoryRun : (a : Agent) → InventoryRun W a S.history S.moment next
  means : Means
  deadweight_loss : ℕ
  runBalance : (∑ a ∈ cohort, (inventoryRun a).totalYield means) + deadweight_loss =
    ∑ a ∈ cohort, (inventoryRun a).totalUse means
  operatorInCohort : S.operator ∈ cohort
  operatorGain : W.omega S.operator S.moment S.history means <
    W.omega S.operator next S.history means

/-- Fiscal incidence has a named beneficiary-loss witness, alongside the
calculation and purposeful-action results. -/
structure StatutoryMonopolyFiscalIncidenceConclusion [W : ActionFrame]
    [BilateralExchangeFrame W] (S : StatutoryMonopolyCalculationScenario (W := W))
    (E : StatutoryMonopolyFiscalIncidenceEvidence S) : Prop where
  calculation : StatutoryMonopolyCalculationConclusion S
  beneficiaryLoss : ∃ beneficiary ∈ E.cohort,
    W.omega beneficiary E.next S.history E.means <
      W.omega beneficiary S.moment S.history E.means

theorem statutory_monopoly_run_blindness_and_fiscal_incidence [W : ActionFrame]
    [BilateralExchangeFrame W] (S : StatutoryMonopolyCalculationScenario (W := W))
    (E : StatutoryMonopolyFiscalIncidenceEvidence S) :
    StatutoryMonopolyFiscalIncidenceConclusion S E := by
  have hcalc := statutory_cost_and_choice_classification S
  have ⟨b, hb_mem, hb_loss⟩ := calhoun_action_frame_run_class_partition
    E.cohort E.inventoryRun E.means E.deadweight_loss E.runBalance S.operator
    E.operatorInCohort E.operatorGain
  exact ⟨hcalc, ⟨b, hb_mem, hb_loss⟩⟩


structure PublicGoodsTaxationEvidence [W : ActionFrame] {i j : W.Agent} {t : W.Moment}
    {h : W.History} where
  comply : W.Action
  tax : W.Action
  publicGood : W.Action → W.Action → ℕ
  servicePositive : 0 < publicGood comply tax
  taxPhysicallyInvasive : EndogenouslyInvasiveJ i j t h tax
  complianceBeatsPrison :
    W.Preference i t h (jointEndI i j t h comply tax)
      (jointEndI i j t h W.alpha_zero tax)
  dissentBeatsCompliance :
    W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
      (jointEndI i j t h comply tax)
  stateGains :
    W.Preference j t h (jointEndJ i j t h comply tax)
      (jointEndJ i j t h W.alpha_zero W.alpha_zero)

/-- Evidence for a subject's ruler acting as judge in its own cause. -/
structure JudicialMonopolyRulingEvidence [W : ActionFrame] where
  monopoly : TerritorialMonopoly
  subject : Agent
  subjectInTerritory : subject ∈ monopoly.subjects
  moment : Moment
  history : History
  limitingAction : Action
  expandingAction : Action
  expansionFeasible : expandingAction ∈ A_feas monopoly.ruler moment history
  expansionPreferred : Preference monopoly.ruler moment history
    (End_of monopoly.ruler expandingAction moment history)
    (End_of monopoly.ruler limitingAction moment history)

/-- A single input package connects coercive taxation and the judicial
monopoly evidence without flattening their unrelated hypotheses. -/
structure StateMonopolyMasterEvidence [W : ActionFrame] {i j : W.Agent} {t : W.Moment}
    {h : W.History} where
  taxation : PublicGoodsTaxationEvidence (W := W) (i := i) (j := j) (t := t) (h := h)
  ruling : JudicialMonopolyRulingEvidence

/-- Named conclusion for both the economic classification of taxation and the
arbiter's purposeful-action failure. -/
structure StateMonopolyMasterConclusion [W : ActionFrame] {i j : W.Agent} {t : W.Moment}
    {h : W.History}
    (S : StateMonopolyMasterEvidence (W := W) (i := i) (j := j) (t := t) (h := h)) :
    Prop where
  politicalNotEconomic :
    IsPoliticalMeans i j t h S.taxation.comply S.taxation.tax ∧
    ¬ IsEconomicMeans i j t h S.taxation.comply S.taxation.tax
  arbiterCannotPurposefullyLimit :
    ¬ PurposefulAct (S.ruling.monopoly.arbiter S.ruling.subject
      S.ruling.monopoly.ruler) S.ruling.moment S.ruling.history S.ruling.limitingAction

theorem state_monopoly_political_economy_master_synthesis [W : ActionFrame] {i j : W.Agent}
    {t : W.Moment} {h : W.History}
    (S : StateMonopolyMasterEvidence (W := W) (i := i) (j := j) (t := t) (h := h)) :
    StateMonopolyMasterConclusion S := by
  have h_tax := physically_invasive_tax_with_public_good_classification
    i j t h S.taxation.comply S.taxation.tax S.taxation.publicGood
    S.taxation.servicePositive S.taxation.taxPhysicallyInvasive
    S.taxation.complianceBeatsPrison S.taxation.dissentBeatsCompliance
    S.taxation.stateGains
  exact ⟨⟨h_tax.1, h_tax.2.1⟩,
    territorial_judicial_monopoly_self_exoneration S.ruling.monopoly
      S.ruling.subject S.ruling.subjectInTerritory S.ruling.moment S.ruling.history
      S.ruling.limitingAction S.ruling.expandingAction
      S.ruling.expansionFeasible S.ruling.expansionPreferred⟩


-- Section 6: Non-Vacuity Classification


/-- Given supplied tax, service, and preference evidence, the interaction is
classified as political means and yields purposeful compliance. This theorem
does not construct an inhabited evidence package. -/
theorem taxation_with_public_goods_from_supplied_evidence [W : ActionFrame] {i j : W.Agent}
    {t : W.Moment} {h : W.History}
    (E : PublicGoodsTaxationEvidence (W := W) (i := i) (j := j) (t := t) (h := h)) :
    IsPoliticalMeans i j t h E.comply E.tax ∧
    ¬ IsEconomicMeans i j t h E.comply E.tax ∧
    PurposefulResponseI i j t h E.comply E.tax ∧
    0 < E.publicGood E.comply E.tax :=
  physically_invasive_tax_with_public_good_classification
    i j t h E.comply E.tax E.publicGood E.servicePositive E.taxPhysicallyInvasive
    E.complianceBeatsPrison E.dissentBeatsCompliance E.stateGains

section

@[reducible] local instance : ActionFrame := BilateralTradeActionFrame

/-- An executed offer with equal returns is not purposeful. -/
theorem fiscal_tie_not_purposeful_non_vacuous :
    ∃ D : @TeleologicalBinaryChoice BilateralTradeActionFrame (0 : Fin 2) .root (1 : Fin 4),
      @Exec BilateralTradeActionFrame (0 : Fin 2) .root D.act (1 : Fin 4) ∧
      ¬ @PurposefulAct BilateralTradeActionFrame (0 : Fin 2) .root (1 : Fin 4) D.act := by
  let D : @TeleologicalBinaryChoice BilateralTradeActionFrame (0 : Fin 2) .root (1 : Fin 4) := {
    act := ModelAction.offer 0 1 1 0 1 1
    active_ne := by decide
    feasible := by decide
    baseline_feasible := by decide
    menu := by
      intro β hβ
      change β ∈ ({ModelAction.idle, ModelAction.offer 0 1 1 0 1 1} : Finset ModelAction) at hβ
      change β = ModelAction.offer 0 1 1 0 1 1 ∨ β = ModelAction.idle
      simpa only [Finset.mem_insert, Finset.mem_singleton, or_comm] using hβ
  }
  refine ⟨D, ⟨by trivial, rfl⟩, ?_⟩
  intro hp
  rcases hp.2.2.1 with heq | hpref
  · exact D.active_ne heq
  · change @Preference BilateralTradeActionFrame (0 : Fin 2) BilateralMoment.root
      (1 : Fin 4) BilateralEnd.baseline BilateralEnd.baseline at hpref
    exact @pref_irrefl BilateralTradeActionFrame (0 : Fin 2)
      BilateralMoment.root (1 : Fin 4) BilateralEnd.baseline hpref

end

section

@[reducible] local instance : ActionFrame := FiniteBranchingModel

/-- Nonempty subject cohort, arbiter is ruler for subjects. -/
theorem territorial_monopoly_non_vacuous :
    ∃ M : @TerritorialMonopoly FiniteBranchingModel,
      (1 : Fin 2) ∈ M.subjects ∧
      M.arbiter (1 : Fin 2) M.ruler = M.ruler := by
  let M : @TerritorialMonopoly FiniteBranchingModel := {
    ruler := (0 : Fin 2)
    subjects := {(1 : Fin 2)}
    arbiter := fun _ _ => (0 : Fin 2)
    judge_in_own_cause := by intros; rfl
  }
  exact ⟨M, by decide, rfl⟩

end

theorem production_shutdown_arithmetic_boundaries :
    ProductionAtOrBelowLeisure 12 12 0 ∧
    ProductionAtOrBelowLeisure 12 20 0 ∧
    ProductionBeatsLeisure 12 4 5 ∧
    8 * 2 < 20 := by
  norm_num [ProductionAtOrBelowLeisure, ProductionBeatsLeisure]


section

@[reducible] local instance : ActionFrame := BilateralTradeActionFrame

theorem state_monopoly_theorems_non_vacuous :
    ∃ (F : FiscalTransferSystem BilateralTradeActionFrame),
      IsNetTaxConsumer F (0 : Fin 2) ∧
      (∃ b : Fin 2, IsNetTaxpayer F b) ∧
      (8 * 2 < 20 ∧ ProductionBeatsLeisure 12 4 5) ∧
      (20 ≤ 4 * 8 ∧ ProductionAtOrBelowLeisure 12 9 5) := by
  let F : FiscalTransferSystem BilateralTradeActionFrame := {
    Cohort := {(0 : Fin 2), (1 : Fin 2)}
    ω_pre := fun _ => 10
    ω_post := fun a => if a = (0 : Fin 2) then 15 else 3
    deadweight_loss := 2
    h_conservation := by decide
  }
  have h_cons0 : IsNetTaxConsumer F (0 : Fin 2) := ⟨by decide, by dsimp [F]; decide⟩
  have h_taxpayer := calhoun_fiscal_class_partition F (0 : Fin 2) h_cons0
  refine ⟨F, h_cons0, h_taxpayer, ?_, ?_⟩
  · exact ⟨by decide, by simp [ProductionBeatsLeisure]⟩
  · exact ⟨by decide, by simp [ProductionAtOrBelowLeisure]⟩

/-- Non-vacuity witness for Calhoun run partition:
On `BilateralTradeActionFrame`, an actual execution run from `.root` to `.leaf3`
strictly increases agent 0's stock of good 1 under balanced inventory flows,
guaranteeing by `calhoun_action_frame_run_class_partition` that agent 1's stock of good 1
is strictly depleted. -/
theorem calhoun_action_frame_partition_non_vacuous :
    ∃ (Cohort : Finset (Fin 2))
      (runs : (a : Fin 2) → InventoryRun BilateralTradeActionFrame a (3 : Fin 4)
        BilateralMoment.root BilateralMoment.leaf3)
      (m : Fin 3) (deadweight_loss : ℕ),
      ((∑ a ∈ Cohort, (runs a).totalYield m) + deadweight_loss =
        ∑ a ∈ Cohort, (runs a).totalUse m) ∧
      ∃ (s : Fin 2), s ∈ Cohort ∧
        BilateralTradeActionFrame.omega s BilateralMoment.root (3 : Fin 4) m <
          BilateralTradeActionFrame.omega s BilateralMoment.leaf3 (3 : Fin 4) m ∧
        ∃ b ∈ Cohort, BilateralTradeActionFrame.omega b BilateralMoment.leaf3 (3 : Fin 4) m <
          BilateralTradeActionFrame.omega b BilateralMoment.root (3 : Fin 4) m := by
  have h_next : IsNextMoment BilateralTradeActionFrame.Precedence
      BilateralTradeActionFrame.mem_hist
      BilateralMoment.root BilateralMoment.leaf3 (3 : Fin 4) := by
    change IsNextMoment bilateral_prec bilateral_mem_hist
      BilateralMoment.root BilateralMoment.leaf3 (3 : Fin 4)
    refine ⟨trivial, rfl, trivial, ?_⟩
    intro τ _ hbetween
    cases τ <;> simp [bilateral_prec] at hbetween
  let step0 : InventoryStep BilateralTradeActionFrame (0 : Fin 2) (3 : Fin 4)
      BilateralMoment.root BilateralMoment.leaf3 :=
    .matchedOffer (1 : Fin 2) 1 (0 : Fin 3) 1 (1 : Fin 3) (by decide) rfl rfl h_next
  let step1 : InventoryStep BilateralTradeActionFrame (1 : Fin 2) (3 : Fin 4)
      BilateralMoment.root BilateralMoment.leaf3 :=
    .matchedAccept (0 : Fin 2) 1 (0 : Fin 3) 1 (1 : Fin 3) (by decide) rfl rfl h_next
  let run0 : InventoryRun BilateralTradeActionFrame (0 : Fin 2) (3 : Fin 4)
      BilateralMoment.root BilateralMoment.leaf3 :=
    InventoryRun.step step0 (InventoryRun.done BilateralMoment.leaf3)
  let run1 : InventoryRun BilateralTradeActionFrame (1 : Fin 2) (3 : Fin 4)
      BilateralMoment.root BilateralMoment.leaf3 :=
    InventoryRun.step step1 (InventoryRun.done BilateralMoment.leaf3)
  let runs : (a : Fin 2) → InventoryRun BilateralTradeActionFrame a (3 : Fin 4)
      BilateralMoment.root BilateralMoment.leaf3 :=
    fun a => match a with
    | 0 => run0
    | 1 => run1
  let Cohort : Finset (Fin 2) := {(0 : Fin 2), (1 : Fin 2)}
  let m : Fin 3 := (1 : Fin 3)
  let deadweight_loss : ℕ := 0
  have h_run_balance : (∑ a ∈ Cohort, (runs a).totalYield m) + deadweight_loss =
      ∑ a ∈ Cohort, (runs a).totalUse m := by
    change (run0.totalYield m + run1.totalYield m) + 0 =
      run0.totalUse m + run1.totalUse m
    rfl
  have hs_mem : (0 : Fin 2) ∈ Cohort := by decide
  have hs_gain : BilateralTradeActionFrame.omega (0 : Fin 2) BilateralMoment.root (3 : Fin 4) m <
      BilateralTradeActionFrame.omega (0 : Fin 2) BilateralMoment.leaf3 (3 : Fin 4) m := by
    decide
  have h_part := calhoun_action_frame_run_class_partition Cohort runs m deadweight_loss
    h_run_balance (0 : Fin 2) hs_mem hs_gain
  exact ⟨Cohort, runs, m, deadweight_loss, h_run_balance, (0 : Fin 2), hs_mem, hs_gain, h_part⟩

end

/-- Majority preference across three agents within an ActionFrame. -/
def ActionFrameMajorityPref [W : ActionFrame] (t : W.Moment) (h : W.History)
    (i₁ i₂ i₃ : W.Agent) (e₁ e₂ : W.Ends) : Prop :=
  (W.Preference i₁ t h e₁ e₂ ∧ W.Preference i₂ t h e₁ e₂) ∨
  (W.Preference i₁ t h e₁ e₂ ∧ W.Preference i₃ t h e₁ e₂) ∨
  (W.Preference i₂ t h e₁ e₂ ∧ W.Preference i₃ t h e₁ e₂)

/-- Synonym for ActionFrameMajorityPref denoting strict pairwise majority preference. -/
def PairwiseMajorityPreferred [W : ActionFrame] (t : W.Moment) (h : W.History)
    (i₁ i₂ i₃ : W.Agent) (e₁ e₂ : W.Ends) : Prop :=
  ActionFrameMajorityPref t h i₁ i₂ i₃ e₁ e₂

/-- ActionFrame majority preference is asymmetric by ActionFrame preference asymmetry. -/
theorem actionFrameMajorityPref_asymm [W : ActionFrame]
    (t : W.Moment) (h : W.History) (i₁ i₂ i₃ : W.Agent) (e₁ e₂ : W.Ends) :
    ActionFrameMajorityPref t h i₁ i₂ i₃ e₁ e₂ →
    ¬ ActionFrameMajorityPref t h i₁ i₂ i₃ e₂ e₁ := by
  rintro (⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩) (⟨g1, g2⟩ | ⟨g1, g3⟩ | ⟨g2, g3⟩)
  · exact W.pref_asymm i₁ t h h1 g1
  · exact W.pref_asymm i₁ t h h1 g1
  · exact W.pref_asymm i₂ t h h2 g2
  · exact W.pref_asymm i₁ t h h1 g1
  · exact W.pref_asymm i₁ t h h1 g1
  · exact W.pref_asymm i₃ t h h3 g3
  · exact W.pref_asymm i₂ t h h2 g2
  · exact W.pref_asymm i₃ t h h3 g3
  · exact W.pref_asymm i₂ t h h2 g2

/-- Condorcet majority voting cycle under three agents with individually transitive preferences.
Every candidate in the 3-cycle is pairwise majority defeated by another candidate, and
majority preference is strictly asymmetric by `W.pref_asymm`. -/
theorem action_frame_majority_cycle
    [W : ActionFrame] (t : W.Moment) (h : W.History)
    (i₁ i₂ i₃ : W.Agent) (e₀ e₁ e₂ : W.Ends)
    (h₁_01 : W.Preference i₁ t h e₀ e₁) (h₁_12 : W.Preference i₁ t h e₁ e₂)
    (h₂_12 : W.Preference i₂ t h e₁ e₂) (h₂_20 : W.Preference i₂ t h e₂ e₀)
    (h₃_20 : W.Preference i₃ t h e₂ e₀) (h₃_01 : W.Preference i₃ t h e₀ e₁) :
    (ActionFrameMajorityPref t h i₁ i₂ i₃ e₀ e₁ ∧
     ActionFrameMajorityPref t h i₁ i₂ i₃ e₁ e₂ ∧
     ActionFrameMajorityPref t h i₁ i₂ i₃ e₂ e₀) ∧
    let cand : Fin 3 → W.Ends := fun c => match c with | 0 => e₀ | 1 => e₁ | 2 => e₂
    ∀ c : Fin 3, ∃ d : Fin 3, d ≠ c ∧
      PairwiseMajorityPreferred t h i₁ i₂ i₃ (cand d) (cand c) ∧
      ¬ PairwiseMajorityPreferred t h i₁ i₂ i₃ (cand c) (cand d) := by
  have h_maj_01 : ActionFrameMajorityPref t h i₁ i₂ i₃ e₀ e₁ :=
    Or.inr (Or.inl ⟨h₁_01, h₃_01⟩)
  have h_maj_12 : ActionFrameMajorityPref t h i₁ i₂ i₃ e₁ e₂ :=
    Or.inl ⟨h₁_12, h₂_12⟩
  have h_maj_20 : ActionFrameMajorityPref t h i₁ i₂ i₃ e₂ e₀ :=
    Or.inr (Or.inr ⟨h₂_20, h₃_20⟩)
  have h_cycle : ActionFrameMajorityPref t h i₁ i₂ i₃ e₀ e₁ ∧
      ActionFrameMajorityPref t h i₁ i₂ i₃ e₁ e₂ ∧
      ActionFrameMajorityPref t h i₁ i₂ i₃ e₂ e₀ :=
    ⟨h_maj_01, h_maj_12, h_maj_20⟩
  refine ⟨h_cycle, ?_⟩
  intro cand c
  fin_cases c
  · refine ⟨2, by decide, ?_⟩
    change PairwiseMajorityPreferred t h i₁ i₂ i₃ e₂ e₀ ∧
      ¬ PairwiseMajorityPreferred t h i₁ i₂ i₃ e₀ e₂
    exact ⟨h_maj_20, actionFrameMajorityPref_asymm t h i₁ i₂ i₃ e₂ e₀ h_maj_20⟩
  · refine ⟨0, by decide, ?_⟩
    change PairwiseMajorityPreferred t h i₁ i₂ i₃ e₀ e₁ ∧
      ¬ PairwiseMajorityPreferred t h i₁ i₂ i₃ e₁ e₀
    exact ⟨h_maj_01, actionFrameMajorityPref_asymm t h i₁ i₂ i₃ e₀ e₁ h_maj_01⟩
  · refine ⟨1, by decide, ?_⟩
    change PairwiseMajorityPreferred t h i₁ i₂ i₃ e₁ e₂ ∧
      ¬ PairwiseMajorityPreferred t h i₁ i₂ i₃ e₂ e₁
    exact ⟨h_maj_12, actionFrameMajorityPref_asymm t h i₁ i₂ i₃ e₁ e₂ h_maj_12⟩

end Praxeology

end

