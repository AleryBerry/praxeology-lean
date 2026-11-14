/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.FiniteEconomy
public import Praxeology.FiniteEconomy.ActiveParticipation
public import Praxeology.FiniteEconomy.BilateralPilot
public import Praxeology.Action
public import Praxeology.Subjective
public import Praxeology.Veridical
public import Praxeology.EpistemicAbility
public import Praxeology.Marginal
public import Praxeology.Catallactics
public import Praxeology.EconomicCalculation
public import Praxeology.EconomicCalculation.Incentives
public import Praxeology.EconomicCalculation.Institutions
public import Praxeology.Catallactics.Credit
public import Praxeology.Catallactics.ProgramExchangeWitness
public import Praxeology.Production
public import Praxeology.Organization
public import Praxeology.FirmBoundary
public import Praxeology.FirmWitness
public import Praxeology.BusinessCycle
public import Praxeology.BusinessCycle.CreditLifecycleFrame
public import Praxeology.EconometricLimits
public import Praxeology.StateMonopoly


/-!
# Praxeology Lean library

A Lean 4 formalization of selected praxeological, catallactic, entrepreneurial,
and business-cycle claims. The library combines a general `ActionFrame` model
interface with finite and abstract witnesses; the precise assumptions and
proved scope of individual results are documented in `spec/claims_and_assumptions.md`.

The main imports cover action and preference, finite economy and marginal
allocation, exchange and credit, production and firm boundaries, business-cycle
mechanisms, econometric limitations, behavioral choice, and state monopoly.
The modules establish conditional results under explicit model assumptions.
They do not by themselves derive every Austrian economic conclusion from a
single minimal axiom system. The named five-project regimes have a recursive
physical ActionFrame schedule with early capital production, branch-sensitive
market recalculation, and contractual default settlement. Separate behavioral
results establish purposeful household saving and subjective project-two and
project-three acceptance under an explicit forecast, together with
context-matched regret on the two actual default branches. These results do not
derive the forecast from the actual household plan or model legal foreclosure.

Axiom dependencies are audited separately. Mathlib is used as a theorem library;
its use is not an additional axiom. The audit allows Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies and reports any
other transitive axiom dependency.
-/

@[expose] public section

namespace Praxeology

/-- Ground instantiation of Theorem 0.2: ActionFrame consistency. -/
theorem ground_world_consistent : Nonempty ActionFrame :=
  action_frame_consistent

/-- Ground instantiation of linear chain property in FiniteBranchingModel. -/
theorem ground_finite_model_histories_linear (h : Fin 3) :
    IsMaximalLinearChain finite_action_prec { t : Fin 4 | branch_incidence t h } :=
  finite_model_histories_maximal_linear h

/-- Ground instantiation of non-trivial branching in FiniteBranchingModel. -/
theorem ground_branching_nontrivial :
    ∃ (t : Fin 4) (h : Fin 3), ¬ branch_incidence t h :=
  finite_model_branching_nontrivial

/-- Ground instantiation of Theorem 3.3a: equivalence of purposeful action and comparability. -/
theorem ground_menu_comparable_equiv (i : FiniteBranchingModel.Agent)
    (t : FiniteBranchingModel.Moment) (h : FiniteBranchingModel.History)
    (α : FiniteBranchingModel.Action) :
    (@ActivePurposefulAct FiniteBranchingModel i t h α ∧
     @MenuComparable FiniteBranchingModel i t h α) ↔
    @DistinctEndDominantAct FiniteBranchingModel i t h α :=
  @purposeful_act_and_comparable_iff_distinct_dominant FiniteBranchingModel i t h α

/-- Ground instantiation of standalone quantity monotonicity in FiniteBranchingModel. -/
theorem ground_finite_model_quantity_monotonicity
    (i : FiniteBranchingModel.Agent) (t : FiniteBranchingModel.Moment)
    (h : FiniteBranchingModel.History) (m : FiniteBranchingModel.Means)
    (q q' : ℕ) (τ : FiniteBranchingModel.Moment) (hq : q' < q) :
    @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel _ m q τ)
      (@timedQuantityEnd FiniteBranchingModel _ m q' τ) :=
  finite_model_quantity_monotonicity i t h m q q' τ hq

/-- Ground instantiation of Theorem 3.5b: non-vacuous positive originary interest. -/
theorem ground_intertemporal_chain_non_vacuous :
    ∃ (i : FiniteBranchingModel.Agent) (t : FiniteBranchingModel.Moment)
      (h : FiniteBranchingModel.History) (m : FiniteBranchingModel.Means)
      (q q' : ℕ) (α_cons : FiniteBranchingModel.Action) (τ1 : FiniteBranchingModel.Moment),
      @PurposefulAct FiniteBranchingModel i t h α_cons ∧
      @DistinctEndDominantAct FiniteBranchingModel i t h α_cons ∧
      @CausalDoxasticOpenHorizon FiniteBranchingModel _ i t h
        (@QuantityEnd FiniteBranchingModel _ m q) α_cons τ1 ∧
      ¬ @IsPostHorizon FiniteBranchingModel i t h ∧
      (∃ (τ2 : FiniteBranchingModel.Moment) (δ : ℕ),
        0 < q ∧ @LT.lt FiniteBranchingModel.Moment _ τ1 τ2 ∧ q < q' ∧ δ ≥ 1 ∧ q' = q + δ ∧
        @Preference FiniteBranchingModel i t h
          (@TimedEnd FiniteBranchingModel _ (@QuantityEnd FiniteBranchingModel _ m q) τ1)
          (@TimedEnd FiniteBranchingModel _ (@QuantityEnd FiniteBranchingModel _ m q) τ2) ∧
        @Preference FiniteBranchingModel i t h
          (@timedQuantityEnd FiniteBranchingModel _ m q τ1)
          (@timedQuantityEnd FiniteBranchingModel _ m q τ2)) :=
  causal_intertemporal_chain_non_vacuous

/-- Ground instantiation of Theorem 7.1b: Kirznerian arbitrage contracts the indeterminacy cone. -/
theorem ground_kirznerian_arbitrage_contracts_cone :
    ∃ (P_low P_high P_low' P_high' : PriceVec 2) (x y : InputVec 2),
      (∀ r, P_low r ≤ P_low' r) ∧
      (∀ r, P_high' r ≤ P_high r) ∧
      PhysicalAntichain x y ∧
      InIndeterminacyCone 2 P_low P_high x y ∧
      ¬ InIndeterminacyCone 2 P_low' P_high' x y :=
  kirznerian_arbitrage_strictly_contracts_cone

/-- Ground instantiation of Theorem 7.6b: viable coalescence under critical attenuation. -/
theorem ground_viable_coalescence_critical_attenuation :
    ∃ (L K _K_min grid_step : ℕ) (h_K_lt : K < L)
      (ΔP_out R1 R2 db_int db_u : ℕ),
      SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u) = false ∧
      SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
      CoalescedQuantizationNoise
        (NatRemainder.ofLE L K (Nat.le_of_lt h_K_lt)) grid_step <
        TotalQuantizationNoise L grid_step ∧
      0 < (NatRemainder.ofLE L K (Nat.le_of_lt h_K_lt)).remaining := by
  refine ⟨4, 2, 2, 10, by decide, 16, 2, 2, 10, 3, ?_⟩
  let geometry : FirmCoalescenceGeometry 4 2 := {
    external := NatRemainder.ofLE 4 2 (by decide)
    internalizedPositive := by decide
    externalPositive := by decide
  }
  exact viable_coalescence_critical_attenuation_window 4 2 2 10 16 2 2 10 3
    (by decide) (by decide) (by decide) (by decide) (by decide) geometry

/-- Ground instantiation of Theorem 9.6: Macro-aggregate regime non-identifiability witness. -/
theorem ground_abct_regime_non_identifiability_witness :
    ∃ (W : ActionFrame)
      (interp_absorb interp_liquidate : EconometricInterpretation W)
      (regimeOf : EconometricInterpretation W → CapitalRegime)
      (i : W.Agent) (t : W.Moment) (h : W.History),
      ObsEquiv W interp_absorb interp_liquidate i t h ∧
      regimeOf interp_absorb = CapitalRegime.Absorption ∧
      regimeOf interp_liquidate = CapitalRegime.Liquidation ∧
      regimeOf interp_absorb ≠ regimeOf interp_liquidate :=
  abct_regime_non_identifiability_witness

/-- Ground instantiation of Theorem 4.3f: Decentralized emergence of universal money. -/
theorem ground_three_agent_network_money_emergence_witness
    [∀ Γ i m, Decidable (NetworkFeasIndirect ThreeAgentTradingNetwork id
      (fun i m => (i = 0 ∧ m = 1) ∨ (i = 1 ∧ m = 2) ∨ (i = 2 ∧ m = 0)) Γ i m)] :
    let G := ThreeAgentTradingNetwork
    let supplies : Fin 3 → Fin 3 := id
    let demands : Fin 3 → Fin 3 → Prop := fun i m =>
      (i = 0 ∧ m = 1) ∨ (i = 1 ∧ m = 2) ∨ (i = 2 ∧ m = 0)
    let Γ₀ : Fin 3 → Finset (Fin 3) := fun m =>
      if m = 0 then {2} else if m = 1 then {0} else {1}
    (∀ m : Fin 3, (Γ₀ m).card = 1) ∧
    ¬ IsNetworkUniversalMoney Γ₀ 0 ∧
    ¬ IsNetworkUniversalMoney (PhiTradingNet G supplies demands Γ₀) 0 ∧
    IsNetworkUniversalMoney ((PhiTradingNet G supplies demands)^[2] Γ₀) 0 :=
  three_agent_network_money_emergence_witness

/-- Ground instantiation of Theorem 4.3a.1: Finset acceptance profiles grow
under the computable acceptance operator. -/
theorem ground_phi_inflationary [W : ActionFrame]
    (FeasIndirect : W.Agent → W.Means → Prop) (Γ : W.Means → Finset W.Agent)
    [∀ m, Decidable (IsMaxMarketable Γ m)]
    [∀ i m, Decidable (FeasIndirect i m)] :
    ProfileLE Γ (Phi FeasIndirect Γ) :=
  phi_inflationary FeasIndirect Γ

/-- Ground instantiation of Theorem 4.3a.2: Inflationary property of network operator.
    Kernel-certified with strictly zero transitive axioms (`[] (0 axioms)`). -/
theorem ground_phi_net_inflationary
    {V C : Type} [Fintype V] [DecidableEq V]
    (AdoptRule : (C → Finset V) → V → C → Prop)
    [∀ Γ i m, Decidable (AdoptRule Γ i m)]
    (Γ : C → Finset V) :
    ∀ m, Γ m ⊆ PhiNet AdoptRule Γ m := by
  intro m
  dsimp [PhiNet]
  exact Finset.subset_union_left

/-- Ground instantiation of Theorem 4.1c: Non-vacuity of Mises's Law of Association. -/
theorem ground_mises_law_of_association :
    ∃ (E : RicardianEconomy) (P : RicardianTradePlan E),
      (∀ g : Fin 2, E.a_i g < E.a_j g) ∧
      RicardianTradeGains P :=
  mises_law_of_association_non_vacuous

/-- Ground instantiation of Theorem 7.6d: Non-vacuity of purposeful firm coalescence. -/
theorem ground_firm_coalescence_separate_choice_and_signal_witness :
    ∃ (i : FiniteBranchingModel.Agent)
      (t : FiniteBranchingModel.Moment)
      (h : FiniteBranchingModel.History) (L K _K_min grid_step : ℕ)
      (ΔP_out R1 R2 db_int db_u : ℕ)
      (α_split α_merge α_socialize : FiniteBranchingModel.Action)
      (geom : FirmCoalescenceGeometry L K),
      (¬ @PurposefulAct FiniteBranchingModel i t h α_split) ∧
      (¬ @PurposefulAct FiniteBranchingModel i t h α_socialize) ∧
      (@PurposefulAct FiniteBranchingModel i t h α_merge) ∧
      (SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u) = false ∧
       SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
       CoalescedQuantizationNoise geom.external grid_step <
         TotalQuantizationNoise L grid_step ∧
       0 < geom.external.remaining) :=
  purposeful_firm_coalescence_separate_choice_and_signal_witness

/-- Ground instantiation of Theorem 3.5c: Böhm-Bawerk's roundabout productivity necessity. -/
theorem ground_bohm_bawerk_roundabout_necessity
    (i : FiniteBranchingModel.Agent) (t : FiniteBranchingModel.Moment)
    (h : FiniteBranchingModel.History) (m : FiniteBranchingModel.Means)
    (q_direct q_roundabout : ℕ) (hq : 0 < q_direct) (τ_direct τ_later : FiniteBranchingModel.Moment)
    (h_pos_tp : @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel _ m q_direct τ_direct)
      (@timedQuantityEnd FiniteBranchingModel _ m q_direct τ_later))
    (α_direct α_roundabout : FiniteBranchingModel.Action)
    (h_direct_feas : α_direct ∈ @ActionFrame.A_feas FiniteBranchingModel i t h)
    (h_direct_end : @ActionFrame.End_of FiniteBranchingModel i α_direct t h =
      @timedQuantityEnd FiniteBranchingModel _ m q_direct τ_direct)
    (h_round_end : @ActionFrame.End_of FiniteBranchingModel i α_roundabout t h =
      @timedQuantityEnd FiniteBranchingModel _ m q_roundabout τ_later)
    (h_round_purp : @PurposefulAct FiniteBranchingModel i t h α_roundabout)
    (h_sync_mono : q_roundabout ≤ q_direct →
      @Preference FiniteBranchingModel i t h
        (@timedQuantityEnd FiniteBranchingModel _ m q_direct τ_later)
        (@timedQuantityEnd FiniteBranchingModel _ m q_roundabout τ_later) ∨
      @timedQuantityEnd FiniteBranchingModel _ m q_direct τ_later =
        @timedQuantityEnd FiniteBranchingModel _ m q_roundabout τ_later)
    (h_trans : ∀ e1 e2 e3,
      @Preference FiniteBranchingModel i t h e1 e2 →
      @Preference FiniteBranchingModel i t h e2 e3 →
      @Preference FiniteBranchingModel i t h e1 e3) :
    q_direct < q_roundabout ∧
    (∃ δ_cap : ℕ, δ_cap ≥ 1 ∧ q_roundabout = q_direct + δ_cap) :=
  by
    have h_interest := purposeful_positive_originary_interest (W := FiniteBranchingModel)
      i t h m q_direct q_roundabout hq τ_direct τ_later h_pos_tp
      α_direct α_roundabout h_direct_feas h_direct_end h_round_end
      h_round_purp h_sync_mono h_trans
    exact ⟨h_interest.1, h_interest.2.2⟩

/-- Ground instantiation of Theorem 9.1: Master non-identifiability principle. -/
theorem ground_non_identifiability_of_divergent_models
    {W : ActionFrame} {Θ : Type}
    (M : Set (EconometricInterpretation W))
    (f : EconometricInterpretation W → Θ)
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (interp₁ interp₂ : EconometricInterpretation W)
    (hC₁ : interp₁ ∈ M) (hC₂ : interp₂ ∈ M)
    (h_obs : ObsEquiv W interp₁ interp₂ i t h)
    (h_diff : f interp₁ ≠ f interp₂) :
    ¬ ∃ est : EconometricEstimator W Θ, Identifies W M f est i t h :=
  non_identifiability_of_divergent_models M f i t h interp₁ interp₂ hC₁ hC₂ h_obs h_diff

/-- Ground instantiation of Theorem 10.6: Poset-theoretic behavioral anomaly embedding.
When contextual preferences are transitive, they satisfy irreflexivity, asymmetry,
and transitivity on ends. -/
theorem ground_contextual_frame_induces_strict_poset
    (W : ActionFrame) (i : W.Agent) (t : W.Moment) (h : W.History)
    (h_trans : ∀ e₁ e₂ e₃, W.Preference i t h e₁ e₂ → W.Preference i t h e₂ e₃ →
      W.Preference i t h e₁ e₃) :
    (∀ e, ¬ W.Preference i t h e e) ∧
    (∀ e₁ e₂, W.Preference i t h e₁ e₂ → ¬ W.Preference i t h e₂ e₁) ∧
    (∀ e₁ e₂ e₃, W.Preference i t h e₁ e₂ → W.Preference i t h e₂ e₃ → W.Preference i t h e₁ e₃) :=
  ⟨fun e => W.pref_irrefl i t h e, fun _ _ hp => W.pref_asymm i t h hp, h_trans⟩

/-- Ground instantiation of Theorem 4.4c: Market clearing with pairwise conservation. -/
theorem ground_multilateral_cohort_market_clearing
    [W : ActionFrame] [BilateralExchangeFrame W] (M : MultilateralCohortMarket W.Agent W.Means)
    (S : MultilateralClearingScenario M) : MultilateralClearingConclusion M S :=
  action_frame_multilateral_market_clearing M S

/-- Ground instantiation of Theorem 4.4c.1: Cohort buyer partition (intra vs extra-marginal).
    Kernel-certified with strictly zero transitive axioms (`[] (0 axioms)`). -/
theorem ground_multilateral_cohort_buyer_partition
    {V C : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V C) (P : ℕ) :
    (∀ b ∈ M.ActiveBuyers P, b ∉ M.ExtraMarginalBuyers P) ∧
    (∀ b ∈ M.Buyers, b ∈ M.ActiveBuyers P ∨ b ∈ M.ExtraMarginalBuyers P) :=
  M.buyer_partition P

/-- Ground instantiation of Theorem 4.4c.2: Cohort seller partition (intra vs extra-marginal).
    Kernel-certified with strictly zero transitive axioms (`[] (0 axioms)`). -/
theorem ground_multilateral_cohort_seller_partition
    {V C : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V C) (P : ℕ) :
    (∀ s ∈ M.ActiveSellers P, s ∉ M.ExtraMarginalSellers P) ∧
    (∀ s ∈ M.Sellers, s ∈ M.ActiveSellers P ∨ s ∈ M.ExtraMarginalSellers P) :=
  M.seller_partition P

/-- Ground instantiation of Theorem 4.4c.3: Cohort pairwise trade endowment conservation.
    Kernel-certified with strictly zero transitive axioms (`[] (0 axioms)`). -/
theorem ground_multilateral_cohort_pairwise_trade_conservation
    {V C : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V C)
    (b s : V) (hb : b ∈ M.Buyers) (hs : s ∈ M.Sellers)
    (omega_pre omega_post : V → C → ℕ)
    (m : C)
    (h_pair_conserved : omega_post b m + omega_post s m = omega_pre b m + omega_pre s m)
    (h_rest_invariant : ∀ a ∈ M.Buyers ∪ M.Sellers, a ≠ b → a ≠ s →
      omega_post a m = omega_pre a m) :
    (∑ a ∈ M.Buyers ∪ M.Sellers, omega_post a m) =
      ∑ a ∈ M.Buyers ∪ M.Sellers, omega_pre a m :=
  multilateral_cohort_pairwise_trade_conservation M b s hb hs omega_pre omega_post m
    h_pair_conserved h_rest_invariant

/-- Ground instantiation of Theorem 4.5a: Cantillon purchasing power dilution. -/
theorem ground_cantillon_network_purchasing_power_dilution
    [W : ActionFrame] (net : CantillonNetwork (W := W)) :
    net.P_pre ≤ net.M_downstream ∧
    net.M_downstream < net.P_post ∧
    net.M_downstream * net.P_pre < net.M_downstream * net.P_post := by
  have h_excl : net.M_downstream < net.P_post := by
    have h := net.h_exclusion_post
    rw [net.h_downstream_cash_unchanged] at h
    exact h
  exact ⟨net.h_solvency_pre, h_excl,
    (cantillon_network_purchasing_power_dilution net).crossProductDecline⟩

/-- Ground instantiation of Theorem 7.9: Non-vacuity of firm boundary under box coarsening. -/
theorem ground_order_theoretic_firm_boundary_non_vacuous :
    ∃ (d : ℕ) (B_int B_mkt : OrdinalPriceBox d) (Menu : Finset (InputVec d)),
      BoxCoarsening B_int B_mkt ∧
      IndeterminacyAntichainWidth d B_int Menu < IndeterminacyAntichainWidth d B_mkt Menu :=
  order_theoretic_firm_boundary_non_vacuous

/-- Ground instantiation of Theorem 8.6: Non-vacuity of factor substitution liquidation regime. -/
theorem ground_convex_substitution_regime_non_vacuous :
    ∃ (buffer_stock substitute_stock req_comp sub_penalty : ℕ),
      InNeoclassicalAbsorptionRegime buffer_stock substitute_stock req_comp ∧
      2 ≤ sub_penalty ∧
      InConvexSubstitutionLiquidationRegime buffer_stock substitute_stock req_comp sub_penalty :=
  convex_substitution_regime_non_vacuous

/-- Ground instantiation: STIT Independence of Agents in BilateralTradeActionFrame (Concern 3). -/
theorem ground_bilateral_trade_model_stit_independent :
    STITAgentIndependence BilateralTradeActionFrame BilateralMoment.root :=
  bilateral_trade_model_stit_independent

/-- Ground instantiation: Matched swap execution in BilateralTradeActionFrame (Concern 3). -/
theorem ground_bilateral_trade_model_executes_matched_swap :
    bilateral_enacted 0 .root 3 = ModelAction.offer 0 1 1 0 1 1 ∧
    bilateral_enacted 1 .root 3 = ModelAction.accept 1 0 1 0 1 1 ∧
    bilateral_omega 0 .leaf3 3 0 = 1 ∧
    bilateral_omega 0 .leaf3 3 1 = 1 ∧
    bilateral_omega 1 .leaf3 3 0 = 1 ∧
    bilateral_omega 1 .leaf3 3 1 = 1 :=
  bilateral_trade_model_executes_matched_swap

/-- Ground instantiation: Unilateral offer no-op in BilateralTradeActionFrame (Concern 3). -/
theorem ground_bilateral_trade_model_unilateral_offer_noop :
    bilateral_enacted 0 .root 1 = ModelAction.offer 0 1 1 0 1 1 ∧
    bilateral_enacted 1 .root 1 = ModelAction.idle ∧
    (∀ m : Fin 3, bilateral_omega 0 .leaf1 1 m = bilateral_omega 0 .root 1 m) :=
  bilateral_trade_model_unilateral_offer_noop

/-- Ground instantiation: Performative self-falsification under KD45 coherence (Concern 2). -/
theorem ground_deliberative_doxastic_action_denial_self_falsifying
    [W : ActionFrame]
    (i : W.Agent) (t : W.Moment) (H_t : Set W.History) (h : W.History)
    (α_assert : W.Action)
    (h_coh : InternalDoxasticCoherence (F := W) i t H_t h)
    (h_delib : DoxasticDeliberativeEpistemicAssertion (F := W) i t H_t h
      (fun h' => ¬ DoxasticAppraisalCertificate (F := W) i
        (W.tau i t h') H_t h') α_assert) :
    False :=
  deliberative_doxastic_action_denial_self_falsifying (F := W) i t H_t h α_assert h_coh h_delib

/-- Ground instantiation: Sorted cohort marginal pairs equilibrium (Concern 6). -/
theorem ground_sorted_cohort_marginal_pairs_equilibrium
    {M : Type*} {n : ℕ} (Mkt : OCGroundedCohortMarket (M := M) n) (r_star : Fin n) (P : ℕ)
    (h_clearing : Mkt.v_s (Mkt.seller_perm r_star) ≤ P ∧ P ≤ Mkt.v_b (Mkt.buyer_perm r_star)) :
    (∀ r : Fin n, r ≤ r_star → P ≤ Mkt.v_b (Mkt.buyer_perm r) ∧ Mkt.v_s (Mkt.seller_perm r) ≤ P) :=
  sorted_cohort_marginal_pairs_equilibrium Mkt r_star P h_clearing

/-- Ground instantiation: Simultaneous multilateral trade conservation (Concern 6). -/
theorem ground_simultaneous_multilateral_trade_conservation
    {V M : Type*} [DecidableEq V] [DecidableEq M]
    {P : ℕ} {m_good m_money : M} {pairs : List (V × V)}
    {ω ω' : InventoryLedger V M}
    (_h_goods_money : m_good ≠ m_money)
    (run : TransferRun P m_good m_money pairs ω ω')
    (Cohort : Finset V)
    (h_in_cohort : ∀ p ∈ pairs, p.1 ∈ Cohort ∧ p.2 ∈ Cohort) (m : M) :
    ∑ a ∈ Cohort, ω' a m = ∑ a ∈ Cohort, ω a m :=
  simultaneous_multilateral_trade_conservation run Cohort h_in_cohort m

/-- Ground instantiation: Precautionary cash demand increases under price box widening. -/
theorem ground_box_widening_increases_precautionary_cash_demand {d : ℕ}
    (B1 B2 : FactorPriceBox d) (x : Fin d → ℕ)
    (h_widen : PriceBoxWidening B1 B2) :
    PrecautionaryCashDemand B1 x ≤ PrecautionaryCashDemand B2 x :=
  box_widening_increases_precautionary_cash_demand B1 B2 x h_widen

/-- Ground instantiation: Solvent cash-acceptance profile contracts under price box widening. -/
theorem ground_box_widening_contracts_solvent_profile
    {V M : Type*} [DecidableEq V] {d : ℕ}
    (ω : V → M → ℕ) (m_money : M)
    (B1 B2 : FactorPriceBox d) (x : V → Fin d → ℕ) (Cohort : Finset V)
    (h_widen : PriceBoxWidening B1 B2) :
    CashBackedAcceptanceProfile ω m_money B2 x Cohort ⊆
      CashBackedAcceptanceProfile ω m_money B1 x Cohort :=
  box_widening_contracts_solvent_profile ω m_money B1 B2 x Cohort h_widen

/-- Ground instantiation: Multi-hop money emergence collapses price boxes and expands solvency. -/
theorem ground_network_money_emergence_narrows_price_box_and_expands_solvency
    [W : ActionFrame] [Finite W.Means]
    (G : TradingNetwork W.Agent) (Supplies : W.Agent → W.Means) (Demands : W.Agent → W.Means → Prop)
    [∀ Γ i m, Decidable (NetworkFeasIndirect G Supplies Demands Γ i m)]
    (seed : W.Agent) (m_star : W.Means) (Γ₀ : W.Means → Finset W.Agent)
    (h_seed : seed ∈ Γ₀ m_star)
    (h_conn : NetworkWantsConnected G Supplies Demands seed)
    {d : ℕ} (sched : NetworkPriceBoxSchedule (V := W.Agent) (M := W.Means) d)
    (ω : W.Agent → W.Means → ℕ) (x : W.Agent → Fin d → ℕ) (Cohort : Finset W.Agent) :
    ∃ (Γ_star : W.Means → Finset W.Agent) (n : ℕ),
      Γ_star = (PhiTradingNet G Supplies Demands)^[n] Γ₀ ∧
      IsNetworkUniversalMoney Γ_star m_star ∧
      PriceBoxWidening (sched.boxOf Γ_star) (sched.boxOf Γ₀) ∧
      (∀ i : W.Agent, PrecautionaryCashDemand (sched.boxOf Γ_star) (x i) ≤
                    PrecautionaryCashDemand (sched.boxOf Γ₀) (x i)) ∧
      CashBackedAcceptanceProfile ω m_star (sched.boxOf Γ₀) x Cohort ⊆
      CashBackedAcceptanceProfile ω m_star (sched.boxOf Γ_star) x Cohort := by
  have : Fintype W.Means := Fintype.ofFinite W.Means
  exact network_money_emergence_narrows_price_box_and_expands_solvency G Supplies Demands seed
    m_star Γ₀ h_seed h_conn sched ω x Cohort

/-- Ground instantiation: Multi-hop Cantillon diffusion crowds out downstream agents (Concern 6). -/
theorem ground_cantillon_hop_shifts_clearing_price_and_crowds_out_downstream
    {V : Type} [DecidableEq V]
    (diff : CantillonNetworkDiffusion V) (v_b : V → ℕ)
    (d : ℕ) (P_pre P_wave : ℕ)
    (j : V) (h_downstream : d < diff.hop_dist j)
    (h_intra_pre : P_pre ≤ v_b j)
    (h_below_wave : v_b j < P_wave) :
    P_pre ≤ diff.effective_bid v_b 0 j ∧
    diff.effective_bid v_b d j < P_wave :=
  cantillon_hop_shifts_clearing_price_and_crowds_out_downstream diff v_b d P_pre P_wave j
    h_downstream h_intra_pre h_below_wave

/-- Ground instantiation: Firm coalescence shrinks indeterminacy width under price bounds. -/
theorem ground_firm_coalescence_shrinks_indeterminacy_width (d : ℕ)
    (C_firm C_mkt : StageCoarseningMap d) (B : OrdinalPriceBox d) (Menu : Finset (InputVec d))
    (h_coarsen : BoxCoarsening (C_firm.coarsen B) (C_mkt.coarsen B)) :
    IndeterminacyAntichainWidth d (C_firm.coarsen B) Menu ≤
    IndeterminacyAntichainWidth d (C_mkt.coarsen B) Menu :=
  firm_coalescence_shrinks_indeterminacy_width d C_firm C_mkt B Menu h_coarsen

/-- Ground instantiation: Generalized liquidation boundary with discrete substitution penalty. -/
theorem ground_convex_penalized_liquidation_regime_boundary
    (buffer_stock substitute_stock req_comp sub_penalty : ℕ) :
    InConvexSubstitutionLiquidationRegime
      buffer_stock substitute_stock req_comp sub_penalty ↔
    ¬ CanCompleteWithSubstitutes buffer_stock substitute_stock req_comp sub_penalty :=
  convex_penalized_liquidation_regime_boundary buffer_stock substitute_stock req_comp sub_penalty

/-- Ground instantiation: Order book trade execution conserves endowments and solvency. -/
theorem ground_multilateral_market_book_trade_conserved_and_solvent
    {V M : Type*} [DecidableEq V] [DecidableEq M]
    (B : MultilateralMarketBook V M) (m : M) :
    (∀ a, 0 ≤ B.after a m) ∧
      ∑ a ∈ B.Traders, B.after a m = ∑ a ∈ B.Traders, B.ω a m :=
  multilateral_market_book_trade_conserved_and_solvent B m

/-- Ground instantiation of the appraisal-certificate bridge to `PurposefulAct`.
The certificate records scenario appraisal evidence; it is not a second
purposefulness predicate. -/
theorem ground_purposeful_act_of_doxastic_appraisal
    (W : ActionFrame) (i : W.Agent) (t : W.Moment) (H_t : Set W.History) (h : W.History)
    (h_mem : W.mem_hist t h)
    (h_projected : W.ProjectedFeasibility)
    (h_app : W.IsUnanimousAppraisal i t h)
    (h_dox : DoxasticAppraisalCertificate (F := W) i t H_t h) :
    PurposefulAct (F := W) i t h (W.enacted i t h) :=
  purposeful_act_of_doxastic_dominance (F := W) i t H_t h h_mem h_projected h_app h_dox

/-- Ground instantiation of the singleton appraisal-certificate equivalence. -/
theorem ground_purposeful_act_iff_doxastic_appraisal_certificate
    (W : ActionFrame) (i : W.Agent) (t : W.Moment) (H_t : Set W.History) (h : W.History)
    (h_mem : W.mem_hist t h)
    (h_in : h ∈ H_t)
    (h_base : W.alpha_zero ∈ W.A_feas i t h)
    (h_branch : BranchFeas (F := W) i t H_t W.alpha_zero)
    (h_pl : W.History)
    (h_singleton : W.MinPlausible i t = {h_pl})
    (h_projected : W.ProjectedFeasibility)
    (h_unease : W.Preference i t h
      (W.End_of i (W.enacted i t h) t h) (W.End_of i W.alpha_zero t h)) :
    PurposefulAct (F := W) i t h (W.enacted i t h) ↔
      DoxasticAppraisalCertificate (F := W) i t H_t h :=
  purposeful_act_iff_doxastic_purposeful_act_singleton (F := W) i t H_t h h_mem h_in
    h_base h_branch h_pl h_singleton h_projected h_unease

/-- Ground instantiation of Theorem 11.2: Calhoun's fiscal class partition. -/
theorem ground_calhoun_fiscal_class_partition [W : ActionFrame]
    (F : FiscalTransferSystem W) (s : W.Agent) (hs_consumer : IsNetTaxConsumer F s) :
    ∃ b : W.Agent, IsNetTaxpayer F b :=
  calhoun_fiscal_class_partition F s hs_consumer

/-- Ground instantiation of Theorem 11.2': Calhoun partition in ActionFrame transitions. -/
theorem ground_calhoun_action_frame_class_partition
    [W : ActionFrame]
    (Cohort : Finset W.Agent) (t t' : W.Moment) (h : W.History) (m : W.Means)
    (deadweight_loss : ℕ)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_nontrade : ∀ a ∈ Cohort, ¬ W.IsTradeAction (W.enacted a t h))
    (h_uninvaded : ∀ a ∈ Cohort, ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) a)
    (h_transfer_balance : (∑ a ∈ Cohort, W.yield_means (W.enacted a t h) m) + deadweight_loss =
      ∑ a ∈ Cohort, W.use_means (W.enacted a t h) m)
    (s : W.Agent) (hs_mem : s ∈ Cohort)
    (hs_gain : W.omega s t h m < W.omega s t' h m) :
    ∃ b : W.Agent, b ∈ Cohort ∧ W.omega b t' h m < W.omega b t h m :=
  calhoun_action_frame_class_partition Cohort t t' h m deadweight_loss
    h_next h_nontrade h_uninvaded h_transfer_balance s hs_mem hs_gain

/-- Ground instantiation of Theorem 11.2'': Calhoun partition in multi-moment inventory runs. -/
theorem ground_calhoun_action_frame_run_class_partition
    [W : ActionFrame] [BilateralExchangeFrame W]
    (Cohort : Finset W.Agent) {t u : W.Moment} {h : W.History}
    (runs : (a : W.Agent) → InventoryRun W a h t u) (m : W.Means)
    (deadweight_loss : ℕ)
    (h_run_balance : (∑ a ∈ Cohort, (runs a).totalYield m) + deadweight_loss =
      ∑ a ∈ Cohort, (runs a).totalUse m)
    (s : W.Agent) (hs_mem : s ∈ Cohort)
    (hs_gain : W.omega s t h m < W.omega s u h m) :
    ∃ b : W.Agent, b ∈ Cohort ∧ W.omega b u h m < W.omega b t h m :=
  calhoun_action_frame_run_class_partition Cohort runs m deadweight_loss
    h_run_balance s hs_mem hs_gain

/-- Ground instantiation of Knaster-Tarski non-monotonicity countermodel (Finset). -/
theorem ground_concrete_phi_non_monotone_witness :
    let Agent := Fin 3
    let Means := Fin 2
    let IsMax := fun (Γ : Means → Finset Agent) (m : Means) => ∀ m', (Γ m').card ≤ (Γ m).card
    let PhiOp := fun (Γ : Means → Finset Agent) (m : Means) =>
      Γ m ∪ Finset.univ.filter (fun _ => IsMax Γ m)
    ∃ (Γ1 Γ2 : Means → Finset Agent),
      (∀ m, Γ1 m ⊆ Γ2 m) ∧
      ¬ (∀ m, PhiOp Γ1 m ⊆ PhiOp Γ2 m) :=
  concrete_phi_non_monotone_witness

/-- Ground instantiation of Theorem 7.9: Refutation of Arithmetic Integration Fallacy. -/
theorem ground_vertical_integration_stage_count_fallacy_refuted :
    (∀ s, PolicyCorrect .bothSignals s) ∧
    (∀ s, PolicyCorrect .factorRestored s) ∧
    (¬ ∃ π : Bool × Bool → FirmProductionDecision,
      ∀ s, π (informationObservation .factorHidden s) = firmRequiredDecision s) ∧
    (¬ ∃ π : Bool × Bool → FirmProductionDecision,
      ∀ s, π (informationObservation .demandHidden s) = firmRequiredDecision s) :=
  vertical_integration_stage_count_fallacy_refuted

/-- Ground instantiation of Theorem 11.6: State Monopoly Political Economy Master Synthesis. -/
theorem ground_state_monopoly_master_synthesis [W : ActionFrame] {i j : W.Agent}
    {t : W.Moment} {h : W.History}
    (S : StateMonopolyMasterEvidence (W := W) (i := i) (j := j) (t := t) (h := h)) :
    StateMonopolyMasterConclusion S :=
  state_monopoly_political_economy_master_synthesis S

/-- Ground instantiation of Lockean homesteading non-invasiveness:
A pure production action strictly increases the homesteading agent's stock
while preserving all other agents' stocks and feasible menus. -/
theorem ground_lockean_homesteading_non_invasive
    [W : ActionFrame] {i j : W.Agent} {t t' : W.Moment} {h : W.History}
    {α : W.Action} {m : W.Means}
    (h_home : IsLockeanHomesteading α m)
    (h_exec_i : W.enacted i t h = α)
    (h_passive_j : W.enacted j t h = W.alpha_zero)
    (h_uninvaded_i : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) i)
    (h_uninvaded_j : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) j)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    W.omega i t h m < W.omega i t' h m ∧
    (∀ m', W.omega j t' h m' = W.omega j t h m') ∧
    ResourceMenuPreserved j t t' h :=
  lockean_homesteading_non_invasive h_home h_exec_i h_passive_j h_uninvaded_i h_uninvaded_j h_next

/-- Ground instantiation of simultaneous contemplation on unowned external resources:
Contemplated actions requiring unowned resources are already infeasible at t;
first appropriation leaves bystanders uncontracted; protection attaches at t'. -/
theorem ground_unowned_resource_contemplation_not_feasible
    [W : ActionFrame] {i j : W.Agent} {t t' : W.Moment} {h : W.History}
    {α β : W.Action} {m : W.Means}
    (h_unowned_j : W.omega j t h m = 0)
    (h_req_β : 0 < W.use_means β m)
    (h_home : IsLockeanHomesteading α m)
    (h_exec_i : W.enacted i t h = α)
    (h_passive_j : W.enacted j t h = W.alpha_zero)
    (h_uninvaded_i : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) i)
    (h_uninvaded_j : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) j)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    β ∉ W.A_feas j t h ∧
    W.omega i t h m < W.omega i t' h m ∧
    StockPreserved j t t' h ∧
    ResourceMenuPreserved j t t' h ∧
    ∀ γ, ¬ FeasibleMenuStripped j t t' h γ :=
  unowned_resource_contemplation_not_feasible_and_first_appropriation_non_invasive
    h_unowned_j h_req_β h_home h_exec_i h_passive_j h_uninvaded_i h_uninvaded_j h_next

/-- Ground instantiation of the Thief-and-Baker path-dependent title trace:
Baker recovering stolen flour from thief is restitution, preserving clean title,
hence is NOT a path-dependent invasion despite contracting thief's physical stock. -/
theorem ground_theft_and_restitution_conclusion
    [W : ActionFrame] (T : TheftAndRestitutionTrace) : TheftAndRestitutionConclusion T :=
  theft_and_restitution_conclusion T

theorem ground_baker_recovery_not_path_dependent_invasion
    [W : ActionFrame]
    (baker thief : W.Agent) (flour : W.Means) (q : ℕ)
    (h_ne : thief ≠ baker)
    (t0 t1 t2 : W.Moment) (h : W.History)
    (title : W.Agent → W.Means → ℕ)
    (h_clean0 : ∀ a m, W.omega a t0 h m = title a m)
    (h_avail0 : q ≤ W.omega baker t0 h flour)
    (h_next01 : IsNextMoment W.Precedence W.mem_hist t0 t1 h)
    (α_loss α_gain : W.Action)
    (h_not_tr_loss : ¬ W.IsTradeAction α_loss)
    (h_not_tr_gain : ¬ W.IsTradeAction α_gain)
    (h_uninv_loss : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t0 h) baker)
    (h_uninv_gain : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t0 h) thief)
    (h_loss_u : W.use_means α_loss flour = q)
    (h_loss_y : W.yield_means α_loss flour = 0)
    (h_gain_u : W.use_means α_gain flour = 0)
    (h_gain_y : W.yield_means α_gain flour = q)
    (h_enact_loss0 : W.enacted baker t0 h = α_loss)
    (h_enact_gain0 : W.enacted thief t0 h = α_gain)
    (h_next12 : IsNextMoment W.Precedence W.mem_hist t1 t2 h)
    (α_surrender α_recov : W.Action)
    (h_not_tr_surr : ¬ W.IsTradeAction α_surrender)
    (h_not_tr_rec : ¬ W.IsTradeAction α_recov)
    (h_uninv_surr : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t1 h) thief)
    (h_uninv_rec : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t1 h) baker)
    (h_surr_u : W.use_means α_surrender flour = q)
    (h_surr_y : W.yield_means α_surrender flour = 0)
    (h_rec_u : W.use_means α_recov flour = 0)
    (h_rec_y : W.yield_means α_recov flour = q)
    (h_enact_surr1 : W.enacted thief t1 h = α_surrender)
    (h_enact_rec1 : W.enacted baker t1 h = α_recov) :
    (0 < q → IsPathDependentTitleInvasion title baker t0 t1 h flour) ∧
    (0 < q → IsPresentMomentReduction thief t1 t2 h flour) ∧
    ¬ IsPathDependentTitleInvasion title thief t1 t2 h flour ∧
    W.omega baker t2 h flour = title baker flour :=
  baker_recovery_restitution_not_path_dependent_invasion
    baker thief flour q h_ne t0 t1 t2 h title h_clean0 h_avail0
    h_next01 α_loss α_gain h_not_tr_loss h_not_tr_gain h_uninv_loss h_uninv_gain
    h_loss_u h_loss_y h_gain_u h_gain_y
    h_enact_loss0 h_enact_gain0 h_next12 α_surrender α_recov h_not_tr_surr h_not_tr_rec
    h_uninv_surr h_uninv_rec
    h_surr_u h_surr_y h_rec_u h_rec_y h_enact_surr1 h_enact_rec1

/-- Ground instantiation of targeted complementary factor sabotage:
Stripping a single unit of a complementary factor strands the integrated capital
bundle, reducing usable capital to zero and establishing strict teleological dominance. -/
theorem ground_targeted_sabotage_teleological_dominance
    [W : ActionFrame] {i : W.Agent} {t : W.Moment} {h : W.History}
    {completion : W.Action} {m_cap m_comp : W.Means} {q_comp : ℕ}
    (S : TargetedComplementarySabotage i t h completion m_cap m_comp q_comp)
    (req : W.Ends → W.Means → ℕ) (e_target : W.Ends)
    (h_target_comp : req e_target m_comp = q_comp)
    (h_target_other : ∀ m ≠ m_comp, req e_target m ≤ W.omega i t h m) :
    TeleologicalBundleDominates req
      (fun m => W.omega i t h m)
      (TargetedComplementarySabotage.postSabotageStock i t h m_comp q_comp) :=
  S.targeted_sabotage_teleological_dominance req e_target h_target_comp h_target_other

/-- Ground instantiation of collateral custody upon default:
Because collateral custody is transferred at origination, default retention
by the lender at maturity requires no invasive seizure, preserving borrower stock and menu. -/
theorem ground_unpaid_maturity_borrower_menu_preserved
    [W : ActionFrame] [BilateralExchangeFrame W] {T : PawnLoanTerms W} {A : CreditAdvance T}
    (D : UnpaidMaturity A)
    (t_post : W.Moment)
    (h_succ : IsNextMoment W.Precedence W.mem_hist T.maturity t_post A.history)
    (h_borrower_uninvaded : ∀ j, ¬ W.IsInvasiveOn (W.enacted j T.maturity A.history) T.borrower)
    (h_borrower_idle : W.enacted T.borrower T.maturity A.history = W.alpha_zero) :
    ResourceMenuPreserved T.borrower T.maturity t_post A.history :=
  D.borrower_resource_menu_preserved t_post h_succ h_borrower_uninvaded h_borrower_idle

/-- Ground instantiation of state extraction vs clean title:
In a cohort where initial possession equals clean title, any state beneficiary
necessitates at least one net taxpayer undergoing an extractive transfer that
drives their physical possession below legitimate clean title. -/
theorem ground_calhoun_title_partition [W : ActionFrame]
    (T : TitleAnchoredCohortTransfer W)
    (h_clean_init : ∀ a ∈ T.Cohort, T.pos_pre a = T.title a)
    (beneficiary : W.Agent) (h_ben_mem : beneficiary ∈ T.Cohort)
    (h_ben_gain : T.pos_pre beneficiary < T.pos_post beneficiary) :
    ∃ taxpayer : W.Agent, IsExtractiveTransfer T taxpayer :=
  calhoun_title_partition T h_clean_init beneficiary h_ben_mem h_ben_gain

/-- Ground instantiation of purposeful Lockean homesteading non-invasiveness:
Purposeful first appropriation improves the appropriator over inertia, expands stock,
and leaves bystander stocks and feasible menus unstripped. -/
theorem ground_purposeful_lockean_homesteading_non_invasive
    [W : ActionFrame] {i j : W.Agent} {t t' : W.Moment} {h : W.History}
    {α : W.Action} {m : W.Means}
    (h_home : PurposefulLockeanHomesteading i t h α m)
    (h_passive_j : W.enacted j t h = W.alpha_zero)
    (h_uninvaded_i : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) i)
    (h_uninvaded_j : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) j)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    W.Preference i t h (W.End_of i α t h) (W.End_of i W.alpha_zero t h) ∧
    W.omega i t h m < W.omega i t' h m ∧
    (∀ m', W.omega j t' h m' = W.omega j t h m') ∧
    ResourceMenuPreserved j t t' h ∧
    ∀ γ, ¬ FeasibleMenuStripped j t t' h γ :=
  purposeful_lockean_homesteading_non_invasive h_home h_passive_j h_uninvaded_i h_uninvaded_j h_next

/-- Ground instantiation of the Action-Axiom equivalence between endogenous invasion
and feasible-menu stripping under tight-action richness. -/
theorem ground_endogenous_invasion_iff_menu_stripping
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (h_rich : ∀ m : W.Means, ∃ β, (∀ m', W.use_means β m' ≤ W.omega i t h m') ∧
      W.use_means β m = W.omega i t h m)
    (α_j : W.Action) :
    EndogenouslyInvasiveJ i j t h α_j ↔ MenuStrippingInvasiveJ i j t h α_j :=
  endogenous_invasion_iff_menu_stripping h_rich α_j

/-- Ground instantiation of ActionFrame physical invasion menu stripping:
Invading j against i contracts clean-title stock and strips tight actions from i's menu. -/
theorem ground_actionFrame_invasion_strips_feasible_menu
    [W : ActionFrame]
    (i j : W.Agent) (t t' : W.Moment) (h : W.History)
    (title : W.Agent → W.Means → ℕ) (α_j : W.Action) (m_inv : W.Means) (β : W.Action)
    (ht : W.mem_hist t h)
    (ht_branch : W.mem_hist t (jointBranch i j t h W.alpha_zero α_j))
    (h_clean : ∀ m, title i m ≤ W.omega i t h m)
    (h_contract : W.omega i t' (jointBranch i j t h W.alpha_zero α_j) m_inv < title i m_inv)
    (h_feas : β ∈ W.A_feas i t h)
    (h_cont : β ∈ W.A_cont i t' (jointBranch i j t h W.alpha_zero α_j))
    (h_tight : W.use_means β m_inv = title i m_inv) :
    FeasibleMenuStripped i t t' (jointBranch i j t h W.alpha_zero α_j) β ∧
    IsPathDependentTitleInvasion title i t t'
      (jointBranch i j t h W.alpha_zero α_j) m_inv :=
  actionFrame_invasion_strips_menu_of_history i j t t' h title α_j m_inv β
    ht ht_branch h_clean h_contract h_feas h_cont h_tight

/-- Ground instantiation of Catallactic Bottleneck Pre-Emption:
When rival bidding exhausts a complementary factor at a common supplier,
the passive entrepreneur's physical stock and autarkic resource menu remain
strictly preserved (no direct invasion), yet stage-2 project completion is
rendered physically infeasible (BlockedCompletion). -/
theorem ground_catallactic_bottleneck_preemption_preserves_menu_but_blocks_completion
    [W : ActionFrame] [BilateralExchangeFrame W]
    (i : W.Agent) (t t' : W.Moment) (h : W.History)
    (completion : W.Action) (complementary : W.Means)
    (h_passive_i : W.enacted i t h = W.alpha_zero)
    (h_uninvaded_i : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) i)
    (h_starve_i : W.omega i t h complementary = 0)
    (h_req : 0 < W.use_means completion complementary)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    StockPreserved i t t' h ∧
    ResourceMenuPreserved i t t' h ∧
    (∀ γ, ¬ FeasibleMenuStripped i t t' h γ) ∧
    W.omega i t' h complementary = 0 ∧
    BlockedCompletion i t' h completion :=
  catallactic_bottleneck_preemption_preserves_menu_but_blocks_completion
    i t t' h completion complementary h_passive_i h_uninvaded_i h_starve_i h_req h_next

/-- Ground instantiation of Catallactic Bottleneck Pre-Emption Cycle Regret:
Derives the complete entrepreneurial cycle conclusion under factor starvation. -/
theorem ground_catallactic_bottleneck_preemption_cycle_regret
    [W : ActionFrame] [BilateralExchangeFrame W] {Context : Type}
    (S : EntrepreneurialCycleScenario W Context)
    (h_starve : W.omega S.investment.i S.investment.next S.investment.x.history
      S.investment.complementary = 0)
    (h_req : 0 < W.use_means S.investment.completion S.investment.complementary)
    (purposeful : PurposefulAct S.investment.i S.investment.x.moment
      S.investment.x.history S.investment.investment) :
    EntrepreneurialCycleConclusion S ∧
    BlockedCompletion S.investment.i S.investment.next S.investment.x.history
      S.investment.completion :=
  catallactic_bottleneck_preemption_cycle_regret S h_starve h_req purposeful

/-- Ground instantiation of Strategic Default vs. Illiquidity Non-Identifiability:
External historical observation of default (inaction `alpha_zero` at maturity)
cannot distinguish between hard physical illiquidity and strategic default. -/
theorem ground_default_illiquidity_vs_strategic_non_identifiability
    {W : ActionFrame}
    (M : Set (EconometricInterpretation W))
    (causeOf : EconometricInterpretation W → DefaultCause)
    (borrower : W.Agent) (t_mat : W.Moment) (h : W.History)
    (interp_illiq interp_strat : EconometricInterpretation W)
    (h_illiq : interp_illiq ∈ M)
    (h_strat : interp_strat ∈ M)
    (h_obs : ObsEquiv W interp_illiq interp_strat borrower t_mat h)
    (h_diff_cause : causeOf interp_illiq ≠ causeOf interp_strat) :
    ¬ ∃ est : EconometricEstimator W DefaultCause,
      Identifies W M causeOf est borrower t_mat h :=
  default_illiquidity_vs_strategic_non_identifiability
    M causeOf borrower t_mat h interp_illiq interp_strat h_illiq h_strat h_obs h_diff_cause

/-- Ground witness of Default Cause Non-Identifiability on FiniteBranchingModel. -/
theorem ground_default_cause_non_identifiability_witness :
    ∃ (W : ActionFrame)
      (interp_illiq interp_strat : EconometricInterpretation W)
      (causeOf : EconometricInterpretation W → DefaultCause)
      (borrower : W.Agent) (t_mat : W.Moment) (h : W.History),
      ObsEquiv W interp_illiq interp_strat borrower t_mat h ∧
      causeOf interp_illiq = DefaultCause.Illiquidity ∧
      causeOf interp_strat = DefaultCause.Strategic ∧
      causeOf interp_illiq ≠ causeOf interp_strat :=
  default_cause_non_identifiability_witness

/-- Ground instantiation of Network Liquidity-Freeze Cascades:
Contraction of an intermediary's liquid reserves after credit origination
propagates a settlement freeze and strips feasible spot-trade actions downstream,
even though aggregate media is 100% conserved across the economy. -/
theorem ground_network_liquidity_freeze_cascade
    [W : ActionFrame] [BilateralExchangeFrame W]
    (sellerA intermediaryB : W.Agent)
    (issuer : W.Agent)
    (t t' : W.Moment) (h : W.History)
    (T_BC : PawnLoanTerms W) (A_BC : CreditAdvance T_BC)
    (h_lender : T_BC.lender = intermediaryB)
    (h_uninv_idle : ∀ a, a ≠ T_BC.lender → a ≠ T_BC.borrower →
      ∀ j, ¬ W.IsInvasiveOn (W.enacted j A_BC.moment A_BC.history) a)
    (h_idle : ∀ a, a ≠ T_BC.lender → a ≠ T_BC.borrower →
      W.enacted a A_BC.moment A_BC.history = W.alpha_zero)
    (h_succ : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_uninv_B : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) intermediaryB)
    (qA : ℕ) (mA : W.Means) (price : ℕ)
    (h_short : W.omega intermediaryB t h T_BC.money < price)
    (h_freeze : W.enacted intermediaryB t h = W.alpha_zero) :
    totalMedia issuer T_BC.money A_BC.nextMoment A_BC.history =
      totalMedia issuer T_BC.money A_BC.moment A_BC.history ∧
    W.omega intermediaryB A_BC.nextMoment A_BC.history T_BC.money + T_BC.principal =
      W.omega intermediaryB A_BC.moment A_BC.history T_BC.money ∧
    (∀ β : W.Action,
      β ∈ W.A_feas intermediaryB A_BC.moment A_BC.history →
      β ∈ W.A_cont intermediaryB A_BC.nextMoment A_BC.history →
      W.use_means β T_BC.money = W.omega intermediaryB A_BC.moment A_BC.history T_BC.money →
      FeasibleMenuStripped intermediaryB A_BC.moment A_BC.nextMoment A_BC.history β) ∧
    W.Accept intermediaryB sellerA qA mA price T_BC.money ∉ W.A_feas intermediaryB t' h ∧
    ¬ @PurposefulAct W intermediaryB t' h
      (W.Accept intermediaryB sellerA qA mA price T_BC.money) :=
  network_liquidity_freeze_cascade sellerA intermediaryB issuer
    t t' h T_BC A_BC h_lender h_uninv_idle h_idle h_succ h_uninv_B
    qA mA price h_short h_freeze

/-- Ground instantiation of Compositionally Self-Falsifying Cohort Forecasts:
A cohort of entrepreneurs facing shared factor demand simultaneously experience
pre-commitment affordability, factor-price squeeze leading to completion infeasibility,
and clustered entrepreneurial regret. -/
theorem ground_supplied_price_squeeze_yields_blockage_and_regret
    {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    {C : CreditShockCohort W Context Entrepreneur} {d : ℕ}
    (S : PriceSqueezeCohort C d) :
    (∀ e ∈ S.affected,
      PrecautionaryCashDemand S.response.preBox (S.quantity e) ≤
        W.omega (C.agent e) S.next S.history S.money) ∧
    (∀ e ∈ S.affected,
      (C.project e).cycle.investment.completion ∉
        W.A_feas (C.agent e) S.next S.history) ∧
    (∃ projects : Finset Entrepreneur,
      projects.card ≥ S.minimumFailures ∧
      (∀ e ∈ projects, e ∈ S.affected) ∧
      ∀ e ∈ projects, EntrepreneurialCycleConclusion (C.project e).cycle) ∧
    (∃ e₁ e₂, e₁ ∈ C.entrepreneurs ∧ e₂ ∈ C.entrepreneurs ∧ e₁ ≠ e₂ ∧
      C.agent e₁ ≠ C.agent e₂ ∧
      EntrepreneurialCycleConclusion (C.project e₁).cycle ∧
      EntrepreneurialCycleConclusion (C.project e₂).cycle) :=
  PriceSqueezeCohort.supplied_price_squeeze_yields_blockage_and_regret S

/-- Ground instantiation of Lockean proviso feasibility under alternative abundance:
When bystander `j` contemplates a distinct homesteading action `β` for `m_alt`, `β` requires
zero prior means and remains feasible across `i`'s appropriation of `m`. -/
theorem ground_lockean_proviso_abundant_alternative_remains_feasible
    {W : ActionFrame} {i j : W.Agent} {t t' : W.Moment} {h : W.History}
    {α β : W.Action} {m m_alt : W.Means}
    (h_home_j : IsLockeanHomesteading β m_alt)
    (h_cont_t : β ∈ W.A_cont j t h)
    (h_cont_t' : β ∈ W.A_cont j t' h)
    (h_homestead_i : IsLockeanHomesteading α m)
    (h_exec_i : W.enacted i t h = α)
    (h_passive_j : W.enacted j t h = W.alpha_zero)
    (h_uninvaded_i : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) i)
    (h_uninvaded_j : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) j)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    β ∈ W.A_feas j t h ∧
    β ∈ W.A_feas j t' h ∧
    W.omega i t h m < W.omega i t' h m ∧
    StockPreserved j t t' h ∧
    ResourceMenuPreserved j t t' h :=
  lockean_proviso_abundant_alternative_remains_feasible
    h_home_j h_cont_t h_cont_t' h_homestead_i h_exec_i h_passive_j
    h_uninvaded_i h_uninvaded_j h_next

/-- Ground instantiation of sole resource appropriation:
When an unappropriated resource `m` is unowned by bystander `j`, actions requiring `m` were
already infeasible at `t`, so `i`'s appropriation strips zero feasible actions from `j`. -/
theorem ground_sole_resource_appropriation_preserves_feasible_menu
    {W : ActionFrame} {i j : W.Agent} {t t' : W.Moment} {h : W.History}
    {α γ : W.Action} {m : W.Means}
    (h_unowned_j : W.omega j t h m = 0)
    (h_req_γ : 0 < W.use_means γ m)
    (h_homestead_i : IsLockeanHomesteading α m)
    (h_exec_i : W.enacted i t h = α)
    (h_passive_j : W.enacted j t h = W.alpha_zero)
    (h_uninvaded_i : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) i)
    (h_uninvaded_j : ∀ k, ¬ W.IsInvasiveOn (W.enacted k t h) j)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    γ ∉ W.A_feas j t h ∧
    W.omega i t h m < W.omega i t' h m ∧
    StockPreserved j t t' h ∧
    ResourceMenuPreserved j t t' h ∧
    (∀ β, ¬ FeasibleMenuStripped j t t' h β) :=
  sole_resource_appropriation_preserves_feasible_menu
    h_unowned_j h_req_γ h_homestead_i h_exec_i h_passive_j
    h_uninvaded_i h_uninvaded_j h_next

/-- Ground instantiation of invasion precluding respondent gain:
When `j`'s invasive action physically contracts `i`'s stock of means `m` below the requirement
for a valued end `e` that `i`'s baseline stock attains, `i`'s baseline bundle teleologically
dominates the invaded bundle, precluding respondent gain. -/
theorem ground_physical_invasion_depriving_valued_end_precludes_respondent_gain
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (α_i α_j : W.Action) (m : W.Means) (e : W.Ends)
    (b_base b_inv : W.Means → ℕ)
    (h_base_end : jointEndI i j t h W.alpha_zero W.alpha_zero = W.BundleEnd b_base)
    (h_inv_end : jointEndI i j t h α_i α_j = W.BundleEnd b_inv)
    (h_valued : W.ValuedEnd i t h e)
    (h_unique : ∀ e', W.ValuedEnd i t h e' → e' = e)
    (h_req_base : ∀ m', W.requirement e m' ≤ b_base m')
    (h_inv_short : b_inv m < W.requirement e m) :
    ¬ W.Preference i t h (jointEndI i j t h α_i α_j)
        (jointEndI i j t h W.alpha_zero W.alpha_zero) :=
  physical_invasion_depriving_valued_end_precludes_respondent_gain
    α_i α_j m e b_base b_inv h_base_end h_inv_end h_valued h_unique h_req_base h_inv_short

/-- Ground instantiation of the pairwise mutual exclusivity across all ten bilateral
interaction classes: voluntary exchange, coercive extortion, market competition,
autarkic non-interference, unilateral gift, pure destructive aggression, restitution recovery,
mutual combat, coordination failure, and passive inaction (all 45 pairs). -/
theorem ground_praxeological_interaction_classes_pairwise_mutual_exclusivity
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (title_i : W.Means → ℕ) (α_i α_j : W.Action) :
    ¬ (IsVoluntaryExchange i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsVoluntaryExchange i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsCoerciveExtortion i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧ IsUnilateralGift i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsPureDestructiveAggression i j t h title_i α_i α_j ∧
        IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsPureDestructiveAggression i j t h title_i α_i α_j ∧
        IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsPureDestructiveAggression i j t h title_i α_i α_j ∧
        IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsPureDestructiveAggression i j t h title_i α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsRestitutionRecovery i j t h title_i α_i α_j ∧
        IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsRestitutionRecovery i j t h title_i α_i α_j ∧
        IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsRestitutionRecovery i j t h title_i α_i α_j ∧
        IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsAutarkicNonInterference i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsUnilateralGift i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsAutarkicNonInterference i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsUnilateralGift i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsMutualCombat i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsAutarkicNonInterference i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsUnilateralGift i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsMutualCombat i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsCoordinationFailure i j t h α_i α_j) :=
  praxeological_interaction_classes_pairwise_mutual_exclusivity title_i α_i α_j

/-- Ground instantiation of spatial Cantillon malinvestment squeeze:
Under network monetary diffusion, a downstream entrepreneur situated at distance
`hop_stage < diff.hop_dist S.investment.i` holds unaugmented cash, which becomes insufficient
under upstream factor price wave `P_wave`, blocking project completion and inducing cycle regret. -/
theorem ground_spatial_cantillon_malinvestment_squeeze
    [W : ActionFrame] [BilateralExchangeFrame W] [DecidableEq W.Agent]
    {Context : Type}
    (S : EntrepreneurialCycleScenario W Context)
    (diff : CantillonNetworkDiffusion W.Agent)
    (v_b : W.Agent → ℕ)
    (hop_stage : ℕ) (P_pre P_wave : ℕ) (m_money : W.Means)
    (h_downstream : hop_stage < diff.hop_dist S.investment.i)
    (h_intra_pre : P_pre ≤ v_b S.investment.i)
    (h_below_wave : v_b S.investment.i < P_wave)
    (h_cash_below_wave :
      W.omega S.investment.i S.investment.next S.investment.x.history m_money < P_wave)
    (h_wave_cost : P_wave ≤ W.use_means S.investment.completion m_money)
    (h_purposeful : PurposefulAct S.investment.i S.investment.x.moment
      S.investment.x.history S.investment.investment) :
    P_pre ≤ diff.effective_bid v_b 0 S.investment.i ∧
    diff.effective_bid v_b hop_stage S.investment.i < P_wave ∧
    diff.effective_cash
      (fun a => W.omega a S.investment.next S.investment.x.history m_money)
      hop_stage S.investment.i =
      W.omega S.investment.i S.investment.next S.investment.x.history m_money ∧
    BlockedCompletion S.investment.i S.investment.next S.investment.x.history
      S.investment.completion ∧
    EntrepreneurialCycleConclusion S :=
  spatial_cantillon_malinvestment_squeeze
    S diff v_b hop_stage P_pre P_wave m_money h_downstream h_intra_pre h_below_wave
    h_cash_below_wave h_wave_cost h_purposeful

/-- Ground instantiation of inflationary delegation contract hollow-out:
When upstream monetary expansion eliminates real wage purchasing power while the task depletes
effort means below the requirement for a valued rest end, remaining idle teleologically dominates
task execution, precluding purposeful execution. -/
theorem ground_affordability_and_task_rejection_under_rest_appraisal
    {W : ActionFrame} {V : DelegationVocabulary W}
    (P : DelegationProposal V) (X : DelegationExecution P)
    (net : CantillonNetwork (W := W))
    (h_op_downstream : P.operator = net.downstream)
    (h_wage_matches : net.M_downstream = P.compensationQuantity)
    (m_effort : W.Means) (e_rest : W.Ends)
    (b_work b_idle : W.Means → ℕ)
    (h_end_task : W.End_of P.operator X.task X.workMoment P.history = W.BundleEnd b_work)
    (h_end_idle : W.End_of P.operator W.alpha_zero X.workMoment P.history = W.BundleEnd b_idle)
    (h_valued : W.ValuedEnd P.operator X.workMoment P.history e_rest)
    (h_unique : ∀ e', W.ValuedEnd P.operator X.workMoment P.history e' → e' = e_rest)
    (h_idle_attains : ∀ m, W.requirement e_rest m ≤ b_idle m)
    (h_work_short : b_work m_effort < W.requirement e_rest m_effort) :
    P.operator = net.downstream ∧
    CanAffordQuantity 1 net.P_pre P.compensationQuantity ∧
    (∀ q, 0 < q → ¬ CanAffordQuantity q net.P_post P.compensationQuantity) ∧
    W.SubjectiveTeleologicalDominates P.operator X.workMoment P.history b_idle b_work ∧
    ¬ @PurposefulAct W P.operator X.workMoment P.history X.task :=
  affordability_and_task_rejection_under_rest_appraisal
    P X net h_op_downstream h_wage_matches m_effort e_rest b_work b_idle
    h_end_task h_end_idle h_valued h_unique h_idle_attains h_work_short

/-- Ground instantiation of Gresham debt withholding:
When legal tender distortion makes an alternative bad-money tender feasible and strictly preferred
to contract media, offering contract repayment is strictly non-purposeful, even under solvency. -/
theorem ground_gresham_solvent_repayment_withholding_non_purposeful
    {W : ActionFrame} [BilateralExchangeFrame W]
    {T : PawnLoanTerms W} (h : W.History)
    (m_bad : W.Means)
    (e_tender_good e_tender_bad : W.Ends)
    (α_tender : W.Agent → W.Means → W.Action)
    (h_offer_is_good_tender :
      α_tender T.borrower T.money =
        W.Offer T.borrower T.lender T.repayment T.money T.collateralQuantity T.collateral)
    (h_tender_pref : W.Preference T.borrower T.maturity h e_tender_bad e_tender_good)
    (h_bad_feas : α_tender T.borrower m_bad ∈ W.A_feas T.borrower T.maturity h)
    (h_end_bad : W.End_of T.borrower (α_tender T.borrower m_bad) T.maturity h =
      e_tender_bad)
    (h_end_good : W.End_of T.borrower (α_tender T.borrower T.money) T.maturity h =
      e_tender_good) :
    ¬ @PurposefulAct W T.borrower T.maturity h
      (W.Offer T.borrower T.lender T.repayment T.money T.collateralQuantity T.collateral) :=
  gresham_solvent_repayment_withholding_non_purposeful
    h m_bad e_tender_good e_tender_bad α_tender h_offer_is_good_tender
    h_tender_pref h_bad_feas h_end_bad h_end_good

end Praxeology

end


