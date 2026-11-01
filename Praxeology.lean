/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.FiniteSupport
public import Praxeology.FiniteEconomy
public import Praxeology.FiniteEconomy.ActiveParticipation
public import Praxeology.FiniteEconomy.BilateralPilot
public import Praxeology.Action
public import Praxeology.EpistemicAbility
public import Praxeology.Marginal
public import Praxeology.Catallactics
public import Praxeology.Catallactics.Credit
public import Praxeology.Production
public import Praxeology.Organization
public import Praxeology.FirmBoundary
public import Praxeology.FirmWitness
public import Praxeology.BusinessCycle
public import Praxeology.EconometricLimits
public import Praxeology.BehavioralPoset
public import Praxeology.StateMonopoly


/-!
# Praxeology — Formalized Austrian Praxeology

A fully verified Lean 4 formalization of human action, subjective value,
market exchange, socialist calculation, firm boundaries, and business-cycle
dynamics. The project introduces no custom axioms; its audited declarations
depend on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`:

- **Theorems 0.1 & 0.2: Model-Theoretic Consistency & Non-Vacuity** (`Praxeology.Frame`)
  Zero-axiom `ActionFrame` typeclass (`FiniteBranchingModel`, `action_frame_consistent`)
  and spatiotemporal branching-tree & Bourbaki-Witt marketability witness
  (`BranchingMarketabilityModel`, `branching_marketability_model_consistent`).

- **Theorem 1: The Praxeological Action Axiom & Revealed Teleology** (`Praxeology.Action`)
  Purposeful action (`PurposefulAct`, `DoxasticPurposefulAct`), pragmatic self-falsification
  (`pragmatic_self_falsification_of_action_denial`), set-valued opportunity cost
  (`ActionOCSet`, `StrictOCSet`), and performative self-consistency without neoclassical patches.
  *Theorems 1.1–1.7*.

- **Theorem 2: Diminishing Marginal Utility & Value Imputation** (`Praxeology.Marginal`)
  Choice-free ordinal diminishing marginal utility, least-urgent end economizing,
  teleological quanta subsumption of complementarity, odd-shoe sub-quantum remainder sterility,
  praxeological refutation of sunk costs & labor theory of value,
  Menger's law of backward value imputation, intertemporal capital imputation via causal frames,
  and factor specificity value collapse vs. versatility cushioning.
  *Theorems 2.1–2.3 (Theorems 2.1a–2.1f, 2.3a–2.3d)*.

- **Theorem 3: Universal Positive Time Preference & Originary Interest** (`Praxeology.Marginal`)
  Action horizon impossibility under negative time preference
  (`causal_not_purposeful_immediate_consumption_of_negative_time_pref`), action-derived
  positive time preference, strictly positive originary interest ι > 0, Böhm-Bawerk's law of
  roundabout production productivity necessity, capital accumulation as action-menu unlocking
  epochs, and the Autumn-Winter Food Security & DMU End-Individuation theorem.
  *Theorems 3.1–3.6 (Theorems 3.5a–3.5d)*.

- **Theorem 4: Catallactic Bilateral Exchange & Money Emergence** (`Praxeology.Catallactics`)
  Double inequality of exchange, Mises's Law of Association under universal absolute advantage,
  Rothbard-Megger welfare trichotomy pairwise mutual exclusivity
  (`rothbard_megger_trichotomy_mutual_exclusivity`),
  refutation of Knaster-Tarski monotonicity (`concrete_phi_non_monotone_witness`),
  Bourbaki-Witt inflationary fixed-point money emergence,
  price-box precautionary cash demand narrowing and solvency expansion loop,
  discrete marginal pairs pricing bounds, and constructive cardinal-free Gresham's law collapse.
  *Theorems 4.1–4.5 (Theorems 4.1a–4.1c, 4.3a–4.3j)*.

- **Theorem 5: The Mises-Hayek Economic Calculation Problem (ECP)** (`Praxeology.Catallactics`)
  Automorphism non-invariance over physical antichains, semantic incommensurability barrier
  vs. algorithmic complexity, and universal epistemic measurability impossibility across planners.
  *Theorems 5.1–5.3*.

- **Theorem 6: Counterfactual Action & Epistemic Second-Best** (`Praxeology.Counterfactuals`)
  Ex-ante/ex-post divergence, cross-branch regret, mandatory regret in heterodoxastic speculation,
  Misesian entrepreneurial profit and loss dichotomy, purposeful speculation with ex-ante gain
  and ex-post selection, impossibility of speculative trade under shared plausibility,
  Lawson's epistemic second-best non-monotonicity, and regulatory cascades.
  *Theorems 6.1–6.6 (Theorems 6.4b–6.4c, 6.6a)*.

- **Context-Matched Counterfactuals** (`Praxeology.CausalCounterfactuals`)
  Explicit causal contexts and admissible outcome correspondences, robust appraisal,
  possible and guaranteed matched regret, and conditional bridges to selected-branch results.

- **Theorem 7: The Boundary of the Firm & Signal Quantization** (`Praxeology.FirmBoundary`)
  Catallactic price-box indeterminacy cones, Hayekian epistemic compression,
  Kirznerian arbitrage cone contraction, multi-stage signal attenuation, master coalescence
  inequality, purposeful firm coalescence with load-bearing calculational rationality,
  refutation of the arithmetic stage-count integration fallacy
  (`vertical_integration_stage_count_fallacy_refuted`),
  operationally interpreted delegation and market interfaces (`Praxeology.Organization`),
  kernel-checked finite policy and trade witnesses, conditional firm-boundary choice,
  and credit-induced artificial conglomeration with bust regret.
  *Theorems 7.1–7.9 (Theorems 7.6a–7.6d, 7.8b–7.8c)*.

- **Theorem 8: Austrian Business Cycle Theory (ABCT)** (`Praxeology.BusinessCycle`)
  Credit-rate appraisal and purposeful investment, complementary-factor starvation, price-box
  completion squeeze, and contextual regret for a single entrepreneurial scenario. The
  information and cohort extensions model saving/credit signal ambiguity, shared response
  policies, aggregate unit-input shortages, price-buffer crossings, and conditional regret for
  each affected project. A finite two-agent witness grounds one entrepreneur's cycle; a fully
  instantiated multi-entrepreneur credit-and-regret witness remains future work.

- **Theorem 9: Causal Econometric Non-Identifiability** (`Praxeology.EconometricLimits`)
  Master non-identifiability principle (`non_identifiability_of_divergent_models`),
  causal econometric non-identifiability under branching time
  (`causal_econometric_non_identifiability`), generalized Lucas critique policy invariance failure
  (`lucas_critique_policy_invariance_failure`), instrumental variable exclusion restriction
  unverifiability (`iv_exclusion_restriction_unverifiable`), and Duhem-Quine econometric
  underdetermination (`duhem_quine_underdetermination`).
  *Theorems 9.1–9.5*.

- **Theorem 10: Poset-Theoretic Behavioral Equivalence** (`Praxeology.BehavioralPoset`)
  Poset-theoretic behavioral embedding (`contextual_to_poset`),
  cross-frame preference reversals consistent with asymmetry
  (`framing_reversal_consistent_with_asymmetry`), purposeful action invariant under framing shifts
  (`purposeful_act_invariant_under_framing`), hyperbolic discounting and intertemporal preference
  reversals (`hyperbolic_reversal_consistent_with_action_axiom`),
  loss aversion / reference-dependent choice invariance
  (`loss_aversion_instantiates_purposeful_act`), and refutation of the behavioral anomaly dilemma
  (`contextual_frame_induces_strict_poset`).
  *Theorems 10.1–10.6*.

- **Theorem 11: State Monopoly & Fiscal Extraction** (`Praxeology.StateMonopoly`)
  Territorial licensing and judicial authority, coercive taxation as extortion, fiscal conservation,
  Calhoun multi-moment inventory run fiscal partition (`calhoun_action_frame_run_class_partition`),
  Hoppean endogenous ruler time-preference extraction, judicial monopoly self-exoneration,
  statutory immunity protecting calculation blindness, and political economy master synthesis
  (`state_monopoly_political_economy_master_synthesis`).
  Behavioral conclusions are conditional on explicit preferences, menus, and execution.
  *Theorems 11.1–11.6*.
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
      (@timedQuantityEnd FiniteBranchingModel m q τ)
      (@timedQuantityEnd FiniteBranchingModel m q' τ) :=
  finite_model_quantity_monotonicity i t h m q q' τ hq

/-- Ground instantiation of Theorem 3.5b: non-vacuous positive originary interest. -/
theorem ground_intertemporal_chain_non_vacuous :
    ∃ (i : FiniteBranchingModel.Agent) (t : FiniteBranchingModel.Moment)
      (h : FiniteBranchingModel.History) (m : FiniteBranchingModel.Means)
      (q q' : ℕ) (α_cons : FiniteBranchingModel.Action) (τ1 : FiniteBranchingModel.Moment),
      @PurposefulAct FiniteBranchingModel i t h α_cons ∧
      @DistinctEndDominantAct FiniteBranchingModel i t h α_cons ∧
      @CausalDoxasticOpenHorizon FiniteBranchingModel i t h
        (@QuantityEnd FiniteBranchingModel m q) α_cons τ1 ∧
      ¬ @IsPostHorizon FiniteBranchingModel i t h ∧
      (∃ (τ2 : FiniteBranchingModel.Moment) (δ : ℕ),
        0 < q ∧ @LT.lt FiniteBranchingModel.Moment _ τ1 τ2 ∧ q < q' ∧ δ ≥ 1 ∧ q' = q + δ ∧
        @Preference FiniteBranchingModel i t h
          (@TimedEnd FiniteBranchingModel (@QuantityEnd FiniteBranchingModel m q) τ1)
          (@TimedEnd FiniteBranchingModel (@QuantityEnd FiniteBranchingModel m q) τ2) ∧
        @Preference FiniteBranchingModel i t h
          (@timedQuantityEnd FiniteBranchingModel m q τ1)
          (@timedQuantityEnd FiniteBranchingModel m q τ2)) :=
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
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) geometry

/-- Ground instantiation of Theorem 5.3: Purely ordinal ECP measurability impossibility. -/
theorem ground_ecp_ordinal_impossibility [W : ActionFrame]
    (i1 i2 : W.Agent) (t1 t2 : W.Moment) (h1 h2 : W.History)
    (E1 : ActionFrameSocialistEconomy i1 t1 h1)
    (E2 : ActionFrameSocialistEconomy i2 t2 h2)
    (h_same_methods : E1.x_A = E2.x_A ∧ E1.x_B = E2.x_B)
    (h_anti : PhysicalAntichain E1.x_A E1.x_B)
    (h_same_report : E1.non_market_report = E2.non_market_report)
    (h_same_ends : E1.eA = E2.eA ∧ E1.eB = E2.eB)
    (h_opposite_preferences : E1.prefers_A = true ∧ E2.prefers_A = false)
    (h_presA : ActionFramePreservedEnd E1 E1.x_A = E1.eB)
    (h_presB : ActionFramePreservedEnd E1 E1.x_B = E1.eA) :
    PhysicalAntichain E1.x_A E1.x_B ∧
    action_frame_non_market_observable E1 = action_frame_non_market_observable E2 ∧
    ViolatesActionFrameMengerianEconomizing E1 E1.x_A ∧
    ¬ ViolatesActionFrameMengerianEconomizing E1 E1.x_B ∧
    ViolatesActionFrameMengerianEconomizing E2 E2.x_B ∧
    ¬ ViolatesActionFrameMengerianEconomizing E2 E2.x_A ∧
    ∀ (planner_rule : (InputVec 2 × InputVec 2 × (Fin 2 → ℕ)) → Bool),
      (let chosen1 := if planner_rule (action_frame_non_market_observable E1)
        then E1.x_A else E1.x_B
       ViolatesActionFrameMengerianEconomizing E1 chosen1) ∨
      (let chosen2 := if planner_rule (action_frame_non_market_observable E2)
        then E2.x_A else E2.x_B
       ViolatesActionFrameMengerianEconomizing E2 chosen2) :=
  action_frame_socialist_calculation_impossibility i1 i2 t1 t2 h1 h2 E1 E2
    h_same_methods h_anti h_same_report h_same_ends h_opposite_preferences h_presA h_presB

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
theorem ground_purposeful_firm_coalescence :
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
  purposeful_firm_coalescence_non_vacuous

/-- Ground instantiation of Theorem 3.5c: Böhm-Bawerk's roundabout productivity necessity. -/
theorem ground_bohm_bawerk_roundabout_necessity
    (i : FiniteBranchingModel.Agent) (t : FiniteBranchingModel.Moment)
    (h : FiniteBranchingModel.History) (m : FiniteBranchingModel.Means)
    (q_direct q_roundabout : ℕ) (hq : 0 < q_direct) (τ_direct τ_later : FiniteBranchingModel.Moment)
    (h_pos_tp : @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel m q_direct τ_direct)
      (@timedQuantityEnd FiniteBranchingModel m q_direct τ_later))
    (α_direct α_roundabout : FiniteBranchingModel.Action)
    (h_direct_feas : α_direct ∈ @ActionFrame.A_feas FiniteBranchingModel i t h)
    (h_direct_end : @ActionFrame.End_of FiniteBranchingModel i α_direct t h =
      @timedQuantityEnd FiniteBranchingModel m q_direct τ_direct)
    (h_round_end : @ActionFrame.End_of FiniteBranchingModel i α_roundabout t h =
      @timedQuantityEnd FiniteBranchingModel m q_roundabout τ_later)
    (h_round_purp : @PurposefulAct FiniteBranchingModel i t h α_roundabout)
    (h_sync_mono : q_roundabout ≤ q_direct →
      @Preference FiniteBranchingModel i t h
        (@timedQuantityEnd FiniteBranchingModel m q_direct τ_later)
        (@timedQuantityEnd FiniteBranchingModel m q_roundabout τ_later) ∨
      @timedQuantityEnd FiniteBranchingModel m q_direct τ_later =
        @timedQuantityEnd FiniteBranchingModel m q_roundabout τ_later)
    (h_trans : ∀ e1 e2 e3,
      @Preference FiniteBranchingModel i t h e1 e2 →
      @Preference FiniteBranchingModel i t h e2 e3 →
      @Preference FiniteBranchingModel i t h e1 e3) :
    q_direct < q_roundabout ∧
    (∃ δ_cap : ℕ, δ_cap ≥ 1 ∧ q_roundabout = q_direct + δ_cap) :=
  bohm_bawerk_roundabout_productivity_necessity (W := FiniteBranchingModel)
    i t h m q_direct q_roundabout hq τ_direct τ_later h_pos_tp
    α_direct α_roundabout h_direct_feas h_direct_end h_round_end
    h_round_purp h_sync_mono h_trans

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

/-- Ground instantiation of Theorem 10.6: Poset-theoretic behavioral anomaly embedding. -/
theorem ground_contextual_frame_induces_strict_poset
    (W : ActionFrame) (i : W.Agent) (t : W.Moment) (h : W.History)
    (h_trans : ∀ e₁ e₂ e₃, W.Preference i t h e₁ e₂ → W.Preference i t h e₂ e₃ →
      W.Preference i t h e₁ e₃) :
    ∃ P : StrictPoset W.Ends, P.lt = W.Preference i t h :=
  ⟨action_frame_strict_poset W i t h h_trans, rfl⟩

/-- Ground instantiation of Theorem 4.4c: Market clearing with pairwise conservation. -/
theorem ground_multilateral_cohort_market_clearing
    [ActionFrame] (M : MultilateralCohortMarket Agent Means)
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
      (fun h' => ¬ DoxasticPurposefulAct (F := W) i (W.tau i t h') H_t h') α_assert) :
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

/-- Ground instantiation of Theorem 1.8: Doxastic dominance implies PurposefulAct. -/
theorem ground_purposeful_act_of_doxastic_dominance
    (W : ActionFrame) (i : W.Agent) (t : W.Moment) (H_t : Set W.History) (h : W.History)
    (h_mem : W.mem_hist t h)
    (h_projected : W.ProjectedFeasibility)
    (h_app : W.IsUnanimousAppraisal i t h)
    (h_dox : DoxasticPurposefulAct (F := W) i t H_t h) :
    PurposefulAct (F := W) i t h (W.enacted i t h) :=
  purposeful_act_of_doxastic_dominance (F := W) i t H_t h h_mem h_projected h_app h_dox

/-- Ground instantiation of Theorem 1.10: Equivalence on singleton plausibility strata. -/
theorem ground_purposeful_act_iff_doxastic_purposeful_act
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
      DoxasticPurposefulAct (F := W) i t H_t h :=
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
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_nontrade : ∀ a ∈ Cohort, ¬ W.IsTradeAction (W.enacted a t h))
    (h_noyield : ∀ a ∈ Cohort, W.yield_means (W.enacted a t h) m = 0)
    (s : W.Agent) (hs_mem : s ∈ Cohort)
    (hs_gain : W.omega s t h m < W.omega s t' h m) :
    ∃ b : W.Agent, b ∈ Cohort ∧ W.omega b t' h m < W.omega b t h m :=
  calhoun_action_frame_class_partition Cohort t t' h m h_next h_nontrade h_noyield s hs_mem hs_gain

/-- Ground instantiation of Theorem 11.2'': Calhoun partition in multi-moment inventory runs. -/
theorem ground_calhoun_action_frame_run_class_partition
    [W : ActionFrame]
    (Cohort : Finset W.Agent) {t u : W.Moment} {h : W.History}
    (runs : (a : W.Agent) → InventoryRun W a h t u) (m : W.Means)
    (h_noyield : ∀ a ∈ Cohort, (runs a).totalYield m = 0)
    (s : W.Agent) (hs_mem : s ∈ Cohort)
    (hs_gain : W.omega s t h m < W.omega s u h m) :
    ∃ b : W.Agent, b ∈ Cohort ∧ W.omega b u h m < W.omega b t h m :=
  calhoun_action_frame_run_class_partition Cohort runs m h_noyield s hs_mem hs_gain

/-- Ground instantiation of Theorem 4.1c: Exclusivity of Rothbard-Megger welfare trichotomy. -/
theorem ground_rothbard_megger_trichotomy
    [W : ActionFrame] {i j : W.Agent} {t t' : W.Moment} {h : W.History}
    (α_i α_j : W.Action) :
    ¬ (IsVoluntaryExchange i j t t' h α_i α_j ∧ IsCoerciveExtortion i j t t' h α_i α_j) ∧
    ¬ (IsVoluntaryExchange i j t t' h α_i α_j ∧ IsMarketCompetition i j t t' h α_i α_j) ∧
    ¬ (IsCoerciveExtortion i j t t' h α_i α_j ∧ IsMarketCompetition i j t t' h α_i α_j) :=
  rothbard_megger_trichotomy_mutual_exclusivity α_i α_j

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
theorem ground_vertical_integration_stage_count_fallacy_refuted
    (L K : ℕ) (h_complete_integration : K = L) :
    (∀ s, PolicyCorrect .bothSignals s) ∧
    (∀ s, PolicyCorrect .factorRestored s) ∧
    (¬ ∃ π : Bool × Bool → FirmProductionDecision,
      ∀ s, π (informationObservation .factorHidden s) = firmRequiredDecision s) ∧
    (¬ ∃ π : Bool × Bool → FirmProductionDecision,
      ∀ s, π (informationObservation .demandHidden s) = firmRequiredDecision s) :=
  vertical_integration_stage_count_fallacy_refuted L K h_complete_integration

/-- Ground instantiation of Theorem 11.6: State Monopoly Political Economy Master Synthesis. -/
theorem ground_state_monopoly_master_synthesis [W : ActionFrame] {i j : W.Agent}
    {t t' : W.Moment} {h : W.History}
    (S : StateMonopolyMasterEvidence (W := W) (i := i) (j := j) (t := t) (t' := t') (h := h)) :
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
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    W.omega i t h m < W.omega i t' h m ∧
    (∀ m', W.omega j t' h m' = W.omega j t h m') ∧
    ResourceMenuPreserved j t t' h :=
  lockean_homesteading_non_invasive h_home h_exec_i h_passive_j h_next

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
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    β ∉ W.A_feas j t h ∧
    W.omega i t h m < W.omega i t' h m ∧
    StockPreserved j t t' h ∧
    ResourceMenuPreserved j t t' h ∧
    ∀ γ, ¬ FeasibleMenuStripped j t t' h γ :=
  unowned_resource_contemplation_not_feasible_and_first_appropriation_non_invasive
    h_unowned_j h_req_β h_home h_exec_i h_passive_j h_next

/-- Ground instantiation of the Thief-and-Baker path-dependent title trace:
Baker recovering stolen flour from thief is restitution, preserving clean title,
hence is NOT a path-dependent invasion despite contracting thief's physical stock. -/
theorem ground_baker_recovery_not_path_dependent_invasion
    [W : ActionFrame]
    (baker thief : W.Agent) (flour : W.Means) (q : ℕ)
    (h_ne : thief ≠ baker)
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
    W.omega baker t2 h flour = title baker flour :=
  baker_recovery_restitution_not_path_dependent_invasion
    baker thief flour q h_ne t0 t1 t2 h title h_clean0 h_avail0
    h_s1_baker h_s1_thief h_s2_thief h_s2_baker

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
    [W : ActionFrame] {T : PawnLoanTerms W} {A : CreditAdvance T}
    (D : UnpaidMaturity A)
    (t_post : W.Moment)
    (h_succ : IsNextMoment W.Precedence W.mem_hist T.maturity t_post A.history)
    (h_borrower_idle : W.enacted T.borrower T.maturity A.history = W.alpha_zero) :
    ResourceMenuPreserved T.borrower T.maturity t_post A.history :=
  D.borrower_resource_menu_preserved t_post h_succ h_borrower_idle

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
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    W.Preference i t h (W.End_of i α t h) (W.End_of i W.alpha_zero t h) ∧
    W.omega i t h m < W.omega i t' h m ∧
    (∀ m', W.omega j t' h m' = W.omega j t h m') ∧
    ResourceMenuPreserved j t t' h ∧
    ∀ γ, ¬ FeasibleMenuStripped j t t' h γ :=
  purposeful_lockean_homesteading_non_invasive h_home h_passive_j h_next

/-- Ground instantiation of the Action-Axiom equivalence between endogenous invasion
and feasible-menu stripping under tight-action richness. -/
theorem ground_endogenous_invasion_iff_menu_stripping
    [W : ActionFrame] {i j : W.Agent} {t t' : W.Moment} {h : W.History}
    (h_rich : ∀ m : W.Means, ∃ β, (∀ m', W.use_means β m' ≤ W.omega i t h m') ∧
      W.use_means β m = W.omega i t h m)
    (α_j : W.Action) :
    EndogenouslyInvasiveJ i j t t' h α_j ↔ MenuStrippingInvasiveJ i j t t' h α_j :=
  endogenous_invasion_iff_menu_stripping h_rich α_j

/-- Ground instantiation of ActionFrame physical invasion menu stripping:
Invading j against i contracts clean-title stock and strips tight actions from i's menu. -/
theorem ground_actionFrame_invasion_strips_feasible_menu
    [W : ActionFrame]
    (i j : W.Agent) (t t' : W.Moment) (h : W.History)
    (title_i : W.Means → ℕ) (α_j : W.Action) (m_inv : W.Means) (β : W.Action)
    (ht : W.mem_hist t h)
    (ht_branch : W.mem_hist t (jointBranch i j t h W.alpha_zero α_j))
    (h_clean : title_i m_inv ≤ W.omega i t h m_inv)
    (h_contract : W.omega i t' (jointBranch i j t h W.alpha_zero α_j) m_inv < title_i m_inv)
    (h_feas : β ∈ W.A_feas i t h)
    (h_cont : β ∈ W.A_cont i t' (jointBranch i j t h W.alpha_zero α_j))
    (h_tight : W.use_means β m_inv = title_i m_inv) :
    FeasibleMenuStripped i t t' (jointBranch i j t h W.alpha_zero α_j) β :=
  actionFrame_invasion_strips_menu_of_history i j t t' h title_i α_j m_inv β
    ht ht_branch h_clean h_contract h_feas h_cont h_tight

end Praxeology

end


