# Specification 04: Bilateral Exchange, Bourbaki-Witt Money Emergence, Discrete Pricing, and the Economic Calculation Problem (ECP)

Formal mathematical specification for [`Praxeology/Catallactics.lean`](../Praxeology/Catallactics.lean).

---

## 1. Bilateral Exchange and Voluntary Cooperation

Catallactic exchange requires bilateral mutual consent between acting agents:

* **Offer and Accept Primitives:** Agent $`i`$ offers $`q_A`$ units of $`m_A`$ to agent $`j`$ in exchange for $`q_B`$ units of $`m_B`$ ([`Offer`](../Praxeology/Catallactics.lean#L828), [`Accept`](../Praxeology/Catallactics.lean#L833)).
* **Double Inequality of Subjective Value:** Exchange executes if and only if both parties subjectively rank what they receive higher than what they surrender ([`double_inequality_of_exchange`](../Praxeology/Catallactics.lean#L917)):

```math
\langle q_B, m_B \rangle \succ_{i,t,h} \langle q_A, m_A \rangle \quad \wedge \quad \langle q_A, m_A \rangle \succ_{j,t,h} \langle q_B, m_B \rangle
```

### Megger's Separation: Coercion vs. Demonstrated Preference

Following Dawid Megger (2024), our codebase explicitly differentiates voluntary exchange from coercive extraction (the "highwayman dilemma"):
* Under coercive extortion (e.g., "your money or your life"), the victim surrenders money not because they prefer the thief's end, but to avoid the immediate destruction of their bodily baseline ($`\alpha_0`$).
* Praxeological demonstrated preference applies to the *constrained choice of lesser physical evil*, but cannot be aggregated as a mutually beneficial catallactic exchange ([`highwayman_is_purposeful_but_not_catallactic`](../Praxeology/Catallactics.lean#L138)).

---

## 2. Bourbaki-Witt Fixed-Point Money Emergence

Menger's organic emergence of money traces how the most marketable commodity ($`m^{\ast}`$) evolves through indirect exchange into a universally accepted medium of exchange.

### The Breakdown of Knaster-Tarski Monotonicity

Let $`L = \langle \mathcal{P}(I)^M, \sqsubseteq \rangle`$ be the finite poset of acceptance profiles, ordered by profile inclusion:
```math
\Phi(\boldsymbol{\Gamma})_m = \boldsymbol{\Gamma}(m) \cup \left\lbrace i \in I \mid m \in \arg\max_{m'} |\boldsymbol{\Gamma}(m')| \wedge \text{FeasibleIndirect}(i, m) \right\rbrace
```
Because off-diagonal shifts in individual liquidity and argmax substitutions induce localized non-monotonicities, $`\Phi`$ is **not globally monotone** on $`(\mathcal{P}(I)^M, \subseteq)`$, rendering Knaster-Tarski inapplicable. This breakdown is certified by a concrete countermodel in [`concrete_phi_non_monotone_witness`](../Praxeology/Catallactics.lean) and [`concrete_phi_list_non_monotone_witness`](../Praxeology/Catallactics.lean) with zero transitive axioms (`[] (0 axioms)`).

### The Inflationary Orbit Theorem

Our codebase resolves this foundational barrier constructively:
1. **Inflationary Property:** For all profiles $`\boldsymbol{\Gamma}`$, $`\boldsymbol{\Gamma} \sqsubseteq \Phi(\boldsymbol{\Gamma})`$ by set-extension construction ([`phi_max_list_inflationary`](../Praxeology/Catallactics.lean)).
2. **Bourbaki-Witt Stabilization on Finite Posets:** Iterating any inflationary operator on a finite poset $`[L, \le]`$ stabilizes at a fixed point in $`n \le |L|`$ steps by the pigeonhole principle on strictly ascending chains ([`universal_money_emergence`](../Praxeology/Catallactics.lean#L1504)):

```math
\exists n \le |L|, \quad \Phi^n(\boldsymbol{\Gamma}_0) = \Phi^{n+1}(\boldsymbol{\Gamma}_0)
```

3. **Universal Medium Convergence:** Starting from non-monetary barter, the iterative orbit terminates at a unique universal medium of exchange $`m^{\ast}`$ where $`\boldsymbol{\Gamma}^{\ast}(m^{\ast}) = I`$ ([`universal_money_emergence`](../Praxeology/Catallactics.lean#L1504), [`purposeful_mengerian_money_adoption`](../Praxeology/Catallactics.lean#L1542)).
4. **The Money–Price-Box–Solvency Loop:** Transition from barter to universal money contracts factor transaction spreads, narrowing factor price boxes ($`\mathcal{B}_{\text{barter}} \to \mathcal{B}_{\text{money}}`$). By [`constructive_list_money_price_box_solvency_loop`](../Praxeology/Catallactics.lean) and [`network_money_emergence_narrows_price_box_and_expands_solvency`](../Praxeology/Catallactics.lean):
   - Precautionary cash demand weakly falls for all agents: $`C^+_{\text{money}}(x_i) \le C^+_{\text{barter}}(x_i)`$.
   - The solvent cohort of entrepreneurs able to finance factor bundles weakly expands: $`\text{SolventCohort}_{\text{barter}} \subseteq \text{SolventCohort}_{\text{money}}`$.
5. **Gresham Circulation Collapse:** Under coercive par-tender legislation, purposeful buyers hoard good money and tender debased currency, completely extinguishing the circulation of good money ([`greshams_law_circulation_collapse`](../Praxeology/Catallactics.lean) and [`greshams_law_list_circulation_collapse`](../Praxeology/Catallactics.lean)).

---

## 3. Discrete Marginal Pairs and Catallactic Pricing Grid

To avoid off-by-one boundary tie errors on continuous models, currency is parameterized on a discrete grid $`\mathbb{M}_D = \{ k / D \mid k \in \mathbb{N} \}`$ with step size $`1/D`$:

* Buyers are sorted in descending order of subjective reservation values: $`v_1^b \ge v_2^b \ge \dots \ge v_r^b`$.
* Sellers are sorted in ascending order of subjective reservation costs: $`v_1^s \le v_2^s \le \dots \le v_r^s`$.
* Let $`r^{\ast}                                              v_{r^{\ast}}^b \ge v_{r^{\ast}}^s         v_{r^{\ast}+1}^b < v_{r^{\ast}+1}^s`$.

### Marginal Pair Deterrence Price Bounds

```math
\max\left( v_{r^{\ast}}^s, v_{r^{\ast}+1}^b + \frac{1}{D} \right) \le P_t(m) \le \min\left( v_{r^{\ast}}^b, v_{r^{\ast}+1}^s - \frac{1}{D} \right)
```
([`price_bracket_width_nonneg`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L2265)). This interval ensures that extra-marginal buyers and sellers are deterred from entering the market, preventing indeterminacy and guaranteeing market clearance.

---

## 3b. Multilateral Cohort Markets and Cantillon Network Dilution

### Multilateral Cohort Marginal-Pairs Clearing

Extending bilateral marginal pairs to an arbitrary multilateral cohort of $`N`$ buyers and sellers ([`MultilateralCohortMarket`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L2346)):
1. **Intra-Marginal Trade Clearance:** All active intra-marginal buyers satisfy $`P \le v_b(b)`$ and sellers satisfy $`v_s(s) \le P`$.
2. **Extra-Marginal Purposeful Deterrence:** Bids and offers from extra-marginal agents fail to relieve felt unease relative to autarky, actively deterring extra-marginal entry ([`multilateral_extra_marginal_deterrence`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L2430)).
3. **Pairwise Sum Conservation:** Executing bilateral transactions between matched pairs strictly conserves aggregate endowments of both commodities and money across the entire market cohort without requiring global matrix algebra ([`cohort_sum_two_swap_invariant`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L1926), [`multilateral_cohort_pairwise_trade_conservation`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L2407), [`multilateral_cohort_market_clearing`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L2492)).

### Cash-Balance Reservation Demand and Cantillon Networks

1. **Cash-Balance Solvency Guarantee:** An agent holding nominal money balance $`M_{\text{cash}} \ge P`$ possesses the physical capacity to clear market transactions, guaranteeing positive purchasing power ([`cash_balance_solvency_guarantee`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L3118)).
2. **Cantillon Network Purchasing Power Dilution:** In a network of trading agents ([`CantillonNetwork`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L3130)), new money injected at specific nodes bids up prices along the topological distance path ($`P_{\text{pre}} \to P_{\text{post}}`$). Downstream agents holding cash balance $`M_{\text{downstream}}`$ face diluted purchasing power, demonstrating that non-neutral credit expansion redistributes real wealth from late recipients to early recipients ([`cantillon_network_purchasing_power_dilution`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics.lean#L3173)).

---

## 3c. Credit Contracts, Media Conservation, and Monetary Aggregation Limits

Formalized in [`Praxeology/Catallactics/Credit.lean`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean):

1. **Spot-Trade Feasibility Characterization:** In any `ActionFrame`, accepting a spot purchase of $q_A$ units of commodity $m_A$ at price $P$ in medium $m$ is feasible at $(t, h)$ if and only if the acceptance is contemplated and $P \le \omega_{\text{buyer}}(t, h, m)$ ([`accept_spot_trade_feasible_iff`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L810)).
2. **Cross-Medium Aggregation Impossibility:** Even if a buyer's combined endowment across distinct media $m_1 \neq m_2$ covers price $P$, if neither balance individually satisfies $\omega \ge P$, spot acceptance is infeasible in both media and cannot be enacted as a purposeful act ([`infeasible_accept_of_split_media_endowment`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L834)).
3. **Cross-Agent Aggregation Impossibility:** If two buyers each hold less than $P$ of medium $m$, spot acceptance is infeasible for each buyer individually, regardless of whether their sum covers $P$ ([`infeasible_accept_of_split_agent_endowment`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L860)).
4. **Conservation of Total Media in Commodity Credit:** In a matched credit advance where loan principal is transferred and bystanders remain passive, universal total media (`totalMedia`) is strictly conserved ([`CreditAdvance.totalMedia_conserved`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L884)).
5. **Lender Menu-Stripping:** Advancing principal contracts the lender's money balance and strictly strips any tight money-using action from the lender's feasible menu (`FeasibleMenuStripped`) ([`CreditAdvance.lender_tight_action_stripped`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L918)).
6. **Reserve Invariance in Fiduciary Origination:** Note printing followed by loan advance transfers zero units of the reserve commodity, leaving the issuer's physical reserve endowment strictly invariant ([`FiduciaryOrigination.issuer_reserve_unchanged`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L935)).
7. **Redemption Infeasibility and Shortfall:** Any redemption claim exceeding the issuer's physical reserve is resource-infeasible and non-purposeful ([`redemption_accept_not_purposeful_of_exceeds_reserve`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L960)). Origination expands circulating media by $+T.\text{principal} > 0$ while leaving reserves unchanged, producing an unbacked redemption shortfall ([`FiduciaryOrigination.unbacked_expansion_creates_redemption_shortfall`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L976)).
8. **Endowment Matrix and Macro-Sum Underdetermination:** Spot feasibility is determined exclusively by the individual agent's row in the endowment matrix $[\omega_a(t, h, m)]$, not by macro scalar sums; a macro sum underdetermines spot feasibility ([`macro_sum_underdetermines_spot_feasibility`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L998)).
9. **Bank-Specific Fiduciary Overhang and Local Infeasibility:** Fiduciary deposits at distinct commercial banks are distinct media; even if aggregate banking reserves are large, a bank-specific shortfall renders par redemption at that bank strictly infeasible ([`bank_specific_redemption_infeasible_of_local_shortfall`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L1030)).
10. **Three-Sector Base Money Partition:** Universal base money partitions exactly into non-bank public currency, commercial bank custodial reserves, and sovereign Treasury cash without double-counting ([`totalBaseMoney_eq_three_sector_partition`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L1061)).
11. **Two-Tier Fiat Lender-of-Last-Resort Dichotomy:** In a two-tier fiat regime, commercial bank redemption demands exceeding reserves are autonomously infeasible; a central bank lender-of-last-resort bailout rescues the bank only by enacting fiduciary issuance that strictly expands total base media ([`two_tier_fiat_lolr_dichotomy`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L1085)).
12. **Bank-Tier Partition of Reserves:** Total commercial bank custodial reserves partition additively across disjoint bank tiers (e.g. money-center vs. regional/community banks) ([`bankReserves_tier_partition`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L1105)).
13. **Asymmetric Tier Coverage Divergence and Localized Run Infeasibility:** When reserve concentration across tiers is asymmetric, the second tier's coverage ratio strictly diverges below the aggregate system ratio ([`asymmetric_tier_coverage_divergence`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L1117)); even when aggregate reserves across all tiers cover a redemption run, a localized reserve shortfall at an individual bank renders spot redemption strictly infeasible and non-purposeful ([`tier_asymmetric_reserve_run_infeasibility`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L1129)).
14. **Automated Sweep Two-Step Execution vs. Liquidity Freeze Breakdown:** An automated sweep mechanism can only enable spot purchases via a two-step sequential bilateral credit advance; if a liquidity freeze occurs and secondary conversion halts, cash endowments are conserved under baseline inaction $\alpha_0$, leaving spot purchase acceptance strictly resource-infeasible and non-purposeful ([`automated_sweep_two_step_vs_freeze_dichotomy`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L1149)).
15. **Standing Central Bank LOLR Facilities and Collateral Encumbrance:** Standing central bank credit facilities restore commercial bank reserve coverage only by executing a collateralized fiduciary origination that strictly encumbers commercial bank collateral assets while expanding total base money in the economy ([`standing_lolr_origination_restores_reserve_and_expands_base`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Catallactics/Credit.lean#L1183)).

---

## 4. The Mises-Hayek Economic Calculation Problem (ECP)

Socialist central planning abolishes private ownership in the means of production, eliminating exchange markets for capital goods:
```math
\forall m \in M_{\text{capital}}, \quad \mathcal{A}_i^{\text{exchange}}(m) = \emptyset
```
Consequently, market prices for higher-order capital goods do not exist.

### Antichain Cost Minimization Undefinedness

Let $`\omega_1, \omega_2 \in \Omega(c)`$ be two rival production techniques for consumer good $`c`$, requiring input vectors $`\mathbf{x}(\omega_1), \mathbf{x}(\omega_2) \in \mathbb{N}^d`$ that form an **antichain** in the physical partial order (e.g., technique 1 uses more hydroelectric power and less coal; technique 2 uses more coal and less hydroelectric power):

1. **Catallactic Resolution:** Under private property, cardinal market prices $`\mathbf{P}_t \in \mathbb{Q}^d`$ define a scalar cost function, inducing a total linear order over production techniques:

```math
C_t(\mathbf{x}) = \sum_{k=1}^d P_t(m_k) x_k
```

2. **Socialist Incommensurability:** In the absence of market prices, summing physically heterogeneous factors ($`\text{coal} + \text{electricity}`$) is mathematically ill-typed.
3. **Automorphism Invariance Barrier:** Any pseudo-cost ranking $`\preceq_{\text{cost}}`$ derived from consumer goods preferences is invariant under order-automorphisms $`\text{Aut}(M_1, \succ)`$. Sums of ordinal rank differences mutate arbitrarily under monotonic transformations, proving that the cost-minimizing technique is mathematically undefined in socialist systems ([`socialist_calculation_incommensurability`](../Praxeology/Catallactics.lean#L3544)):

```math
\arg\min_{\omega \in \Omega(c)} \text{Cost}(\omega)
```

4. **Epistemic Measurability Impossibility:** Central calculation fails not due to computational NP-hardness, but because the objective evaluation function does not exist within the relational model ([`ecp_epistemic_measurability_impossibility`](../Praxeology/Catallactics.lean#L3560)).
