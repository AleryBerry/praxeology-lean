# Specification 05: Counterfactual Action, Speculative Regret, and Epistemic Second-Best

Formal mathematical specification for [`Praxeology/Counterfactuals.lean`](../Praxeology/Counterfactuals.lean) and [`Praxeology/CausalCounterfactuals.lean`](../Praxeology/CausalCounterfactuals.lean).

---

## 1. Context-Matched Counterfactual Appraisal and Regret

`MaturationActionModel` records actions, histories, plausibility, outcomes, and preferences without choosing a counterfactual history or maturation time. A deterministic selector is separate optional data in `MaturationSelection`; its `ProjectedOutcome` and `SelectedExAntePurposefulAct` describe that special case explicitly.

`CausalCounterfactualModel` supplies a context relation and an admissibility correspondence for alternative histories and maturation moments. The relation says which circumstances the model holds fixed. It is a substantive modeling premise: membership in the same choice partition or preservation of endowments alone does not establish shared causal context.

`RobustStrictDominates` compares every pair of admissible outcomes in each modeled plausible context. `PurposefulAct` uses this robust comparison and requires maximality against other uniformly available actions. `MatchedRegret` requires a preferred foregone outcome and the actual outcome to be admitted in one common context. `GuaranteedMatchedRegret` requires every admissible alternative outcome in that context to be preferred. The finite causal example demonstrates selector sensitivity alongside robust invariance (`selector_sensitivity_and_robust_invariance`), distinguishes possible from guaranteed regret, and shows that an unmatched branch witness is insufficient for matched regret (`unmatched_branch_is_not_matched_regret`).

A deterministic selector recovers the older selected comparison only under an explicit `SelectionRepresents` certificate. Thus selected evaluation is an optional deterministic special case, while the general causal judgment ranges over the modeled correspondence.

## 1.1 Legacy Branch Comparisons

`CrossBranchRegret` retains an existential comparison across histories without requiring a shared causal context. It is useful for describing a branch difference, but by itself it does not establish causal regret. A result that needs causal regret should use `MatchedRegret` or state and prove an explicit coupling premise.

## 2. Entrepreneurial Profit and Loss Dichotomy

Speculation over an uncertain future event $`E \subseteq \text{History}`$ between two entrepreneurs $`i`$ and $`j`$ represents a heterodoxastic exchange:

1. **Ex-Ante Mutual Purposefulness:** At the moment of contracting $`t`$, both entrepreneurs purposefully act, expecting positive subjective gain over inertia ([`purposeful_speculation_ex_ante_gain_ex_post_selection`](../Praxeology/Counterfactuals.lean#L814)).
2. **Ex-Post Profit and Loss Partition:** Upon maturation at $`\tau > t`$, reality partitions the outcome strictly into pure entrepreneurial profit ($`\text{RealizedGain}`$) for the accurate forecaster and mandatory loss ($`\text{ExPostRegret}`$) for the mistaken forecaster:
```math
   (E(h) \wedge \text{Gain}_i \wedge \text{Loss}_j) \vee (\neg E(h) \wedge \text{Gain}_j \wedge \text{Loss}_i)
```
   ([`entrepreneurial_profit_and_loss_dichotomy`](../Praxeology/Counterfactuals.lean#L790)).
3. **Market Selection Mechanism:** Universal mutual profit in speculative futures is mathematically impossible; the price mechanism systematically redistributes capital toward accurate forecasters and weeds out malinvesting speculators through ordinal losses.

---

## 3. Lawson's Epistemic Second-Best Non-Monotonicity

Following Gary Lawson (2022), technocratic policymaking assumes that acquiring more empirical information necessarily improves decision quality. Our codebase disproves this claim:

* Moving from complete ignorance to strictly *more* true knowledge (learning a true partial fact without comprehending the entire non-linear causal interaction network) can strictly induce ex-post regret:
```math
  \text{Information}(\text{Partial}) > \text{Information}(\text{None}) \not\implies \text{Regret}(\text{Partial}) \le \text{Regret}(\text{None})
```
  ([`lawson_epistemic_second_best_regret`](../Praxeology/Counterfactuals.lean#L837)).
* Technocratic piecemeal optimization in complex market systems is fundamentally non-monotonic.

---

## 4. The Misesian Dynamic Regulatory Cascade

When the state imposes an initial price ceiling below the market-clearing level to make a consumer good "affordable":

1. **Supply Contraction:** Sellers refuse to sell at the controlled price because retention dominates controlled exchange ([`price_ceiling_precludes_purposeful_sale`](../Praxeology/Counterfactuals.lean#L877)).
2. **Shortage Creation:** An acute shortage emerges in the targeted consumer sector.
3. **Downstream/Upstream Spillover:** The state is confronted with a dilemma: either repeal the initial control, or impose price ceilings on all upstream factors of production (labor, raw materials, capital equipment).
4. **The Downward Spiral:** Iterating this interventionist logic across supply networks drives the system stepwise toward total central planning (the Misesian interventionist cascade, [`dynamic_regulatory_cascade_downward_spiral`](../Praxeology/Counterfactuals.lean#L1012), [`action_microfounded_regulatory_cascade`](../Praxeology/Counterfactuals.lean#L1123)).
