# Specification 08: Causal Econometric Non-Identifiability and Epistemic Boundaries

Formal mathematical specification for [`Praxeology/EconometricLimits.lean`](../Praxeology/EconometricLimits.lean).

---

## 1. The Master Non-Identifiability Principle

Positivist and econometric methodologies attempt to derive causal laws solely from historical time-series data. Praxeology demonstrates that under forward-looking teleological expectations, structural economic parameters are mathematically non-identifiable without unprovable a priori assumptions:

* **Observational Equivalence:** Two economic models $`C_1, C_2`$ are observationally equivalent along realized history $`h`$ if they generate identical historical data traces:
```math
  \text{observe}(C_1, i, t, h) = \text{observe}(C_2, i, t, h)
```
  ([`ObsEquiv`](../Praxeology/EconometricLimits.lean#L66)).
* **Master Theorem:** If there exist two models $`C_1, C_2 \in \mathcal{M}`$ that are observationally equivalent along history $`h`$, but possess strictly divergent structural parameters ( $`f(C_1) \neq f(C_2)`$ ), then **no** econometric estimator can identify $`f`$ on $`\mathcal{M}`$ from historical data:
```math
  \neg \exists \text{est}, \quad \text{Identifies}(\mathcal{M}, f, \text{est}, i, t, h)
```
  ([`non_identifiability_of_divergent_models`](../Praxeology/EconometricLimits.lean#L84)).

---

## 2. Causal Non-Identifiability under Branching Time

Because human action implies an open, branching universe where counterfactual options remain unchosen:

* Let an agent purposefully execute $`\alpha^{\ast}             \langle t, h \rangle`$.
* Along the realized path $`h`$, the outcome of the unchosen counterfactual alternative $`\alpha_0`$ along counterfactual branch $`h_0`$ is never observed.
* If the universe of ends contains at least two distinct elements, there exists an alternative model $`C_2`$ that produces identical observed data on $`h`$ and constitutes a valid purposeful action model, yet predicts a contradictory outcome on branch $`h_0`$:
```math
  \text{BranchCausalParam}(C_1, h_0, \alpha_0) \neq \text{BranchCausalParam}(C_2, h_0, \alpha_0)
```
  ([`causal_econometric_non_identifiability`](../Praxeology/EconometricLimits.lean#L102)).
* Causal parameters on unchosen counterfactual paths cannot be estimated from historical data without arbitrary non-empirical restrictions.

---

## 3. Generalized Lucas Critique: Policy Invariance Failure

Econometric policy simulations assume that statistical regression equations estimated from past regimes remain invariant when policy rules change. Praxeological teleology refutes this:

* Suppose a policy intervention alters the anticipated payoff of a hitherto rejected option $`\beta          e_{\text{bad}}        e_{\text{great}}                e_{\text{great}}                                       \alpha^{\ast}`$.
* The agent's teleological choice mathematically shifts away from $`\alpha^{\ast}            \beta`$.
* Historical behavioral coefficients break down precisely because acting human beings possess purposeful forward-looking agency ([`lucas_critique_policy_invariance_failure`](../Praxeology/EconometricLimits.lean#L137)).

---

## 4. Instrumental Variable Exclusion Restriction Unverifiability

Modern empirical econometrics relies heavily on Instrumental Variables (IV) to infer causality, requiring that instrument $`Z`$ affects the outcome *only* through treatment $`\alpha`$ (the Exclusion Restriction):

* When only treatment $`\alpha^{\ast}                                                                                                  \alpha_{\text{alt}}`$) cannot be empirically verified.
* There exist two observationally identical structural models—one satisfying the exclusion restriction globally, and one violating it on unchosen actions:
```math
  \text{IV}_{\text{invalid}}(z_1, \alpha_{\text{alt}}) \neq \text{IV}_{\text{invalid}}(z_2, \alpha_{\text{alt}})
```
  ([`iv_exclusion_restriction_unverifiable`](../Praxeology/EconometricLimits.lean#L168)).
* IV identification rests on an untestable metaphysical leap.

---

## 5. Duhem-Quine Econometric Underdetermination

Given any observed historical trace $`\langle \alpha^{\ast}, e^{\ast} \rangle`$, there always exist at least two distinct structural models that perfectly fit the historical observations while embodying contradictory causal laws across counterfactual scenarios:
```math
\text{Outcome}_1(i, \alpha_{\text{cf}}, t, h) \neq \text{Outcome}_2(i, \alpha_{\text{cf}}, t, h)
```
([`duhem_quine_underdetermination`](../Praxeology/EconometricLimits.lean#L208)).

This formally establishes the Misesian epistemological thesis: economic history can illustrate praxeological theorems, but cannot inductively discover or refute fundamental economic laws.

---

## 6. Macro-Aggregate Observational Equivalence & Regime Non-Identifiability

A key challenge in macroeconomic identification is distinguishing a sustainable expansion from an artificial credit boom. In our formalization:

* **Structural Capital Regimes:** An economy's true state is partitioned into two regimes ([`CapitalRegime`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/EconometricLimits.lean#L253)):
  * `Absorption`: Capital projects are backed by sufficient voluntary deferred consumption or physical buffer inventory.
  * `Liquidation`: Early-stage projects exceed physical completion capacity, mandating midstream abandonment.
* **Theorem 9.6 (Macro Observational Equivalence):**
  At boom origination moment $`t_0`$, both regimes generate identical observable macroeconomic traces (identical early-stage investment choices $`\alpha_{\text{stage1}}`$ and identical realized output):
```math
  \text{ObsEquiv}(C_{\text{absorb}}, C_{\text{liquidate}}, i, t_0, h)
```
  By the Master Non-Identifiability Principle, **no** econometric estimator operating on macroeconomic time series can identify whether the system occupies the Absorption or Liquidation regime:
```math
  \neg \exists \text{est}, \quad \text{Identifies}(\mathcal{M}, \text{regimeOf}, \text{est}, i, t_0, h)
```
  ([`abct_macro_aggregate_regime_non_identifiability`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/EconometricLimits.lean#L260), [`observable_data_generating_regime_non_identifiability`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/EconometricLimits.lean#L370)).
* **Witness:** The non-identifiability theorem is constructively witnessed over finite types ([`abct_regime_non_identifiability_witness`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/EconometricLimits.lean#L276), [`macro_crisis_observation_equivalence_witness`](../Praxeology/BusinessCycle.lean)) with strictly zero axioms (`[]`).
* **Epistemological Consequence:** Discerning sustainable investment from monetary malinvestment cannot be achieved by aggregate regression models alone; it requires microeconomic capital accounting, time-to-build specificity, and physical factor endowment tracking (*Laws in Re*).
