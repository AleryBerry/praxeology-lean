# Specification 03: Ordinal Diminishing Marginal Utility, Mengerian Imputation, Time Preference, and Originary Interest

Formal mathematical specification for [`Praxeology/Marginal.lean`](../Praxeology/Marginal.lean).

---

## 1. Choice-Free Ordinal Diminishing Marginal Utility (DMU)

Neoclassical models define marginal utility by differentiating a continuous utility function ($`\partial U / \partial x`$). In contrast, praxeological DMU is strictly ordinal and discrete:

* **Homogeneous Units:** A supply of $`k`$ discrete, interchangeable units of means $`m \in M`$.
* **Ranked Teleological Ends:** A finite hierarchy of distinct ends $`e_1 \succ e_2 \succ \dots \succ e_N`$, where each end requires one unit of $`m`$.
* **Economizing Allocation:** An acting agent allocates available units to attain the most urgent of their valued ends.
* **Marginal Unit Definition:** The value of a marginal unit is imputed from the *least urgent end* among the realized set:
```math
  \text{MU}(m, k) := e_k
```
  ([`mengerian_least_urgent_end_exists`](../Praxeology/Marginal.lean#L982)).

### Theorems on Marginal Sacrifice and Complementarity

1. **Marginal Sacrifice Theorem:** If the supply of means contracts from $`k`$ to $`k - 1`$, the agent surrenders the least important goal $`e_k`$, never an infra-marginal goal $`e_j`$ ($`j < k`$) ([`mengerian_marginal_sacrifice_exists`](../Praxeology/Marginal.lean#L992)).
2. **Complementarity Breakdown:** When units of means exhibit non-additive joint complementarity (e.g., left and right shoes, or chemical reagents requiring exact stoichiometry), DMU applies to the *integral teleological quantum*, not to isolated physical components ([`dmu_fails_under_complementarity`](../Praxeology/Marginal.lean#L1498)).

---

## 2. Mengerian Backward Value Imputation and Factor Specificity

Value does not flow forward from labor costs or physical inputs into consumer goods (refuting the Labor Theory of Value and sunk-cost fallacies); rather, subjective value is imputed *backward* from expected consumer ends to higher-order capital goods:

```math
\text{Value}(m_{\text{capital}}) \longleftarrow \text{Value}(e_{\text{consumer}})
```
([`mengerian_backward_value_imputation`](../Praxeology/Marginal.lean#L458)).

### The Factor Specificity Dichotomy

Let $`m`$ be a higher-order production factor:
1. **Specific Factors:** If factor $`m`$ can only be utilized in producing a single good $`c`$, then if consumer demand for $`c`$ collapses to zero, the subjective value of $`m`$ experiences immediate total collapse.
2. **Versatile Factors:** If factor $`m`$ possesses multiple alternate production avenues ($`c_1, c_2, \dots, c_r`$), its value is cushioned by the marginal opportunity yield of the next-best alternative employment.
([`mengerian_factor_specificity_dichotomy`](../Praxeology/Marginal.lean#L556)).

---

## 3. Universal Positive Time Preference and Originary Interest

### Action-Derived Time Preference

Praxeology establishes positive time preference not as an empirical psychological quirk, but as an inescapable praxeological category:

* **Action Horizon Impossibility:** If an agent held negative time preference across all ends ($`\forall \tau_1 < \tau_2, \langle e, \tau_2 \rangle \succ \langle e, \tau_1 \rangle`$), the agent would perpetually postpone consumption into the infinite future, rendering purposeful action impossible prior to biological expiration ([`causal_not_purposeful_immediate_consumption_of_negative_time_pref`](../Praxeology/Marginal.lean)).
* **Demonstrated Time Preference:** Any enacted consumption at moment $`t`$ demonstrates that satisfaction in the nearer future is preferred to satisfaction in the more remote future ([`causal_enacted_consumption_demonstrates_strict_time_pref`](../Praxeology/Marginal.lean)).

### Originary Interest Rate ($`\iota > 0`$)

From universal positive time preference, the originary interest rate emerges directly from the intertemporal price discount of future goods against present goods:

1. **Rejection of Unit-for-Unit Exchange:** Under stationary endowments, an agent strictly rejects trading 1 present unit of $`m`$ for 1 future unit of $`m`$:
```math
   \langle 1, \tau_1 \rangle \succ_{i,t,h} \langle 1, \tau_2 \rangle \quad (\tau_1 < \tau_2)
```
   ([`purposeful_unit_for_unit_exchange_rejected`](../Praxeology/Marginal.lean#L1174)).
2. **Strictly Positive Originary Premium:** Any voluntary intertemporal exchange of present means for future means requires a strictly positive agio $`\delta > 0`$, yielding an originary interest rate:
```math
   \iota = \frac{q' - q}{q} = \frac{\delta}{q} > 0
```
   ([`positive_originary_interest`](../Praxeology/Marginal.lean#L1188), [`purposeful_positive_originary_interest`](../Praxeology/Marginal.lean#L1216)).

---

## 4. The Autumn-Winter Food Security and Saving Theorem

A classical critique asserts that storing grain in autumn for winter consumption contradicts positive time preference. Our codebase resolves this paradox by proving that seasonal saving is an instance of **end-individuation under DMU**, not negative time preference:

* Eating surplus food in autumn serves lower-ranked, satiated desires ($`e_{\text{autumn luxury}}`$).
* Preserving grain for winter secures survival and basic caloric needs ($`e_{\text{winter survival}}`$).
* Because $`e_{\text{winter survival}} \succ e_{\text{autumn luxury}}`$, saving demonstrates high subjective valuation of survival, fully consistent with universal positive time preference ([`saving_for_winter_is_positive_time_pref_for_security`](../Praxeology/Marginal.lean#L1310)).
