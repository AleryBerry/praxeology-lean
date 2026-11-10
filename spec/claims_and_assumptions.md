# Scope and Assumption Register: Meta-Claims about the Formal Codebase

This register documents the foundational assumptions, methodological constraints, and formal meta-claims governing the Lean codebase. Rather than cataloging applied economic theorems, it specifies what the formal framework mathematically presupposes, what it explicitly avoids, and what verified guarantees it provides.

---

## 1. The Single Foundational Assumption: `ActionFrame`

In neoclassical economics, models typically rest on a multiplicity of ad-hoc assumptions—such as utility functions, convex preferences, continuous technology sets, rational expectations, and aggregate equilibrium clearing.

In this formalization, **there are no ad-hoc behavioral assumptions or external hypothesis wrappers**.

The **Action Axiom**, formalized as [`ActionFrame`](../Praxeology/Frame/Core.lean#L276), is the **single foundational premise** of the entire codebase. It supplies the minimal mathematical ontology required to state human choice without introducing artificial neoclassical machinery:

1. **Acting Agents & Finite Menus**: A finite set of acting agents facing finite menus of contemplated and physically feasible alternatives.
2. **Irreversible Branching Time**: Moments form a strict backward-linear partially ordered set (poset). The past is fixed and undivided; the future branches into an open set of realizable histories.
3. **Physical Scarcity & Conservation**: Material endowments are scarce and governed by strict physical transition balance laws. Matter cannot be created or destroyed along action transitions.
4. **Subjective Ordinal Evaluation**: At each decision node, an actor's evaluation is modeled as an asymmetric ordinal preference relation ($\succ$) over intended ends.

All results in the library are deductive derivations from `ActionFrame`. Specific economic environments (such as bilateral exchange, banking, or fiscal extraction) do not introduce new behavioral axioms; they are simply **concrete institutional configurations** defining specific actors, initial endowments, feasible contracts, and transaction rules within that same underlying ActionFrame.

---

## 2. Methodological Non-Assumptions (What the Code Explicitly Excludes)

The codebase enforces strict modeling boundaries (audited programmatically by [`scripts/audit_adhoc_premises.py`](../scripts/audit_adhoc_premises.py) and [`scripts/audit_axiomatic_floor.py`](../scripts/audit_axiomatic_floor.py)) to prevent neoclassical distortion:

* **No Cardinal Utility or Payoff Matrices**: The formalization excludes cardinal utility numbers, utils, indifference curves, and standalone game-theoretic payoff matrices. Choice is strictly comparative and ordinal.
* **No Equilibrium Forcing (No Assumed Market Clearing)**: Markets do not clear by assumption or mathematical fiat. Clearing occurs only when individual buyers and sellers voluntarily execute matched actions.
* **No Representative Agents or Macro Aggregates**: The codebase contains no representative consumer, aggregate production function, or macro price-level variable. Systemic phenomena emerge entirely from the interacting choices of heterogeneous individuals.
* **No Exogenous Stochastic Shocks**: Crises, capital malinvestment, factor bottlenecks, and defaults are not driven by external stochastic shocks ($\epsilon_t$); they are derived endogenously from credit expansion interacting with scarce physical capital.
* **No Omniscience or Rational Expectations**: Uncertainty is modeled through open branching histories and subjective plausibility sets. Actors can hold mistaken beliefs, formalizing the reality of entrepreneurial error and ex-post regret.

---

## 3. Formal Meta-Claims about the Codebase

The formalization makes six specific meta-claims regarding the mathematical and logical integrity of the code:

### 3.1 Kernel Verification and Deductive Soundness
* **Zero Custom Axioms**: The codebase introduces **zero custom Lean `axiom` declarations**.
* **Zero Incomplete Proofs**: The repository contains **zero unfinished `sorry` placeholders**.
* **Standard Logical Core**: The entire proof library relies exclusively on standard Lean 4 kernel foundations: `propext` (propositional extensionality), `Classical.choice` (classical choice operator), and `Quot.sound` (quotient soundness).

### 3.2 Non-Vacuity & Model-Theoretic Realizability
A formal theorem is logically vacuous if its premises contain hidden contradictions (since `False → P`). To ensure non-vacuity and physical realizability, the codebase constructs explicit, constructive model witnesses for all major theoretical frameworks:
* **Frame Consistency**: [`action_frame_consistent`](../Praxeology/Frame/Witnesses.lean#L508) constructs an explicit non-trivial branching time frame.
* **Bilateral Trade Realizability**: [`subjective_bilateral_trade_action_frame_witness`](../Praxeology/Catallactics.lean#L1417) constructs a fully instantiated market frame verifying purposeful trade execution.
* **Firm Boundary Realizability**: [`WorkshopActionFrame`](../Praxeology/FirmWitness.lean#L665) constructs an explicit three-agent workshop verifying internal delegation, factor pricing, and customer delivery.
* **Credit Lifecycle Realizability**: [`creditLifecycleActionFrame`](../Praxeology/BusinessCycle/CreditLifecycleFrame.lean#L1318) constructs an explicit contractual loan frame tracking issuance, advance, custodial collateral, and default.

### 3.3 Deductive Separation: Invariant Laws vs. Contingent Branches
The codebase formally distinguishes between two levels of economic claims:
1. **Universal Praxeological Invariants**: Categories that hold for all purposeful human actions across all branches (e.g., choice under scarcity, diminishing marginal utility, opportunity cost, and time preference).
2. **Contingent Institutional Trajectories**: Outcomes that depend on which branch of actions is enacted within a given institutional frame (e.g., whether voluntary exchange creates mutual gains, or unbacked credit expansion induces malinvestment and cluster defaults).

### 3.4 Formal Limitative Theorems
The codebase formally proves mathematical boundaries on what can be known, identified, or calculated:
* **Econometric Identification Limits**: [`lucas_critique_policy_invariance_failure`](../Praxeology/EconometricLimits.lean#L156) proves that historical empirical observations cannot guarantee policy invariance when counterfactual choice menus change.
* **Calculation Incommensurability**: [`socialist_calculation_incommensurability`](../Praxeology/Catallactics.lean#L3947) gives two numerical encodings preserving one ordinal ranking while reversing a sum comparison. It does not establish the absence of prices or rule out other allocation procedures. [`action_frame_socialist_calculation_impossibility`](../Praxeology/Catallactics.lean#L4084) assumes matching records and opposite local preferences. The strategic interfaces and institutional ledger transitions in [`EconomicCalculation.lean`](../Praxeology/EconomicCalculation.lean) do not yet derive those assumptions from a command economy.
* **Epistemic Indistinguishability**: Proves that identical quoted gross repayment factors across fiduciary and voluntary regimes produce observationally indistinguishable signals at the decision node without explicit source disclosure.

---

## 4. Summary of Code Guarantees

| Meta-Property | Formal Status in Codebase | Verification Mechanism |
|---|---|---|
| **Axiomatic Floor** | Single primitive: `ActionFrame` | Machine-checked Lean kernel |
| **Custom Axioms** | None (0) | `scripts/audit_constructive_axioms.py` |
| **Unfinished Proofs** | None (0 `sorry`) | Lean 4 compiler build check |
| **Ad-Hoc Wrappers** | None (0) | `scripts/audit_adhoc_premises.py` |
| **Ontological Leakage** | None (0) | `scripts/audit_axiomatic_floor.py` |
| **Model Realizability** | Constructive witnesses instantiated | Verified `Witnesses` modules |
| **Cross-Doc Consistency** | 100% verified across specs, essays, prose | `scripts/update_theorem_links.py` |
