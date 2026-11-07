# Specification 02: Purposeful Action, Demonstrated Preference, Opportunity Cost, and Dialectical Consistency

Formal mathematical specification for [`Praxeology/Action.lean`](../Praxeology/Action.lean).

---

## 1. The Praxeological Action Axiom (`PurposefulAct`)

In our constructive formalization, purposeful human action is defined as **undominated choice relative to an inertial baseline** ($`\alpha_0`$), eliminating the need for unphysical injectivity axioms:

```lean
def PurposefulAct (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  α_star ∈ A_feas i t h ∧
  Exec i t α_star h ∧
  (α_star = α₀ ∨ Preference i t h (End_of i α_star t h) (End_of i α₀ t h)) ∧
  ∀ β ∈ A_feas i t h, ¬ Preference i t h (End_of i β t h) (End_of i α_star t h)
```
([`PurposefulAct`](../Praxeology/Action.lean#L232)).

### Structural Components

1. **Feasibility:** The chosen action $`\alpha^{\ast}                                                  \alpha^{\ast} \in \mathcal{A}_i(t, h)`$.
2. **Physical Execution:** The action is enacted along history $`h      \text{Exec}(i, t, \alpha^{\ast}, h)`$.
3. **Baseline comparison:** Either the selected action is the passive baseline or its end is preferred to the baseline end. Thus purposeful inaction is allowed; an active action must improve on the baseline.
```math
   \text{End}(i, \alpha^{\ast}, t, h) \succ_{i,t,h} \text{End}(i, \alpha_0, t, h)
```
4. **Undominated Optimality:** No feasible alternative realizes an end strictly preferred to that of $`\alpha^{\ast}`$:
```math
   \forall \beta \in \mathcal{A}_i(t, h), \quad \neg (\text{End}(i, \beta, t, h) \succ_{i,t,h} \text{End}(i, \alpha^{\ast}, t, h))
```

### Foundational Properties

* **Active-action theorem:** If the purposeful action's end is strictly preferred to the baseline, then its action and end both differ from the baseline:
```math
  \text{PurposefulAct}(i, t, h, \alpha^{\ast}) \wedge \text{End}(\alpha^{\ast}) \succ \text{End}(\alpha_0) \implies \alpha^{\ast} \neq \alpha_0 \wedge \text{End}(\alpha^{\ast}) \neq \text{End}(\alpha_0)

This implication requires the stated strict-preference premise; purposeful
action by itself also permits the passive baseline.
```
  ([`purposeful_act_non_passive`](../Praxeology/Action.lean#L378)).
* **Buridan Tie Compatibility:** Because optimality is undominated rather than strictly dominant, two distinct physical actions $`\alpha_1 \neq \alpha_2`$ serving identical ends ( $`\text{End}(\alpha_1) = \text{End}(\alpha_2)`$ ) are admitted without producing logical contradiction ($`\bot`$) ([`buridan_tie_refutes_strict_demonstrated_pref`](../Praxeology/Action.lean#L1009), [`buridan_tie_compatible_with_purposeful_act`](../Praxeology/Action.lean#L524)).

---

## 2. Demonstrated Preference with Prenex Scope Guardrail

Following Definition 4.3 of *A Formalization of Austrian Economics* ($`T_{\text{prx}}`$) while dropping menu completeness (O2) in favor of undominated choice, our codebase positions the quantification over rejected alternatives strictly within the relational assertion:

```lean
def DemonstratedPref (i : Agent) (t : Moment) (h : History) (α_star β : Action) : Prop :=
  PurposefulAct i t h α_star ∧ β ∈ (A_feas i t h).erase α_star
```
([`DemonstratedPref`](../Praxeology/Action.lean#L289)).

### Catallactic Consistency

* **Pairwise Asymmetry:** If $`\alpha^{\ast}                                  \beta      \beta                                         \alpha^{\ast}`$:
```math
  \text{DemonstratedPref}(i, t, h, \alpha^{\ast}, \beta) \implies \neg \text{DemonstratedPref}(i, t, h, \beta, \alpha^{\ast})
```
  ([`demonstrated_pref_grounding`](../Praxeology/Action.lean#L307)).
* **Multi-Option Consistency:** For menus of size $`|\mathcal{A}_i(t, h)| \ge 3`$, no execution cycles or contradictory multiple simultaneous choices are forced ([`purposeful_act_unique_execution`](../Praxeology/Action.lean#L476)).

---

## 3. Set-Valued Opportunity Cost Frontier (`OCSet`)

Our codebase eliminates the assumption of local preference completeness (O2) over unchosen ends. Opportunity cost is defined as the undominated frontier of foregone ends on a finite partially ordered set:

```lean
def ForegoneEnds (i : Agent) (t : Moment) (h : History) (α_star : Action) : Finset Ends :=
  ((A_feas i t h).erase α_star).image (fun β => End_of i β t h)

def OCSet (i : Agent) (t : Moment) (h : History) (α_star : Action) : Finset Ends :=
  (ForegoneEnds i t h α_star).filter (fun e =>
    ∀ e' ∈ ForegoneEnds i t h α_star, ¬ Preference i t h e' e)
```
([`StrictForegoneEnds`](../Praxeology/Action.lean#L677), [`StrictOCSet`](../Praxeology/Action.lean#L729)).

### Structural Theorems

1. **Existence under Transitivity:** When preference is transitive over foregone ends, the opportunity cost set is guaranteed non-empty:
```math
   \text{ForegoneEnds}.\text{Nonempty} \implies (\text{OCSet}(i, t, h, \alpha^{\ast})).\text{Nonempty}
```
   ([`strict_ocset_nonempty_of_trans`](../Praxeology/Action.lean#L784)).
2. **Subsumption of Classical Uniqueness:** When local connectedness (comparability) holds across all foregone alternatives, $`\text{OCSet}`$ contracts to a unique singleton:
```math
   |\text{OCSet}(i, t, h, \alpha^{\ast})| = 1
```
   ([`strict_ocset_singleton_of_connected`](../Praxeology/Action.lean#L815)), recovering textbook opportunity cost as a special regime condition rather than an ontological axiom.

---

## 4. Performative Consistency and Pragmatic Self-Falsification

We decouple acoustic token emission from purposeful semantic communication:

```lean
def Asserts (i : Agent) (t : Moment) (h : History) (_p : Prop) : Prop :=
  ∃ α ∈ A_feas i t h, PurposefulAct i t h α

def DenialOfAction (i : Agent) (t : Moment) (h : History) : Prop :=
  ¬ ∃ α ∈ A_feas i t h, PurposefulAct i t h α
```
([`Asserts`](../Praxeology/Action.lean#L895), [`NoPurposefulActionProp`](../Praxeology/Action.lean#L909)).

### Theorem 1.1b (Pragmatic Self-Falsification of Action Denial)

Let $`P_{\text{no act}}`$ be the universal proposition asserting that no agent ever acts purposefully:
```math
P_{\text{no act}}(h') := \forall j, t', \alpha, \neg \text{PurposefulAct}(j, t', h', \alpha)
```
If an agent $`i`$ purposefully asserts $`P_{\text{no act}}`$ at node $`\langle t, h \rangle`$, then:
1. $`P_{\text{no act}}(h)`$ is false at world $`h`$.
2. The assertion cannot be veridical:
```math
   \neg \text{VeridicalClaim}(i, t, h, \text{content}, P_{\text{no act}})
```
   ([`dialectical_self_falsification_under_deliberative_norms`](../Praxeology/Action.lean#L985)).

The result is conditional on the structured `DeliberativeEpistemicAssertion`
premises, including assertion, belief, counterexample-history, response, and
preference-norm evidence. It does not establish that every utterance denying
purposeful action is self-falsifying.
