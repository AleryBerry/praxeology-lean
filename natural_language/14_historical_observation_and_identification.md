# Chapter 14: Historical Observation and Identification

We ask which features of an economic model can be recovered from a record of enacted actions and realized outcomes. The results are conditional identification statements. They show what a specified observation rule does or does not determine; they do not settle general disputes about empirical economics.

## Models and Their Observable Records

To ask what an empirical record determines, we first specify an action frame and the candidate interpretations that an econometrician might consider. Let $W$ be an action frame with agents, moments, histories, feasible menus, and enacted actions. An econometric candidate interpretation specifies an outcome mapping $(i, \alpha, t, h) \mapsto \mathcal{O}(i, \alpha, t, h)$ and an asymmetric preference relation $\succ_{i, t, h}$ over ends.

An enacted action $\alpha^{\ast} = \text{enacted}(i, t, h)$ is purposeful under an interpretation when:

1. $\alpha^{\ast}$ is feasible for agent $i$ at $(t, h)$;
2. $\alpha^{\ast}$ is enacted at $(i, t, h)$;
3. either $\alpha^{\ast}$ is the passive action $\alpha_0$, or its outcome is strictly preferred to the outcome of $\alpha_0$ under $\succ_{i, t, h}$; and
4. no feasible alternative $`\beta \in \mathcal{A}_{\mathrm{feas}}(i, t, h)`$ yields an outcome strictly preferred to $\alpha^{\ast}$'s outcome under $\succ_{i, t, h}$.

For an action frame $W$, interpretation, agent $i$, moment $t$, and history $h$ containing $t$, an empirical historical observation consists of the enacted action and its realized outcome:

$$
\mathcal{O}_{\mathrm{obs}}(W, \text{interp}, i, t, h) = \bigl(\text{enacted}(i, t, h),\; \mathcal{O}_{\text{interp}}(i, \text{enacted}(i, t, h), t, h)\bigr).
$$

Two interpretations are observationally equivalent at $(i, t, h)$ when their empirical observations coincide:

$$
\text{ObsEquiv}(W, \text{interp}_1, \text{interp}_2, i, t, h) \iff \mathcal{O}_{\mathrm{obs}}(W, \text{interp}_1, i, t, h) = \mathcal{O}_{\mathrm{obs}}(W, \text{interp}_2, i, t, h).
$$

This observation rule records the actual action and its realized outcome, not unchosen alternatives, subjective preferences, or counterfactual branches. An econometric estimator is a mapping from historical observations to a target parameter space $\Theta$. An estimator identifies a parameter function $f : \mathcal{M} \to \Theta$ over an admissible class $\mathcal{M}$ of interpretations at $(i, t, h)$ when $`\text{est}(\mathcal{O}_{\mathrm{obs}}(W, \text{interp}, i, t, h)) = f(\text{interp})`$ for all $\text{interp} \in \mathcal{M}$.

### Theorem 14.1 (Non-identification from Equal Records)
Let $\mathcal{M}$ be an admissible class of interpretations and $f : \mathcal{M} \to \Theta$ a target structural parameter. If two interpretations $`\text{interp}_1, \text{interp}_2 \in \mathcal{M}`$ produce the same historical observation at $(i, t, h)$ but diverge in the target parameter:

$$
\mathcal{O}_{\mathrm{obs}}(W, \text{interp}_1, i, t, h) = \mathcal{O}_{\mathrm{obs}}(W, \text{interp}_2, i, t, h) \quad \land \quad f(\text{interp}_1) \neq f(\text{interp}_2),
$$

then no empirical estimator depending only on that historical observation can identify $f$ correctly over $\mathcal{M}$ at $(i, t, h)$.

**Proof.** Suppose toward a contradiction that such an estimator $\text{est}$ exists. By the identification condition, $`\text{est}(\mathcal{O}_{\mathrm{obs}}(W, \text{interp}_1, i, t, h)) = f(\text{interp}_1)`$ and $`\text{est}(\mathcal{O}_{\mathrm{obs}}(W, \text{interp}_2, i, t, h)) = f(\text{interp}_2)`$. Because the two historical observations are identical, $\text{est}$ receives the same input and evaluates to the same output: $`f(\text{interp}_1) = f(\text{interp}_2)`$, which directly contradicts $`f(\text{interp}_1) \neq f(\text{interp}_2)`$. $\square$

The conclusion depends on the observation rule and the admissible model class. Additional observations or structural restrictions on admissible models may restore identification. The theorem says that the realized historical observation alone cannot distinguish two models that share that record.

## Unobserved Counterfactual Outcomes

The empirical record captures only the action enacted along the realized history. A counterfactual asks what an alternative choice would have produced.

### Theorem 14.2 (Counterfactual Outcomes Can Vary without Changing the Record)
Let $\text{interp}$ be an interpretation where $\alpha^{\ast} = \text{enacted}(i, t, h)$ is purposeful at $(i, t, h)$. Let $`\beta \in \mathcal{A}_{\mathrm{feas}}(i, t, h)`$ be a distinct feasible action ($\beta \neq \alpha^{\ast}$). Then there exists an alternative interpretation $\text{interp}'$ such that:

1. $\alpha^{\ast}$ remains purposeful at $(i, t, h)$ under $\text{interp}'$;
2. the empirical historical observation at $(i, t, h)$ is unchanged: $`\mathcal{O}_{\mathrm{obs}}(W, \text{interp}', i, t, h) = \mathcal{O}_{\mathrm{obs}}(W, \text{interp}, i, t, h)`$; and
3. the counterfactual outcome of $\beta$ differs between the two interpretations: $`\mathcal{O}_{\text{interp}'}(i, \beta, t, h) \neq \mathcal{O}_{\text{interp}}(i, \beta, t, h)`$.

**Proof.** Define $\text{interp}'$ to coincide with $\text{interp}$ on all inputs except for assigning $\beta$ an outcome $`e' \neq \mathcal{O}_{\text{interp}}(i, \beta, t, h)`$ such that $`\neg(e' \succ_{i, t, h} \mathcal{O}_{\text{interp}}(i, \alpha^{\ast}, t, h))`$. Since $\beta \neq \alpha^{\ast}$, the outcome of the enacted action $\alpha^{\ast}$ is identical between the two interpretations, so the historical observations match. Because $e'$ does not dominate $\alpha^{\ast}$'s outcome, $\alpha^{\ast}$ remains undominated and purposeful under $\text{interp}'$. Thus the counterfactual outcome varies without altering the realized observation. $\square$

## Choice under a Changed Outcome Structure: The Lucas Critique

An observed action can be purposeful in one structure and fail to be purposeful in another structure that shares the exact same realized action and outcome.

### Proposition 14.3 (Lucas Critique: Feasible Improvement Removes Purposefulness)
Suppose $\alpha^{\ast}$ is enacted at $(i, t, h)$ and purposeful under interpretation $\text{interp}$, and let $\beta \neq \alpha^{\ast}$ be a distinct feasible action. Construct an alternative interpretation $\text{interp}'$ that preserves the enacted action and its realized outcome:

$$
\mathcal{O}_{\text{interp}'}(i, \alpha^{\ast}, t, h) = \mathcal{O}_{\text{interp}}(i, \alpha^{\ast}, t, h),
$$

but modifies the outcome or valuation of $\beta$ such that $\beta$'s outcome is strictly preferred to $\alpha^{\ast}$'s outcome:

$$
\mathcal{O}_{\text{interp}'}(i, \beta, t, h) \succ_{i, t, h} \mathcal{O}_{\text{interp}'}(i, \alpha^{\ast}, t, h).
$$

Then $\alpha^{\ast}$ is not purposeful under $\text{interp}'$, despite identical historical observations.

**Proof.** In $\text{interp}'$, the action $\beta$ is feasible and its outcome is strictly preferred to the outcome of $\alpha^{\ast}$. This directly violates the undominatedness condition of purposeful action for $\alpha^{\ast}$. $\square$

This proposition isolates the deliberative threshold relevant to the Lucas critique: historical observation of a chosen action cannot guarantee that the choice remains invariant when the consequences of feasible alternatives change.

## What an Instrumental-Variable Observation Leaves Open

An exclusion restriction imposes invariance across counterfactual instrument values and unchosen actions, demanding structural assumptions beyond the single action actually realized.

### Proposition 14.4 (Observed Outcomes Need Not Determine an Exclusion Restriction)
Let $z_1 \ne z_2$ be two instrument values and let $\alpha^{\ast} \ne \alpha'$ be two actions. There are two potential-outcome functions that agree on the outcome of $\alpha^{\ast}$ at both instrument values, while:

1. the first function gives the same outcome at $z_1$ and $z_2$ for every action; and
2. the second function gives different outcomes at $z_1$ and $z_2$ for action $\alpha'$.

**Proof.** Assign one common outcome to $\alpha^{\ast}$ at both instrument values in both functions. For every other action, let the first function be constant in the instrument. Let the second assign distinct outcomes to $\alpha'$ at $z_1$ and $z_2$. The functions agree on the specified observed-action outcomes but differ on whether the instrument changes an outcome for an unobserved action. $\square$

This proposition rigorously proves the epistemic underdetermination of instrumental variables: empirical observation of the enacted path leaves off-path potential outcomes unconstrained, requiring explicit theoretical assumptions to identify counterfactual effects.

## Joint Hypotheses and Auxiliary Conditions

Suppose an empirical test concerns a conjunction $H_1 \land \cdots \land H_n$ of a theoretical core and auxiliary conditions. A rejection establishes only that at least one conjunct fails:

$$
\neg(H_1 \land \cdots \land H_n) \iff \neg H_1 \lor \cdots \lor \neg H_n.
$$

This proposition formalizes the Duhem-Quine thesis: an empirical refutation of a compound theoretical prediction establishes the falsity of the conjunction $\neg (H_1 \wedge \cdots \wedge H_n)$, demonstrating that isolating the specific failed auxiliary assumption requires independent, structurally identified tests.

## Regime Labels and Equal Observations

The same identification argument applies when the parameter of interest is a regime label. If two models have the same observable record but different labels, no estimator based only on that record identifies the label on a class containing both models.

### Corollary 14.5 (Regime Non-identification)
Let $r(\text{interp})$ assign a regime label to each interpretation. If $`\text{interp}_1`$ and $`\text{interp}_2`$ have equal records at $(i,t,h)$ but $`r(\text{interp}_1) \ne r(\text{interp}_2)`$, then no estimator based only on that record identifies the regime label for both interpretations.

**Proof.** Apply [Theorem 14.1](#theorem-141-non-identification-from-equal-records) with the regime label $r$ as the parameter of interest. $\square$

## Macro-Aggregate Capital Regime Non-Identifiability

We can make the identification limit concrete for the absorption and liquidation labels analyzed in Chapter 13. Consider two economic interpretations with identical macro-aggregate loan quantities and nominal expenditure at an initial observation. In the first interpretation, the economy completes the investment run through adequate complementary factor stocks (absorption). In the second interpretation, complementary factor starvation triggers premature abandonment and asset restructuring (liquidation).

### Corollary 14.6 (Macro Aggregates Do Not Identify the Capital Regime)
There exist two finite interpretations in an action frame that agree on the observed macro-aggregate action and realized output at an initial decision point but receive opposite absorption and liquidation labels from their structural factor paths. Consequently, no empirical estimator that uses only that initial macro aggregate can identify the capital regime correctly across a class containing both.

**Proof.** Both interpretations share the identical initial enacted loan issuance and initial observed yield. In the absorption interpretation, complementary input stocks are sufficient, leading to successful maturation. In the liquidation interpretation, real complementary savings are deficient, leading to factor shortages and liquidation. Because their initial historical observations are identical, [Theorem 14.1](#theorem-141-non-identification-from-equal-records) precludes any estimator based solely on that initial record from identifying the regime. $\square$

## Auxiliary Assumptions and Counterfactual Underdetermination

Observed action-outcome agreement can also leave an auxiliary hypothesis undetermined. We can hold fixed the realized outcome and assign different outcomes to an action that was not taken.

### Proposition 14.7 (Duhem-Quine Underdetermination of Auxiliary Claims)
Let $\alpha^{\ast}$ be the observed action and $\alpha'$ a distinct feasible alternative. There exist two outcome assignments that assign the same outcome to $\alpha^{\ast}$ at the observed decision point but assign different outcomes to $\alpha'$ there.

**Proof.** Assign a common end to $\alpha^{\ast}$ in both functions. Assign distinct ends to $\alpha'$ in the two functions. Since $\alpha' \neq \alpha^{\ast}$, the change leaves the realized observation pair unchanged while altering the counterfactual property. $\square$

When an empirical hypothesis depends jointly on a theoretical assertion and an auxiliary claim about unchosen actions, agreement with realized observations alone cannot uniquely identify the auxiliary claim. The examples in this chapter isolate information lost when observations exclude unchosen actions, unobserved histories, or structural restrictions. In an application, we must therefore state the observation rule, the target parameter, and the admissible model class before making an identification claim.

## Conclusion

We have proved that equal observed records cannot identify targets that differ across models with those records, and we have exhibited this limit for capital-regime labels, changed outcome structures, and unchosen-action outcomes. These conclusions depend on the observation rule and the set of models under consideration. To continue from theory to a concrete inquiry, we must choose what to observe, define the target precisely, and justify which models the evidence permits us to retain.
