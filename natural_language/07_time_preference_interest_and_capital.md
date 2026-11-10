# Chapter 7: Time Preference, Interest, and Capital

We now extend preference to ends distinguished by their time of realization. This makes it possible to compare immediate and delayed outcomes, but an observed action supports a time-preference conclusion only when the relevant alternatives are available and comparable. We state those conditions before deriving interest or capital results.

> *Prerequisites and scope:* Chapters 1–5. We use temporal order, purposeful choice, and plausible histories to derive conditional comparisons of timed ends, loan quantities, and production methods.

The same physical good can serve an end at different dates, so we represent an end together with its time. We first ask what a feasible deferral alternative can show about immediate choice. We then add comparability and quantity assumptions to derive stricter conclusions about premiums and production methods.

## Timed Ends and the Open Epistemic Horizon

We start with an end indexed by a moment. This notation lets us compare the same end at two dates. The first result uses a feasible deferral to rule out a universal ranking in favor of delay; later results need stronger assumptions to infer strict preference or a positive premium.

### Definition 7.1 (Timed Ends)
Let $\mathcal{E}$ be the set of ends and $\mathcal{T}$ the set of moments. We write $T(e,\tau)$ for the end of realizing $e$ at moment $\tau$:

$$
T(e,\tau) \in \mathcal{E}.
$$

We use $T(e,\tau)$ consistently for timed ends. When a result needs different dates to represent different ends, it states the required injectivity premise explicitly.

### Definition 7.2 (Causal Negative Time Preference)
An agent $i$ exhibits *causal negative time preference* at moment $t$ along history $h$ for end $e$ if, whenever $\tau_1$ is weakly future to $t$ ($t = \tau_1 \lor t \prec \tau_1$) and $\tau_1$ temporally precedes $\tau_2$, the agent strictly prefers realizing $e$ at $\tau_2$ over realizing it at $\tau_1$:

$$
\forall \tau_1, \tau_2 \in \mathcal{T}, \quad (t = \tau_1 \lor t \prec \tau_1) \implies \tau_1 \prec \tau_2 \implies T(e,\tau_2) \succ_{i, t, h} T(e,\tau_1).
$$

This condition compares every earlier-later future pair for the same end at the stated choice context. We use it as a deliberately strong hypothesis in the next impossibility result.

### Definition 7.3 (Causal Doxastic Open Horizon)
An agent $i$ at decision situation $(t,h)$ has a *causal doxastic open horizon* for end $e$, near action $\alpha_{\mathrm{near}}$, and target moment $\tau_1$ if, whenever $\alpha_{\mathrm{near}}$ is feasible and aims at $T(e, \tau_1)$, the moment $\tau_1$ is weakly future to $t$ and there exists a feasible deferral action aiming at the same end at a strictly later moment:

$$
(t = \tau_1 \lor t \prec \tau_1) \land \exists \alpha_{\mathrm{defer}} \in \mathcal{A}_{\mathrm{feas}}(i, t, h),\; \exists \tau_2 \in \mathcal{T},\; \tau_1 \prec \tau_2 \land \mathcal{O}(i, \alpha_{\mathrm{defer}}, t, h) = T(e, \tau_2).
$$

When the deferral action yields an outcome distinct from inaction, the open horizon guarantees that the decision situation is not post-horizon, meaning the feasible menu does not collapse to the singleton $`\{\alpha_0\}`$.

### Proposition 7.4 (Universal Preference for Delay Excludes Purposeful Immediate Choice)
Under the purposeful-choice condition and a causal doxastic open horizon, an agent with causal negative time preference cannot purposefully execute the specified near-consumption action:

$$
\neg \mathsf{P}(i, t, h, \alpha_{\mathrm{near}}).
$$

**Proof.** Suppose, toward a contradiction, that $\alpha_{\mathrm{near}}$ is purposeful.
1. By purposeful choice, $\alpha_{\mathrm{near}}$ is feasible and undominated on the feasible menu:

$$
\forall \beta \in \mathcal{A}_{\mathrm{feas}}(i, t, h), \quad \neg(\mathcal{O}(i, \beta, t, h) \succ_{i,t,h} \mathcal{O}(i, \alpha_{\mathrm{near}}, t, h)).
$$

2. By [Definition 7.3](#definition-73-causal-doxastic-open-horizon), since $\alpha_{\mathrm{near}}$ is feasible and yields $T(e,\tau_1)$, we have $t = \tau_1 \lor t \prec \tau_1$, and there exists a feasible deferral action $`\alpha_{\mathrm{defer}} \in \mathcal{A}_{\mathrm{feas}}(i, t, h)`$ and a moment $\tau_2 \succ \tau_1$ such that $\mathcal{O}(i, \alpha_{\mathrm{defer}}, t, h) = T(e,\tau_2)$.
3. By [Definition 7.2 (Causal Negative Time Preference)](#definition-72-causal-negative-time-preference), since $t = \tau_1 \lor t \prec \tau_1$ and $\tau_1 \prec \tau_2$, the agent strictly prefers deferral:

$$
T(e,\tau_2) \succ_{i,t,h} T(e,\tau_1) \iff \mathcal{O}(i, \alpha_{\mathrm{defer}}, t, h) \succ_{i,t,h} \mathcal{O}(i, \alpha_{\mathrm{near}}, t, h).
$$

4. Since $`\alpha_{\mathrm{defer}} \in \mathcal{A}_{\mathrm{feas}}(i, t, h)`$, this strict preference directly contradicts the undominatedness of $\alpha_{\mathrm{near}}$.

We have found a feasible action whose delayed end is strictly preferred to the near end. That contradicts the requirement that a purposeful action be undominated. $\square$

### Proposition 7.5 (Purposeful Immediate Choice Rules Out Universal Preference for Delay)
If an agent purposefully executes immediate consumption $\alpha_{\mathrm{near}}$ at $(i,t,h)$ under a causal doxastic open horizon, at least one feasible deferral moment $\tau_2$ is not strictly preferred to near consumption:

$$
\exists \tau_2 \in \mathcal{T}, \quad \tau_1 \prec \tau_2 \land \neg(T(e,\tau_2) \succ_{i,t,h} T(e,\tau_1)).
$$

**Proof.** By the open horizon, feasibility of $\alpha_{\mathrm{near}}$ yields a feasible deferral $\alpha_{\mathrm{defer}}$ targeting $\tau_2$ with $\tau_1 \prec \tau_2$. Because $\alpha_{\mathrm{near}}$ is purposeful, it is undominated against all feasible alternatives, including $\alpha_{\mathrm{defer}}$. Thus $\neg(T(e,\tau_2) \succ_{i,t,h} T(e,\tau_1))$. $\square$

---

## Positive Time Preference and Originary Interest

The previous result leaves open whether immediate consumption is strictly preferred: the two timed ends could be incomparable. We now add local comparability. Under that stronger condition, undominated immediate consumption rules out the reverse ranking and yields a strict comparison.

### Definition 7.6 (Direction-Symmetric Local Menu Comparability)
An action $\alpha^{\ast}$ satisfies *local menu comparability* on $`\mathcal{A}_{\mathrm{feas}}(i, t, h)`$ if it is comparable with every feasible alternative that yields a distinct end:

$$
\forall \beta \in \mathcal{A}_{\mathrm{feas}}(i, t, h), \quad \mathcal{O}(\beta) \neq \mathcal{O}(\alpha^{\ast}) \implies (\mathcal{O}(\alpha^{\ast}) \succ \mathcal{O}(\beta) \lor \mathcal{O}(\beta) \succ \mathcal{O}(\alpha^{\ast})).
$$

### Proposition 7.7 (Comparability Turns Undominatedness into Strict Dominance)
An action is active and purposeful and its end is comparable with the end of every feasible action having a different end if and only if it satisfies the distinct-end dominance condition:

$$
\text{ActivePurposefulChoice}(i, t, h, \alpha^{\ast}) \land \text{MenuComparable}(i, t, h, \alpha^{\ast}) \iff \text{DistinctEndDominantAct}(i, t, h, \alpha^{\ast}).
$$

**Proof.**
- ($\implies$): If $\alpha^{\ast}$ is active purposeful and menu comparable, for any $\beta$ yielding a distinct end, menu comparability gives $\mathcal{O}(\alpha^{\ast}) \succ \mathcal{O}(\beta) \lor \mathcal{O}(\beta) \succ \mathcal{O}(\alpha^{\ast})$. But the second disjunct contradicts the undominatedness clause of purposeful action. Thus $\mathcal{O}(\alpha^{\ast}) \succ \mathcal{O}(\beta)$ holds.
- ($\impliedby$): If $\alpha^{\ast}$ is distinct-end dominant, undominatedness holds because any $\beta$ with $\mathcal{O}(\beta) = \mathcal{O}(\alpha^{\ast})$ satisfies $\neg(\mathcal{O}(\beta) \succ \mathcal{O}(\alpha^{\ast}))$ by irreflexivity, while any $\beta$ with a distinct end satisfies $\mathcal{O}(\alpha^{\ast}) \succ \mathcal{O}(\beta)$, which by asymmetry precludes $\mathcal{O}(\beta) \succ \mathcal{O}(\alpha^{\ast})$. Menu comparability is immediate from the strict comparison. $\square$

### Proposition 7.8 (Comparable Immediate Choice Reveals Strict Time Preference)
Let an agent execute a distinct-end dominant action to consume $\alpha_{\mathrm{near}}$ at $(i,t,h)$ under a causal doxastic open horizon, where temporal end indexing is injective: $\tau_1 \neq \tau_2 \implies T(e,\tau_1) \neq T(e,\tau_2)$. Then the agent strictly demonstrates positive time preference:

$$
\exists \tau_2 \in \mathcal{T}, \quad \tau_1 \prec \tau_2 \land T(e,\tau_1) \succ_{i,t,h} T(e,\tau_2).
$$

**Proof.** Under the open horizon, there exists a feasible deferral action $\alpha_{\mathrm{defer}}$ yielding $T(e,\tau_2)$ with $\tau_1 \prec \tau_2$. By strict irreflexivity of temporal precedence, $\tau_1 \neq \tau_2$. Injectivity gives $T(e,\tau_1) \neq T(e,\tau_2)$. Thus $\alpha_{\mathrm{defer}}$ yields an end distinct from $\alpha_{\mathrm{near}}$. By distinct-end dominance ([Proposition 7.7](#proposition-77-comparability-turns-undominatedness-into-strict-dominance)), $\alpha_{\mathrm{near}}$ strictly dominates $\alpha_{\mathrm{defer}}$, establishing $T(e,\tau_1) \succ_{i,t,h} T(e,\tau_2)$. Earlier satisfaction is strictly preferred to later satisfaction. $\square$

### Definition 7.9 (Timed Quantity Bundles)
For a commodity $m \in \mathcal{M}$ and discrete quantity $q \in \mathbb{N}$, the untimed quantity end is $Q(m, q) \in \mathcal{E}$. The timed quantity bundle:

$$
\langle m, q, \tau \rangle \equiv T(Q(m, q), \tau) \in \mathcal{E}
$$

represents the consumption or possession of $q$ discrete units of means $m$ at moment $\tau$.

### Theorem 7.10 (The Universal Positive Time Preference Theorem)
When an agent enacts immediate consumption of bundle $\langle m, q, \tau_1 \rangle$ under distinct-end dominance and an open horizon, there exists a later moment $\tau_2$ with $\tau_1 \prec \tau_2$ such that the agent strictly prefers immediate consumption to unit-for-unit deferral:

$$
\langle m, q, \tau_1 \rangle \succ_{i,t,h} \langle m, q, \tau_2 \rangle.
$$

Consequently, when positive time preference holds and present consumption remains feasible, an agent cannot purposefully choose a unit-for-unit loan that yields the same quantity only at the later date:

$$
\neg \mathsf{P}(i, t, h, \alpha_{\mathrm{u4u}}).
$$

**Proof.** The strict comparison follows directly by instantiating [Proposition 7.8](#proposition-78-comparable-immediate-choice-reveals-strict-time-preference) with $e = Q(m, q)$. If present consumption $\alpha_{\mathrm{pres}}$ is feasible and yields $\langle m, q, \tau_1 \rangle$, any unit-for-unit deferral $\alpha_{\mathrm{u4u}}$ yielding $\langle m, q, \tau_2 \rangle$ is strictly dominated by $\alpha_{\mathrm{pres}}$, violating the undominatedness condition of $\mathsf{P}$. $\square$

### Proposition 7.11 (Voluntary Intertemporal Exchange Requires Greater Future Return)
Suppose the agent strictly prefers present delivery of $q$ units to the same quantity at a later date, where $q>0$, and strictly prefers a future delivery of $q'$ units to retaining the present $q$ units. Assume preference is transitive. Also assume that if $q'\le q$, then at the later date either the $q$-unit timed end is strictly preferred to the $q'$-unit timed end or the two timed ends are equal. Then:
1. The future quantity must strictly exceed the present quantity:

$$
q < q'.
$$

2. There exists a strictly positive discrete premium $\delta \ge 1$ such that:

$$
q' = q + \delta.
$$

Here the weak comparison in the premise means exactly "strictly preferred, or equal." The discrete premium $\delta$ is positive. If we describe it as a ratio to the principal, $q>0$ ensures $\iota=\delta/q>0$. This conclusion is conditional on the comparison and monotonicity assumptions above.

**Proof.**
Suppose by contradiction that $q' \le q$.
1. By quantity monotonicity at moment $\tau_2$, either $\langle m, q, \tau_2 \rangle \succ \langle m, q', \tau_2 \rangle$ or $\langle m, q, \tau_2 \rangle = \langle m, q', \tau_2 \rangle$.
2. The agent voluntarily accepts future delivery over present retention: $\langle m, q', \tau_2 \rangle \succ \langle m, q, \tau_1 \rangle$.
3. If $\langle m, q, \tau_2 \rangle = \langle m, q', \tau_2 \rangle$, substitution yields $\langle m, q, \tau_2 \rangle \succ \langle m, q, \tau_1 \rangle$, which directly contradicts positive time preference ($\langle m, q, \tau_1 \rangle \succ \langle m, q, \tau_2 \rangle$) by asymmetry.
4. If $\langle m, q, \tau_2 \rangle \succ \langle m, q', \tau_2 \rangle$, transitivity with step 2 yields $\langle m, q, \tau_2 \rangle \succ \langle m, q, \tau_1 \rangle$, again contradicting asymmetry.

Therefore, $q < q'$. In discrete natural numbers, $q < q'$ implies $q + 1 \le q'$, so $\delta = q' - q \ge 1$. $\square$

### Proposition 7.12 (Time Preference and Physical Return Comparison)
Suppose an agent purposefully chooses immediate consumption, an open horizon supplies a feasible deferral, timed ends at different dates are distinct, and the chosen action strictly dominates every feasible rival with a different end. [Proposition 7.8](#proposition-78-comparable-immediate-choice-reveals-strict-time-preference) then gives a strict preference for present delivery over later delivery of the same quantity.

Now suppose the agent also strictly prefers a future delivery of $q'$ units to retaining $q$ units at the earlier date. If preference is transitive and a future quantity no larger than $q$ is either strictly worse than $q$ units at the same later date or equal to them, [Proposition 7.11](#proposition-711-voluntary-intertemporal-exchange-requires-greater-future-return) gives $q'=q+\delta$ for some $\delta\ge1$.

The first comparison depends on execution, feasibility, deferral, and distinctness of timed ends. The positive quantity premium $\delta \ge 1$ is derived systematically from explicit intertemporal execution, feasibility, transitivity, and ordinal quantity comparisons.

**Proof.** By [Proposition 7.8](#proposition-78-comparable-immediate-choice-reveals-strict-time-preference), the purposeful immediate choice and feasible deferral imply that the present timed end is strictly preferred to the same quantity at the later date. The additional future-versus-present quantity comparison, transitivity, and weak ordering of quantities at the later date are the premises of [Proposition 7.11](#proposition-711-voluntary-intertemporal-exchange-requires-greater-future-return). That theorem gives $q < q'$. Since both are natural numbers, set $\delta=q'-q$; then $\delta\ge1$ and $q'=q+\delta$. $\square$

---

## Böhm-Bawerk: Roundabout Production and Capital

We next compare two methods that deliver the same good at different times. The conclusion that the later method yields more follows only when the agent prefers the earlier delivery of a fixed quantity, quantities are comparable at the later date, and the chosen later method is purposeful. A separate stock example shows how prior production can make a previously infeasible method feasible.

### Proposition 7.13 (Roundabout Production Superiority under Positive Interest)
Suppose a feasible direct method yields $q_{\text{direct}}>0$ units of a product at $\tau_{\text{early}}$, while a purposeful roundabout method yields $q_{\text{round}}$ units at $\tau_{\text{late}}$, with $\tau_{\text{early}}\prec\tau_{\text{late}}$. Assume the agent prefers $q_{\text{direct}}$ units at the earlier date to the same quantity at the later date. Assume preference is transitive and that, at the later date, if one quantity is no greater than another, the larger quantity is either strictly preferred or yields the same timed end. Then:

$$
q_{\text{direct}} < q_{\text{round}}.
$$

Under these assumptions, the purposeful later method must yield a strictly larger quantity.

**Proof.**
Suppose by contradiction that $q_{\text{round}} \le q_{\text{direct}}$.
1. The later-date quantity condition says either that $q_{\text{direct}}$ at $\tau_{\text{late}}$ is strictly preferred to $q_{\text{round}}$ there, or that the two timed ends are equal.
2. The assumed time comparison says that $q_{\text{direct}}$ at $\tau_{\text{early}}$ is strictly preferred to $q_{\text{direct}}$ at $\tau_{\text{late}}$.
3. In the strict case, transitivity makes the direct method's end strictly preferred to the roundabout method's end. In the equality case, substituting equal timed ends gives the same strict comparison.
4. But this strictly dominates $\alpha_{\text{round}}$, directly violating the undominatedness condition of $\mathsf{P}(\alpha_{\text{round}})$.

This contradicts the purposeful roundabout method's undominatedness, since the direct method is feasible. Hence $q_{\text{direct}} < q_{\text{round}}$. Under the stated assumptions, the later method must yield a physical surplus. $\square$

### Proposition 7.14 (A Larger Stock Can Add a Feasible Action)
Suppose an action requires more of a capital good than is available at $t_0$, but no more than is available at $t_1$, where $t_0\prec t_1$:

$$
u(\alpha_{\mathrm{advanced}},m_{\mathrm{cap}})>\omega(i,t_0,h,m_{\mathrm{cap}})
\quad\text{and}\quad
u(\alpha_{\mathrm{advanced}},m_{\mathrm{cap}})\le\omega(i,t_1,h,m_{\mathrm{cap}}).
$$

Then $\alpha_{\mathrm{advanced}}$ is infeasible at $t_0$ and feasible at $t_1$. Thus the feasible menu at $t_1$ contains at least one action absent from the menu at $t_0$. A full inclusion between the two menus requires the additional assumption that no other relevant feasibility condition changes adversely.

**Proof.** The action's requirement exceeds the stock at $t_0$, so it is infeasible there. At $t_1$ the requirement is no greater than the stock, so it is feasible. Hence it belongs to the later menu and not to the earlier one. $\square$

---

## Saving and Comparisons between Different Ends

A preference for an end sooner rather than later compares two timed instances of the same end. A saving decision can instead compare different ends: present feasting versus future survival, or immediate spending versus present security. A ranking across dates for each fixed end therefore does not by itself determine how an agent allocates a limited stock among unlike ends. 

### Theorem 7.15 (The Precautionary Saving and Present Security Theorem)
Let an acting agent face a three-action feasible choice menu at moment $t$ on history $h$:

$$
\mathcal{A}_{\mathrm{feas}}(i, t, h) = \{\alpha_0, \alpha_{\mathrm{spend}}, \alpha_{\mathrm{save}}\}
$$

where $\alpha_0$, $\alpha_{\mathrm{spend}}$, and $\alpha_{\mathrm{save}}$ are pairwise distinct.

Suppose:
1. The saving action $\alpha_{\mathrm{save}}$ yields a current security end $e_{\mathrm{sec}}$ that matures at the immediate successor moment, and the agent strictly prefers this security end to the end of immediate spending $e_{\mathrm{spend}}$ and to inaction:

$$
e_{\mathrm{sec}} \succ_{i,t,h} e_{\mathrm{spend}} \quad \wedge \quad e_{\mathrm{sec}} \succ_{i,t,h} \mathsf{End}(i, t, h, \alpha_0)
$$

2. The saving action is physically executed on history $h$.

Then:
1. The saving action is undominated on the feasible menu and constitutes a purposeful human act: $\mathsf{P}(i, t, h, \alpha_{\mathrm{save}})$.
2. Saving strictly dominates immediate spending in the actor's present preference ranking:

$$
\mathsf{End}(i, t, h, \alpha_{\mathrm{save}}) \succ_{i,t,h} \mathsf{End}(i, t, h, \alpha_{\mathrm{spend}})
$$

*Saving and provision for the future do not demonstrate negative time preference; they demonstrate a purposeful present choice for security over immediate consumption.*

**Proof.** Preference asymmetry and irreflexivity ensure that strict preference $e_{\mathrm{sec}} \succ e_{\mathrm{spend}}$ and $e_{\mathrm{sec}} \succ \mathsf{End}(\alpha_0)$ rule out any weak dominance of $\alpha_{\mathrm{save}}$ by $\alpha_{\mathrm{spend}}$ or $\alpha_0$ on the three-action menu. Together with physical execution, undominatedness establishes that saving is a purposeful act. In turn, the explicit ranking $e_{\mathrm{sec}} \succ e_{\mathrm{spend}}$ establishes that saving strictly dominates immediate spending in the actor's present evaluation. $\square$

### Theorem 7.16 (The Master Positive Time Preference and Originary Interest Synthesis)
Under the combined structural evidence of positive time preference, current security choice, and discrete originary interest:
1. **Universal Dated Preference**: For any fixed end $e$ and any precedence pair $t_1 \prec t_2$ along history $h$, earlier attainment is strictly preferred to later attainment:

$$
\langle e, t_1 \rangle \succ_{i,t,h} \langle e, t_2 \rangle
$$

2. **Teleological Saving Resolution**: Purposeful saving strictly dominates immediate spending in present evaluation:

$$
\mathsf{End}(i, t, h, \alpha_{\mathrm{save}}) \succ_{i,t,h} \mathsf{End}(i, t, h, \alpha_{\mathrm{spend}})
$$

3. **Control Dominance and Positive Originary Interest**: Present control strictly dominates unit-for-unit deferred lending, and the gross interest premium $\delta$ is strictly positive:

$$
\delta \ge 1 \quad \wedge \quad \mathsf{End}(i, t, h, \alpha_{\mathrm{retain}}) \succ_{i,t,h} \mathsf{End}(i, t, h, \alpha_{\mathrm{u4u}})
$$

**Proof.** Direct composition of earlier control dominance, security evaluation, and positive originary interest. The three parts resolve the classical tension between positive time preference, saving/insurance, and positive interest in a single coherent framework. $\square$

---

## Finite Examples for the Intertemporal Results

The final constructions verify that the intertemporal assumptions used above have nonempty models. They separate logical consistency from the empirical question of whether a particular technology or preference ordering occurs.

### Witness 7.17 (Quantity-Monotone Time-Preference Model Witness)
There is a finite model with three means and four moments in which, for every mean $m$, moment $\tau$, and natural-number quantities $q'<q$, the larger timed quantity end is strictly preferred at that same moment.

$$
q' < q \implies T(Q(m,q),\tau)\succ_{i,t,h}T(Q(m,q'),\tau).
$$

**Proof.** Label the three means by a bijection $`\nu:\mathcal{M}\to\{0,1,2\}`$, and call the first moment $\tau_0$. Give $T(Q(m,q),\tau)$ rank $100q+\nu(m)+2$ when $\tau=\tau_0$, and rank $100q+\nu(m)$ at each other moment. Define strict preference by larger rank. For a fixed mean and moment, increasing $q$ by at least one raises the rank by at least $100$, so $q'<q$ gives the required comparison. $\square$

### Witness 7.18 (Originary Interest Action Frame Witness)
There is a finite model with two agents, four moments, three histories, and three means in which the interest argument's premises hold together. Three histories share the initial moment and continue to distinct later moments. For one agent, the feasible menu at the initial moment contains inaction, immediate consumption of one unit, and deferral of that unit to the next moment. The agent enacts immediate consumption. The end ranking makes immediate consumption preferable both to inaction and to deferral; it ranks a future delivery of two units above present retention of one unit. Timed ends at different dates are distinct, preferences are transitive, and a larger quantity at the same date is preferred.

**Verification.** Assign each timed quantity end the ordinal rank from [Witness 7.17](#witness-717-quantity-monotone-time-preference-model-witness). A one-unit immediate-consumption action ranks above both inaction and one-unit deferral, and it is not dominated in the three-action menu; hence its enactment is purposeful. The same rank rule gives strict preference for two units at the later date over one unit at the earlier date. The two dates are distinct, while the ranking is transitive and strictly increasing in quantity at each fixed date. Taking $q=1$ and $q'=2$ yields $\delta=1$. The four-moment, three-history tree supplies the initial choice and later date. These assignments constructively verify the joint mathematical consistency of the intertemporal interest conditions. $\square$

## Conclusion

We have related present and future ends through temporal preference, then used explicit feasibility and choice assumptions to analyze saving, lending, and the premium attached to repayment at a later date. Those results concern individual plans and specified exchanges. We now bring several agents together to study property, bargaining, and the physical terms of social exchange.

---
