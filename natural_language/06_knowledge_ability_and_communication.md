# Chapter 6: Knowledge, Ability, and Communication

We begin with three questions that must not be conflated. Does some action guarantee a target result here? Does the agent know that such an action is available? Can one and the same action guarantee it throughout the situations the agent cannot distinguish? The last condition defines know-how. We then use these distinctions to examine belief and assertion.

## Ability and Know-How

Let $W$ be an action frame. A decision index $x \in W.\text{DecisionIndex}$ is a pair $x = \langle t, h \rangle$ consisting of a moment $t$ and a history $h$ passing through $t$ ($t \in h$). At each decision index $x$, an agent $i$ has a set $`\mathcal{A}_{\mathrm{feas}}(i, x.\text{moment}, x.\text{history})`$ of available actions. An action choice determines a choice cell of decision indices sharing the same moment $x.\text{moment}$ where the agent enacts that action. We write $P : W.\text{DecisionIndex} \to \text{Prop}$ for the target proposition the agent seeks to guarantee.

### Definition 6.1 (Guarantee and Causal Ability)
Action $\alpha$ *guarantees* $P$ for agent $i$ at decision index $x$ when it is feasible there and every decision index $y$ sharing moment $x.\text{moment}$ where $i$ enacts $\alpha$ satisfies $P(y)$:

$$
\text{Guarantees}_i(x, \alpha, P) \iff \alpha \in \mathcal{A}_{\mathrm{feas}}(i, x.\text{moment}, x.\text{history}) \land \forall y \in W.\text{DecisionIndex},\; (y.\text{moment} = x.\text{moment} \land \text{enacted}(i, y.\text{moment}, y.\text{history}) = \alpha \implies P(y)).
$$

The agent has *causal ability* to bring about $P$ at $x$ when at least one action guarantees it:

$$
\text{CausalAbility}_i(x, P) \iff \exists \alpha,\; \text{Guarantees}_i(x, \alpha, P).
$$

### Definition 6.2 (Knowledge and Know-How)
Let $K$ be a knowledge relation on decision indices, where $x \sim_i y$ denotes that agent $i$ cannot distinguish decision index $x$ from $y$. The relation $\sim_i$ is an equivalence relation (reflexive, symmetric, and transitive). The agent *knows* $P$ at $x$ when $P$ holds at every indistinguishable index:

$$
\text{Knows}(K, i, x, P) \iff \forall y,\; (x \sim_i y \implies P(y)).
$$

The agent *knows how* to bring about $P$ at $x$ when one and the same action guarantees $P$ at every index indistinguishable from $x$:

$$
\text{KnowHow}(K, i, x, P) \iff \exists \alpha,\; \forall y,\; (x \sim_i y \implies \text{Guarantees}_i(y, \alpha, P)).
$$

The order of the quantifiers is the whole distinction. At each indistinguishable index, some successful action may exist; know-how requires a single action that works at all of them.

### Proposition 6.3 (Know-How Implies Ability and Knowledge of Ability)
If $\text{KnowHow}(K, i, x, P)$, then the agent has causal ability at $x$ and knows that causal ability is available:

$$
\text{KnowHow}(K, i, x, P) \implies \text{CausalAbility}_i(x, P) \land \text{Knows}\bigl(K, i, x, \lambda y.\, \text{CausalAbility}_i(y, P)\bigr).
$$

**Proof.** Choose the action $\alpha$ witnessing know-how. Since $\sim_i$ is reflexive, $x \sim_i x$, so $\alpha$ guarantees $P$ at $x$, which establishes causal ability at $x$. For any $y$ with $x \sim_i y$, the same action $\alpha$ guarantees $P$ at $y$, which entails causal ability at $y$. Thus causal ability holds at every indistinguishable index, establishing knowledge of causal ability. These are precisely the two conclusions. $\square$

### Proposition 6.4 (Ability Need Not Give Know-How)
There exist indistinguishable decision states $x_1 \sim_i x_2$ where action $\alpha_1$ guarantees $P$ at $x_1$ while failing at $x_2$, and action $\alpha_2$ guarantees $P$ at $x_2$ while failing at $x_1$. In this configuration, causal ability holds at each individual state, yet know-how fails across the epistemic information set.

*Example.* Consider two indistinguishable decision indices $x_1 \sim_i x_2$ and two available actions $\alpha_1, \alpha_2$. Suppose that enacting $\alpha_1$ at $x_1$ produces an outcome in $P$, whereas enacting $\alpha_1$ at $x_2$ branches to an index outside $P$. Conversely, suppose enacting $\alpha_2$ at $x_2$ produces an outcome in $P$, but enacting $\alpha_2$ at $x_1$ branches outside $P$. At $x_1$, $\alpha_1$ guarantees $P$; at $x_2$, $\alpha_2$ guarantees $P$. Therefore, causal ability holds at both indistinguishable indices, and the agent knows that causal ability is available:

$$
\forall y \in \{x_1, x_2\},\; \exists \alpha,\; \text{Guarantees}_i(y, \alpha, P).
$$

However, because $\alpha_1$ fails at $x_2$ and $\alpha_2$ fails at $x_1$, no single action $\alpha$ satisfies $`\forall y \in \{x_1, x_2\},\; \text{Guarantees}_i(y, \alpha, P)`$. In logical form, $`\forall y\,\exists \alpha`$ does not imply $`\exists \alpha\,\forall y`$.

**Verification.** The two guarantees establish ability separately at $x_1$ and $x_2$. Because $x_1 \sim_i x_2$, know-how requires one available action to guarantee $P$ at both. Action $\alpha_1$ fails at $x_2$, and $\alpha_2$ fails at $x_1$, so neither witnesses that uniform condition.

An action's guarantee requires uniform success across the entire choice cell, rigorously formalizing the distinction between incidental success on an isolated branch and robust epistemic know-how.

## Belief, Introspection, and Veridicality

Knowledge concerns every index an agent cannot distinguish from the present one. Because indistinguishability is reflexive, knowledge of $P$ implies that $P$ holds here. Belief uses a set of minimally plausible histories instead; that set may fail to include the actual history.

### Definition 6.5 (Internal Doxastic Coherence)
At a moment $t$ and actual history $h$, write $B_i(t,h)$ for agent $i$'s nonempty set of plausible histories. The agent's deliberative state is *internally coherent* when every $h' \in B_i(t,h)$ passes through $t$ and the following data agree between $h'$ and $h$:

1. the action enacted by $i$ at $t$;
2. the feasible action menu of $i$ at $t$;
3. the preference relation of $i$ at that decision context; and
4. the agent's plausible-history set, so $B_i(t,h') = B_i(t,h)$.

These coherence requirements do not force the actual history into the belief set. We call belief veridical when the actual history is included; nonemptiness alone does not give veridicality.

### Example 6.6 (Nonveridical but Internally Coherent Belief)
Let the histories be $h_0, h_1$ and moments be $t_0, t_1$, with the relevant decision at $t_0$. At the actual history $h_0$, let $`B_i(t_0,h_0) = \{h_1\}`$, and at $h_1$ let the same singleton remain the belief set. Give the agent the same enacted action, feasible menu, and preference relation at both histories. Then belief is nonempty and the listed deliberative facts are internally coherent, although $h_0$ is not believed possible.

This witness formally verifies that subjective internal coherence and objective veridicality are logically distinct praxeological concepts.

## Assertion as an Action

An assertion is both an enacted action and an action with propositional content. We first separate utterance from content, then state the additional conditions under which the utterance is treated as truth-directed.

### Definition 6.7 (Utterance and Assertion)
Let a proposition be a subset $P \subseteq \mathcal{H}$ of histories. Agent $i$ utters action $\alpha$ at $(t,h)$ when it is feasible and enacted there. If the action's content is $P$, it is an assertion of $P$:

$$
\begin{aligned}
\text{Utters}(i,t,h,\alpha) &\iff \alpha \in \mathcal{A}_{\mathrm{feas}}(i,t,h) \land \text{enacted}(i,t,h) = \alpha,\\
\text{Asserts}(i,t,h,P,\alpha) &\iff \text{Utters}(i,t,h,\alpha) \land \text{content}(\alpha) = P.
\end{aligned}
$$

### Definition 6.8 (Truth-Directed Epistemic Assertion)
We call an assertion epistemic in this model when it satisfies four conditions:

1. It is an enacted, feasible assertion action distinct from inaction.
2. For each listener, the update retains the listener's previously minimal histories that satisfy $P$:

$$
B_j^{+}(t) = \{h' \in B_j(t) : h' \in P\}.
$$

3. At every history through $t$ where $P$ is false, the speaker refrains from asserting $P$ (enacting inaction).
4. At least one history through $t$ makes $P$ false.

The update is intersection with $P$. If none of the previously plausible histories satisfies $P$, the result is empty; this definition does not add a nonemptiness condition after updating.

### Definition 6.9 (Relation Generated by an Action Comparison)
Suppose the asserted action $\alpha$ and inaction $\alpha_0$ have distinct outcomes. Define $R_{\mathrm{ind}}$ to contain exactly the ordered pair formed by these two outcomes:

$$
R_{\mathrm{ind}}(e_1, e_2) \iff e_1 = \mathcal{O}(i, \alpha, t, h) \land e_2 = \mathcal{O}(i, \alpha_0, t, h) \land e_1 \ne e_2.
$$

This construction isolates the exact pairwise comparison between the asserted outcome and inaction, establishing local preference without requiring a total ordering over unranked ends.

### Proposition 6.10 (Properties of the Generated Relation)
If $\mathcal{O}(i, \alpha, t, h) \ne \mathcal{O}(i, \alpha_0, t, h)$, then $R_{\mathrm{ind}}$ is asymmetric, it ranks the outcome of $\alpha$ above that of inaction, and no feasible alternative's outcome is ranked above the outcome of $\alpha$ by this relation.

**Proof.** The relation contains only the ordered pair $(\mathcal{O}(\alpha), \mathcal{O}(\alpha_0))$. Reversing the pair would require the two distinct outcomes to be equal, so the relation is asymmetric. The specified pair gives the comparison with inaction. For a feasible $\beta$ to be ranked above $\mathcal{O}(\alpha)$, the relation's definition would require $\mathcal{O}(\alpha) = \mathcal{O}(\alpha_0)$, contrary to the hypothesis. $\square$

### Corollary 6.11 (Purposeful Choice Relative to the Generated Relation)
If $\alpha$ is feasible and enacted, differs from inaction, and has an outcome distinct from inaction's outcome, then it satisfies the purposeful-choice conditions when those conditions are evaluated using $R_{\mathrm{ind}}$.

**Proof.** [Proposition 6.10](#proposition-610-properties-of-the-generated-relation) gives the strict comparison from the action's outcome to inaction's outcome and shows that no feasible alternative is ranked above the action by $R_{\mathrm{ind}}$. Feasibility and enactment are premises. Since the action differs from inaction, these are exactly the improvement and undominatedness conditions for purposeful choice. $\square$

The conclusion is limited to the relation just constructed. We show that the action meets the purposeful-choice clauses relative to this single comparison; we do not recover a separate, independently given preference relation.

### Proposition 6.12 (Conditional Inconsistency of a Universal Denial)
Let $D(h)$ state that no agent at any moment acts purposefully under any binary relation on ends. If an assertion of $D$ is itself feasible, enacted, and has an outcome distinct from inaction's outcome, then $D$ is false at the history of assertion.

**Proof.** By [Corollary 6.11](#corollary-611-purposeful-choice-relative-to-the-generated-relation), the assertion action is purposeful relative to the relation generated by its outcome comparison. The universal quantifiers in $D$ include this agent, moment, action, and relation. Thus $D$ denies a particular instance that holds, so $D$ is false. $\square$

This conclusion depends on the stated properties of the particular assertion. We have not shown that every utterance of the denial is feasible, enacted, or distinct in outcome from inaction.

### Proposition 6.13 (Conditional Doxastic Inconsistency)
Suppose the belief set at a decision node is nonempty. Assume (i) the speaker's purposeful action holds at the actual history and transfers to every believed history by internal coherence, and (ii) the speaker believes that purposeful action fails at every believed history. These assumptions are inconsistent.

**Proof.** Choose a history from the nonempty belief set. By (i), purposeful action holds there. By (ii), it fails there. A proposition and its negation cannot both hold at the same history. $\square$

The actual history need not itself be believed possible. The contradiction uses only nonemptiness, transfer of the deliberative facts, and the stipulated denial on believed histories. This separates the argument from any assumption that belief is factive.

## Conclusion

We have distinguished belief about histories from knowledge, reliable ability, and knowledge-how, then considered how assertions can be assessed against the action structure that gives them meaning. These notions clarify what agents can infer and perform, but they do not yet compare otherwise similar ends at different dates. We now introduce temporal preference and use it to study saving, lending, and capital formation.
