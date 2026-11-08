# Chapter 8: Social Interaction, Property, and Exchange

We now extend individual choice to situations in which several agents act on one history. We first specify how their choices fit together, then distinguish voluntary exchange from defensive response and physical coercion. Finally, we connect matched transfers to each participant's own preference and to a finite specialization example.

> *Prerequisites and scope:* Chapters 1–5. We add joint action, bilateral comparisons, matched transfers, and a two-good specialization model.

Several agents may face the same physical history while holding different stocks and ranking ends differently. To reason about exchange, praxeological analysis strictly preserves distinct individual comparisons, avoiding the methodological fallacy of aggregating separate valuations into a single social ranking. We therefore define joint realization first, then identify which baseline each claim of gain uses.

## Distinct Agents and Joint Action

We now let several agents occupy the same history. Each agent has an individual stock and feasible menu, while a joint action profile records what all of them do at one moment. This distinction is needed before we can say that a proposed offer and acceptance occur together.

### Definition 8.1 (Plurality of Agents)
A frame contains a plurality of agents if there exist $i, j \in \mathcal{I}$ such that $i \neq j$. Throughout the bilateral analysis, fix such a pair and a decision node $\langle t, h\rangle$ with $t \in h$.

Each agent retains the individual structures established in earlier chapters: an endowment $\omega(i, t, h, \cdot)$, a feasible menu $`\mathcal{A}_{\text{feas}}(i, t, h)`$, an ordinal preference $`\succ_{i, t, h}`$, and an enacted action. The physical history is common to the agents; their endowments, evaluations, and beliefs remain indexed by the individual.

Once we fix the agent pair and decision situation, we shorten the notation to $\omega_i(m)$ and $\succ_i$.

We can now separate each person's stock from the total stock held by the pair. This matters because a combined quantity does not tell us which agent can use a good under their own feasibility constraint.

### Definition 8.2 (Distribution of Means)
The pair $(\omega_i, \omega_j)$ describes the distribution of physical means between the two agents. Its combined stock of commodity $m$ is

$$
\Omega_{ij}(m) = \omega_i(m) + \omega_j(m)
$$

A combined stock does not determine its distribution. One unit held by $i$ and one unit held by $j$ give the same combined quantity, but they enter different agents' feasibility constraints. A unit held by one agent does not become available to the other unless an action transfers it.

With individual stocks in view, we can record the agents' actions together. A profile describes their separate choices; a history realizes the profile only when all those choices occur on that history.

### Definition 8.3 (Joint Action Profile)
A joint action profile at $t$ is a function $s : \mathcal{I} \to \mathcal{A}$ assigning an action to each agent. It is realized on a history $h' \in H(t)$ when

$$
\forall k \in \mathcal{I}, \quad \text{enacted}(k, t, h') = s(k)
$$

Individual feasibility and joint realization express different requirements. The former concerns an action available to one agent; the latter concerns a history on which the actions of all agents occur together.

To ensure that simultaneous decentralized choices are physically and strategically coherent, [Definition 8.4](#definition-84-independence-of-agency) introduces the independence of agency condition: whenever each individual action in a profile is individually feasible, there exists a history jointly realizing the complete profile.

### Definition 8.4 (Independence of Agency)
At a moment $t$, independence of agency means that every profile whose components are feasible on every history through $t$ has a joint realization:

$$
\begin{aligned}
\forall s : \mathcal{I} \to \mathcal{A}, \quad
& \left( \forall i \in \mathcal{I}, \forall h \in H(t), \quad s(i) \in \mathcal{A}_{\text{feas}}(i, t, h) \right) \\
& \implies \exists h' \in H(t), \quad \forall i \in \mathcal{I}, \quad \text{enacted}(i, t, h') = s(i)
\end{aligned}
$$

The condition concerns joint realizability of choices, not independence of their consequences. An offer and a refusal may occur together on one history; the offer does not thereby produce a transfer.

For example, a person may offer grain while another declines to accept. Their choices can be jointly realized even though the proposed exchange does not occur. Freedom to select an offer and success in concluding an exchange are distinct facts.

Joint realization tells us which profiles can occur. To compare one agent's alternatives while holding the other's present choice fixed, we also need a branch-selection rule. Chapter 2 introduced such a rule; its co-agency condition now lets us use it for bilateral comparisons.

### Proposition 8.5 (A Unilateral Counterfactual Preserves the Other Agent's Present Choice)
Let $i \neq j$, and let $\alpha$ be feasible for $i$ at $\langle t, h\rangle$. For every $h' \in H(t)$, the selected history $\sigma(i, t, \alpha, h')$ realizes $\alpha$ while preserving $j$'s enacted action at $t$:

$$
\begin{aligned}
\text{enacted}(i,t,\sigma(i,t,\alpha,h')) &= \alpha, \\
\text{enacted}(j,t,\sigma(i,t,\alpha,h')) &= \text{enacted}(j,t,h').
\end{aligned}
$$

**Proof.** The branch-selection condition gives the first equality. Its co-agency clause gives the second because $i$ and $j$ are distinct. $\blacksquare$

This proposition identifies the comparison needed for individual deliberation within a social setting: vary the actor's present choice while holding another actor's present choice fixed. It does not fix the other actor's entire future conduct. Nor does it replace both actors' choices by their passive alternatives. That latter comparison requires a separate baseline.

---

## Baselines and Bilateral Exchange

We now need to decide what “gain” means in an interaction. Refraining while the other agent continues acting is a different comparison from both agents refraining. We derive both baselines directly from the frame's counterfactual branch selector $\sigma$, demonstrating how purposeful choice naturally supplies a conditional response grounded in physical execution.

### Definition 8.6 (Joint Counterfactual Branches and Bilateral Outcomes)
For distinct agents $i \neq j$ at decision node $\langle t, h\rangle$ with feasible actions $`\alpha_i \in \mathcal{A}_{\text{feas}}(i, t, h)`$ and $`\alpha_j \in \mathcal{A}_{\text{feas}}(j, t, h)`$, the joint counterfactual branch $h(\alpha_i, \alpha_j)$ is the history obtained by sequential branch selection:

$$
h(\alpha_i, \alpha_j) \equiv \sigma(j, t, \alpha_j, \sigma(i, t, \alpha_i, h))
$$

By [Proposition 8.5](#proposition-85-a-unilateral-counterfactual-preserves-the-other-agents-present-choice) (co-agency), $h(\alpha_i, \alpha_j)$ passes through $t$ and realizes both choices together:

$$
\text{enacted}(i, t, h(\alpha_i, \alpha_j)) = \alpha_i, \quad \text{enacted}(j, t, h(\alpha_i, \alpha_j)) = \alpha_j
$$

While each agent's single-node intended end at $t$ is bundle-invariant across $H(t)$, bilateral interactions materialize their physical and contractual consequences across an interaction maturation interval $t \to t'$ ($t \prec t'$). The resulting bilateral interaction ends for $i$ and $j$ at maturation moment $t'$ are denoted:

$$
O_i(\alpha_i, \alpha_j) \equiv \text{OutcomeOf}(i, \alpha_i, t, t', h(\alpha_i, \alpha_j)), \quad O_j(\alpha_i, \alpha_j) \equiv \text{OutcomeOf}(j, \alpha_j, t, t', h(\alpha_i, \alpha_j))
$$

evaluated by each agent's ordinal preference relations $`\succ_{i,t,h}`$ and $`\succ_{j,t,h}`$ on their respective end spaces $`\mathcal{E}_i`$, $`\mathcal{E}_j`$. Each outcome can depend on both actions through the resulting maturation state on $h(\alpha_i, \alpha_j)$, but each agent orders only its own end. We need no common numerical scale to state the two separate comparisons.

### Definition 8.7 (Conditional and Autonomous Baselines)
For a proposed action pair $(\alpha_i, \alpha_j)$, there are two distinct comparative baselines:

1. Conditional baselines ( $c_i(\alpha_j), c_j(\alpha_i)$ ): What happens if one agent refrains while the other maintains the proposed action?
   
$$
c_i(\alpha_j) = O_i(\alpha_i^0, \alpha_j), \quad c_j(\alpha_i) = O_j(\alpha_i, \alpha_j^0)
$$

   evaluated on the unilateral non-consenting branches $h(\alpha_i^0, \alpha_j)$ and $h(\alpha_i, \alpha_j^0)$.
2. Autonomous baselines ($b_i, b_j$): What happens if *both* agents refrain?

$$
b_i = O_i(\alpha_i^0, \alpha_j^0), \quad b_j = O_j(\alpha_i^0, \alpha_j^0)
$$

   evaluated on the doubly-passive branch $h(\alpha_i^0, \alpha_j^0)$.

The conditional baseline answers: what happens if this agent refrains while the other maintains the proposed action? The autonomous baseline answers: what happens if both refrain? These questions coincide only under additional restrictions on the outcome functions.

### Definition 8.8 (Strictly Improving Conditional Response)
The action $\alpha_i$ is a strictly improving response to $\alpha_j$ when

$$
O_i(\alpha_i, \alpha_j)\succ_i c_i(\alpha_j)
$$

This comparison says that the response is better than refraining while the other action remains fixed. It is only a conditional comparison; the full purposeful-choice condition also requires feasibility, enactment, and the absence of a strictly preferred feasible rival.

### Proposition 8.8a (Purposeful Action Induces a Strictly Improving Conditional Response)
If agent $i$'s enacted choice on the joint branch $h(\alpha_i, \alpha_j)$ is purposeful ($\mathsf{P}$) and differs from inaction ($\alpha_i \neq \alpha_i^0$), then $\alpha_i$ is necessarily a strictly improving conditional response to $\alpha_j$:

$$
\mathsf{P}(i, t, h(\alpha_i, \alpha_j), \alpha_i) \wedge \alpha_i \neq \alpha_i^0 \implies O_i(\alpha_i, \alpha_j) \succ_{i, t, h} c_i(\alpha_j)
$$

**Proof.** By [Definition 3.1](03_preference_purpose_and_opportunity_cost.md#definition-31-physical-scarcity-predicate) (Purposeful Action), enacting an active choice $\alpha_i \neq \alpha_i^0$ requires that its end strictly improve upon the inertial end under the agent's preference ranking: $`\text{End\_of}(i, \alpha_i, t, h') \succ_{i, t, h} \text{End\_of}(i, \alpha_i^0, t, h')`$. By [Proposition 8.5](#proposition-85-a-unilateral-counterfactual-preserves-the-other-agents-present-choice) (Co-Agency Branching), switching $i$'s action from $\alpha_i$ to $\alpha_i^0$ preserves $j$'s enacted action $\alpha_j$. Hence the inertial counterfactual is precisely the unilateral branch $h(\alpha_i^0, \alpha_j)$, whose outcome is $c_i(\alpha_j)$. Thus $O_i(\alpha_i, \alpha_j) \succ_{i, t, h} c_i(\alpha_j)$. $\blacksquare$

The conditional comparison supplies a reason to respond. To characterize a mutually beneficial interaction, we additionally compare the joint outcome with the outcome in which both agents refrain. For the grain holder and the cloth holder, this asks whether each prefers the result of their agreement to their autonomous baseline. The definition of catallactic exchange combines these two kinds of comparison for both participants.

### Definition 8.9 (Catallactic Exchange at an Interaction Node)
An action pair $(\alpha_i, \alpha_j)$ is a catallactic exchange when both conditional comparisons and both autonomous comparisons hold:

$$
\begin{aligned}
O_i(\alpha_i, \alpha_j) &\succ_i c_i(\alpha_j) \\
O_j(\alpha_i, \alpha_j) &\succ_j c_j(\alpha_i), \\
O_i(\alpha_i, \alpha_j) &\succ_i b_i \\
O_j(\alpha_i, \alpha_j) &\succ_j b_j
\end{aligned}
$$

The first pair of inequalities describes each participant's reason to perform its part given the other participant's action. The second describes the gain from their joint interaction relative to autonomous non-intervention. All four comparisons are intrapersonal: each actor orders its own ends.

### Proposition 8.10 (Mutual Gain in Catallactic Exchange)
*Every catallactic exchange places each participant strictly above its autonomous baseline in that participant's own preference relation.*

**Proof.** The conclusion consists of the last two clauses of [Definition 8.9](#definition-89-catallactic-exchange-at-an-interaction-node). $\blacksquare$

The proposition is definitional, but its role is substantive: it specifies exactly which welfare claim the term *catallactic exchange* contains. It gives two ordinal improvements without measuring their sizes, comparing them across persons, or asserting a gain to an uninvolved third party.

---

## Coercion, Defensive Action, and Peaceful Competition

A response can be purposeful because it is preferable to a threatened alternative without being voluntary relative to the unmolested baseline. The definitions in this section keep those comparisons distinct and derive the physical conditions used to classify coercive invasion from the Action Axiom.

### Definition 8.11 (Coercive Extortion)
Let $\alpha_j^{\text{threat}}$ be an action of $j$. An interaction is coercive extortion in the local outcome model when the victim's response improves upon refusal under the threat, the aggressor gains both conditionally and relative to its autonomous baseline, and the victim falls below its autonomous baseline:

$$
\begin{aligned}
O_i(\alpha_i, \alpha_j^{\text{threat}}) &\succ_i
 O_i(\alpha_i^0, \alpha_j^{\text{threat}}), \\
O_j(\alpha_i, \alpha_j^{\text{threat}}) &\succ_j
 O_j(\alpha_i, \alpha_j^0), \\
O_j(\alpha_i, \alpha_j^{\text{threat}}) &\succ_j b_j, \\
b_i &\succ_i O_i(\alpha_i, \alpha_j^{\text{threat}})
\end{aligned}
$$

### Proposition 8.12 (Conditional Improvement Does Not Imply Voluntary Gain)
*There exists a bilateral interaction in which the victim makes a strictly improving conditional response, yet the interaction is extortion and fails the catallactic-exchange condition.*

**Proof.** Give the victim three ends ordered as follows:

$$
\text{unmolested possession}\succ_i
\text{compliance under threat}\succ_i
\text{injury after refusal}
$$

Let the aggressor prefer receiving the victim's property to receiving nothing. Define the unthreatened outcome to be unmolested possession, compliance with a threat to give the middle victim outcome and the preferred aggressor outcome, and refusal under a threat to give the least victim outcome. Compliance then improves upon refusal conditional on the threat. Both aggressor comparisons in [Definition 8.11](#definition-811-coercive-extortion) hold, while the victim prefers its autonomous baseline to compliance. Hence the interaction satisfies extortion. The victim's autonomous-gain clause in [Definition 8.9](#definition-89-catallactic-exchange-at-an-interaction-node) fails. $\blacksquare$

This is the finite highwayman construction. The distinct baselines rigorously isolate the logic of extortion: an agent purposefully chooses the best available option under duress while strictly preferring the uninvaded autonomous state, proving that defensive response under threat is categorically distinct from voluntary catallactic exchange.

The outcome comparison tells us that the victim is worse off than under the autonomous baseline, but subjective loss alone cannot distinguish coercive predation from peaceful market competition. A competing supplier may draw away customers and leave a rival worse off than before without touching the rival's person or property. To avoid misclassifying competitive loss as coercion, the Action Frame derives property, invasion, and title endogenously from initial appropriation and feasible menus.

### Definition 8.13 (Purposeful Lockean Homesteading and Clean-Title Traces)
An action $\alpha$ is a pure Lockean homesteading action for commodity $m$ when it is non-trade, uses zero units of $m$, and yields a positive quantity of $m$:

$$
\neg \text{IsTradeAction}(\alpha) \wedge u(\alpha, m) = 0 \wedge 0 < y(\alpha, m)
$$

When an agent purposefully enacts Lockean homesteading ($\mathsf{P}$), the transition law ([Theorem 2.13](02_time_histories_and_physical_execution.md#theorem-213-inaction-leaves-inventory-unchanged) and [Proposition 2.14](02_time_histories_and_physical_execution.md#proposition-214-inventory-changes-reflect-inputs-and-outputs)) ensures:
1. Appropriator improvement: Agent $i$ strictly improves over inaction ( $`\text{End\_of}(i, \alpha, t, h) \succ_{i, t, h} \text{End\_of}(i, \alpha_i^0, t, h)`$ ) and strictly increases its physical stock: $\omega(i, t', h, m) > \omega(i, t, h, m)$.
2. Non-invasive appropriation: For every passive bystander $j$ enacting $\alpha_j^0$, $j$'s physical stock $\omega(j, t', h, \cdot)$ and resource-feasible menu are completely preserved: no previously feasible action is stripped from $j$'s menu. Any contemplated action of $j$ requiring $m$ was already infeasible at $t$ because $j$'s stock of $m$ was zero; first appropriation by $i$ strips no previously feasible action from $j$.

Path-dependent clean title $\text{title}(k, m)$ tracks legitimate property boundaries established by original appropriation or voluntary transfer, distinct from present physical stock $\omega(k, t, h, m)$:
- Theft: Seizing goods non-consensually reduces the victim's physical stock below clean title ( $\omega(i, t', h, m) < \text{title}(i, m)$ ), constituting a physical invasion ($\text{IsPathDependentTitleInvasion}$).
- Restitution (the Thief-and-Baker theorem): When rightful owner $i$ recovers stolen goods from possessor $j$ without $j$'s consent, $j$'s physical stock contracts, but because $\omega(j, t', h, m) \ge \text{title}(j, m)$, restitution restores possession to clean title and is non-invasive ($\neg \text{IsPathDependentTitleInvasion}$).

### Definition 8.13a (Directed Physical Invasion and Action-Axiom Menu Stripping)
In the Action Frame, physical invasion is formulated as an explicit directed inter-agent relation $I_{j \to i}(\alpha_j)$ indicating that action $\alpha_j$ of agent $j$ invades agent $i$'s clean title.

At decision node $\langle t, h\rangle$, action $\alpha_j$ physically invades agent $i$ along transition $t \to t'$ when executing $\alpha_j$ on the unilateral non-consenting branch $h(\alpha_i^0, \alpha_j)$ (where $i$ refrains) strictly contracts $i$'s physical stock below clean title:

$$
I_{j \to i}(\alpha_j) \iff \exists m \in \mathcal{M}, \quad \omega_i(t', h(\alpha_i^0, \alpha_j), m) < \text{title}_i(m) \ \wedge\ \omega_i(t', h(\alpha_i^0, \alpha_j), m) < \omega_i(t, h, m)
$$

### Theorem 8.13b (Action-Axiom Menu-Stripping Equivalence)
Under clean initial title ( $`\text{title}_i(m) \le \omega_i(t, h, m)`$ ) and tight-action richness, $I_{j \to i}(\alpha_j)$ holds if and only if $j$'s action strips at least one feasible action from $i$'s feasible action menu:

$$
I_{j \to i}(\alpha_j) \iff \exists \beta \in \mathcal{A}_{\text{cont}}\bigl(i, t', h(\alpha_i^0, \alpha_j)\bigr), \quad \beta \in \mathcal{A}_{\text{feas}}(i, t, h) \ \wedge\ \beta \notin \mathcal{A}_{\text{feas}}\bigl(i, t', h(\alpha_i^0, \alpha_j)\bigr)
$$

*Physical invasion is thus derived directly from the Action Axiom:* an action invades another agent if and only if it forcibly destroys or seizes scarce means, stripping previously feasible purposeful actions from the victim's choice menu without consent.

### Definition 8.13c (Voluntary Exchange, Anchored Extortion, and Peaceful Competition)
With directed physical invasion predicates $I_{i \to j}(\alpha_i)$ and $I_{j \to i}(\alpha_j)$ (shortened to $I_i, I_j$ when the counterparties are fixed):

1. Voluntary exchange:
   
$$
\neg I_i(\alpha_i) \wedge \neg I_j(\alpha_j) \wedge O_i(\alpha_i, \alpha_j) \succ_i b_i \wedge O_j(\alpha_i, \alpha_j) \succ_j b_j
$$

   Neither participant invades the other, and both strictly gain relative to their autonomous baselines.
2. Anchored extortion:

$$
\begin{aligned}
I_j(\alpha_j^{\text{threat}})\ \wedge\\
&O_i(\alpha_i, \alpha_j^{\text{threat}}) \succ_i c_i(\alpha_j^{\text{threat}})\\
\wedge\;&b_i \succ_i O_i(\alpha_i, \alpha_j^{\text{threat}})\\
\wedge\;&O_j(\alpha_i, \alpha_j^{\text{threat}}) \succ_j b_j
\end{aligned}
$$

   Agent $j$'s action is invasive (stripping $i$'s clean-title stocks and feasible menu), the victim complies because compliance improves upon refusal under the threat, the victim falls below the unmolested autonomous baseline, and the aggressor gains.
3. Peaceful competition by $j$ against $i$:

$$
\neg I_i(\alpha_i) \wedge \neg I_j(\alpha_j) \quad \wedge \quad O_j(\alpha_i, \alpha_j) \succ_j c_j(\alpha_i) \quad \wedge \quad b_i \succ_i O_i(\alpha_i, \alpha_j)
$$

The competitor's action is non-invasive, improves the competitor's result relative to that competitor's inaction while the other action remains fixed, and leaves the rival below the autonomous baseline. Crucially, peaceful competition preserves all of $i$'s clean-title stocks and leaves $i$'s feasible menu $`\mathcal{A}_{\text{feas}}`$ completely intact; the rival's loss is purely ordinal and catallactic, not a physical deprivation of means.

### Proposition 8.14 (Peaceful Competition Excludes Anchored Extortion)
*An interaction satisfying the peaceful-competition predicate cannot satisfy the anchored-extortion predicate for the same action pair.*

**Proof.** Peaceful competition entails $\neg I_j(\alpha_j)$. Anchored extortion entails $I_j(\alpha_j)$. Their conjunction is contradictory. $\blacksquare$

### Theorem 8.15 (The Three Stated Categories Are Pairwise Disjoint)
*Under strict preference asymmetry, the three catallactic categories—Voluntary Exchange, Anchored Extortion, and Market Competition—are pairwise mutually exclusive:*

$$
\begin{aligned}
\neg &(\text{VoluntaryExchange}(N, \alpha_i, \alpha_j) \land \text{CoerciveExtortion}(N, \alpha_i, \alpha_j)) \\
{}\land \neg &(\text{VoluntaryExchange}(N, \alpha_i, \alpha_j) \land \text{MarketCompetition}(N, \alpha_i, \alpha_j)) \\
{}\land \neg &(\text{CoerciveExtortion}(N, \alpha_i, \alpha_j) \land \text{MarketCompetition}(N, \alpha_i, \alpha_j))
\end{aligned}
$$

| Catallactic Category | Invasion by $j$ | Victim's comparison with autonomous baseline | Other agent's relevant gain |
| :--- | :---: | :---: | :---: |
| Voluntary Exchange | No, and $i$ is non-invasive | Yes | Gain over autonomous baseline |
| Anchored Extortion | Yes | No: $b_i\succ_i O_i$ | Gain over autonomous baseline |
| Market Competition | No, and $i$ is non-invasive | No: $b_i\succ_i O_i$ | Gain over $j$'s inaction with $i$'s action fixed |

**Proof.**
1. Invasiveness directly separates Voluntary Exchange ($\neg I_j$) from Anchored Extortion ($I_j$).
2. Subjective baseline comparison separates Voluntary Exchange ($O_i \succ_i b_i$) from Market Competition ($b_i \succ_i O_i$) by preference asymmetry ( $\neg (b_i \succ_i O_i \land O_i \succ_i b_i)$ ).
3. Invasiveness separates Anchored Extortion ($I_j$) from Market Competition ($\neg I_j$). $\blacksquare$

The three predicates separate voluntary exchange, extortion, and peaceful competition in the model. They do not classify every possible interaction. We use them to keep defensive compliance distinct from voluntary gain and a competitor's economic loss distinct from physical invasion.

---

## Matched Exchange and Physical Transfer

An offer by itself changes no inventory. We now require the matching acceptance and then apply the inventory equations. Only after determining the physical transfer can we state the separate preference inequalities that characterize purposeful exchange.

### Definition 8.16 (Matched Offer and Acceptance)
Fix distinct goods $m_A, m_B$ and quantities $q_A, q_B \in \mathbb{N}$. Put

$$
\alpha_i = \text{Offer}(i, j, q_A, m_A, q_B, m_B), \quad
\alpha_j = \text{Accept}(j, i, q_A, m_A, q_B, m_B)
$$

The trade is matched on $h$ at $t$ when the enacted actions of $i$ and $j$ are respectively $\alpha_i$ and $\alpha_j$. The offer specifies a common set of terms; acceptance refers to those same terms. An unmatched offer or acceptance is a unilateral trade action.

We assume positive quantities when discussing a nontrivial exchange. The balance equations themselves remain meaningful when one quantity is zero.

### Theorem 8.17 (Physical Balances of Matched Exchange)
Suppose the offer and acceptance are matched, and $t'$ is the immediate successor of $t$ on $h$. Write $`\omega'_k(m) = \omega(k, t', h, m)`$. Then

$$
\begin{aligned}
\omega'_i(m_A) + q_A &= \omega_i(m_A) \\
\omega'_j(m_A) &= \omega_j(m_A) + q_A, \\
\omega'_i(m_B) &= \omega_i(m_B) + q_B \\
\omega'_j(m_B) + q_B &= \omega_j(m_B)
\end{aligned}
$$

**Proof.** Apply the coupled bilateral transfer law first to $m_A$ and then to $m_B$. Distinctness of the goods eliminates the irrelevant incoming or outgoing term in each equation. $\blacksquare$

We write each balance using addition so that all stocks and transfers remain natural numbers. For example, $`\omega'_i(m_A)+q_A=\omega_i(m_A)`$ itself certifies that the offerer had at least $q_A$ units to transfer.

Each matched offer and acceptance is one trade step in the operational trace of Chapter 2. Chaining such steps with production and unmatched actions gives a finite inventory run, whose total-use and total-yield balance accounts for repeated transfers without losing their order. An unmatched offer or acceptance remains a step with no inventory change; it cannot be counted as a completed physical exchange.

### Corollary 8.18 (Conservation of the Joint Stock)
*For either traded commodity, the two-agent total is unchanged:*

$$
\omega'_i(m) + \omega'_j(m) = \omega_i(m) + \omega_j(m), \quad m \in \{m_A, m_B\}
$$

**Proof.** For $m_A$, substitute $`\omega'_j(m_A) = \omega_j(m_A) + q_A`$ and then use $`\omega'_i(m_A) + q_A = \omega_i(m_A)`$. The calculation for $m_B$ is symmetric. $\blacksquare$

Exchange therefore changes the distribution of means while preserving the relevant combined physical stocks. The possible gain arises from the significance of the resulting holdings for the agents' respective ends. Conservation of physical quantities is fully compatible with improvement in both subjective evaluations.

These equations establish the physical change but say nothing about whether either person prefers it. We now return to purposeful choice: each trade action must be feasible and enacted, must improve on inaction, and must be undominated in that person's own feasible menu.

### Definition 8.19 (Purposeful Bilateral Exchange)
A matched offer and acceptance constitute purposeful bilateral exchange when both are purposeful in the sense of Chapter 3 and both differ from passive inertia. Each action must be feasible and executed, must improve upon inertia, and must be undominated among the acting agent's feasible alternatives.

### Theorem 8.20 (The Double Inequality of Exchange)
*Purposeful bilateral exchange entails*

$$
\begin{aligned}
\text{outcome}(i, \alpha_i, t, h) &\succ_i\text{outcome}(i, \alpha_0, t, h), \\
\text{outcome}(j, \alpha_j, t, h) &\succ_j\text{outcome}(j, \alpha_0, t, h)
\end{aligned}
$$

**Proof.** For each participant, purposefulness includes the alternative that the enacted action is inertia or its end is strictly preferred to the inertial end. The trade actions are distinct from inertia. Hence the strict-preference alternative holds for each participant. $\blacksquare$

The theorem establishes that purposeful bilateral exchange requires mutual expected improvement over inaction, formally capturing the Double Inequality of Exchange within the choice structure.

### Proposition 8.21 (Purposefulness on a Binary Trade Menu)
*Suppose each participant has only inertia and its trade action in its feasible menu. Suppose the trade actions are feasible, executed, distinct from inertia, and strictly preferred to inertia. Then both actions are purposeful, and the matched pair constitutes purposeful bilateral exchange.*

**Proof.** Consider $i$. Feasibility, execution, and strict improvement are given. A feasible rival is either inertia or $\alpha_i$. Inertia cannot be strictly preferred to $\alpha_i$ by asymmetry; $\alpha_i$ cannot be strictly preferred to itself by irreflexivity. Thus no feasible rival dominates the trade action. The same argument applies to $j$. $\blacksquare$

This converse makes explicit why gain over inertia alone is insufficient on a larger menu: another feasible trade could be preferred to the proposed one.

### Example: A Fully Specified Two-Person Exchange

We can instantiate the preceding conditions with two traders, two valued ends, and a one-unit requirement for each good. Each trader begins with two units of one good and values the end served by the other good. On the matched branch, one offers a unit and the other accepts. Give each agent a feasible menu containing inaction and the relevant trade. If each agent prefers the resulting bundle because it makes that agent's valued end attainable, then the preference comparisons follow from the specified end requirements and bundle ranking.

This example satisfies the full choice conditions together with the matched transfer equations. Both agents improve relative to inaction, and the combined stock of each modeled means is conserved, demonstrating how physical resource conservation and teleological end fulfillment jointly realize mutually advantageous exchange.

---

## Ricardo’s Law of Comparative Advantage

We finish with a two-good production example. Relative labor requirements can make specialization advantageous even when one agent uses less labor in both activities. We first derive an interval in which each agent can obtain its import at a lower labor cost than producing it directly; then we add the production and budget conditions needed to compare complete consumption bundles with autarky.

### Definition 8.22 (A Two-Agent Ricardian Economy)
Let $L_i, L_j > 0$ be natural-number labor budgets, and let $a_i(g), a_j(g) > 0$ denote the labor requirements per unit of each good $`g \in \{0, 1\}`$. Agent $i$ has comparative advantage in good $0$ when

$$
a_i(0)a_j(1) < a_j(0)a_i(1)
$$

Since all requirements are positive, we may also express this ordering as a comparison of rational ratios:

$$
\frac{a_i(0)}{a_i(1)} < \frac{a_j(0)}{a_j(1)}
$$

These ratios compare labor requirements, not preferences. In the natural-number formulation we can make the same comparison by cross multiplication, avoiding any loss from integer division.

A difference in relative labor requirements suggests a division of tasks, but it does not yet establish a gain to either actor. A proof of gain needs two consumption bundles for each person: what that person can consume when producing independently, and what remains after specialization and exchange. We construct those bundles before choosing terms of trade.

### Definition 8.23 (Autarky and Specialized Consumption)
An autarky bundle $b_i^0=(b_i^0(0),b_i^0(1))$ is supported by an exact labor certificate: for some unused-labor remainder $r_i^0$,

$$
b_i^0(0)a_i(0)+b_i^0(1)a_i(1)+r_i^0=L_i.
$$

Agent $j$'s autarkic bundle has the analogous certificate with its labor requirements and unused-labor remainder. Under specialization, let $i$ produce good $0$ and $j$ produce good $1$, with production bundles $q_i$ and $q_j$. If $i$ exports $x_0$ units of good $0$ and receives $x_1$ units of good $1$, the post-trade bundles $b_i^{\ast}$ and $b_j^{\ast}$ satisfy four exact balances:

$$
\begin{aligned}
b_i^{\ast}(0)+x_0&=q_i(0), & b_i^{\ast}(1)&=q_i(1)+x_1,\\
b_j^{\ast}(0)&=q_j(0)+x_0, & b_j^{\ast}(1)+x_1&=q_j(1).
\end{aligned}
$$

Each production bundle also has an exact labor certificate, including its unused labor. The additive commodity balances certify that each export is covered by production and that each import is added to the recipient's bundle. This keeps labor remainders and trade solvency visible in the natural-number model.

We now choose integer transfer quantities satisfying both labor-cost comparisons. The comparative-advantage inequality orders the two thresholds strictly, so we can select positive quantities between them using products and sums in $\mathbb{N}$.

### Theorem 8.24 (A Strict Interval between Labor-Cost Thresholds)
Under the comparative-advantage inequality, there exist positive integer transfer quantities $x_0, x_1$ such that

$$
x_0a_i(0) < x_1a_i(1), \quad x_1a_j(1) < x_0a_j(0)
$$

**Proof.** Set

$$
x_0 = 2a_i(1)a_j(1), \quad x_1 = a_i(0)a_j(1) + a_j(0)a_i(1)
$$

Both quantities are positive. Put $A = a_i(0)a_j(1)$ and $B = a_j(0)a_i(1)$, so $A < B$. The first desired inequality reduces, after cancellation of the positive factor $a_i(1)$, to $2A < A + B$. The second reduces, after cancellation of $a_j(1)$, to $A + B < 2B$. Both follow from $A < B$. $\blacksquare$

At these terms, each actor can obtain the import by producing the export at lower labor cost than direct production of the import. This is a comparison of production costs, not yet a proof that either actor prefers the resulting bundle or that both final bundles dominate their autarkic bundles. For that stronger conclusion, we need sufficient labor budgets, feasible exports, certified transfer balances, and preference comparisons over the resulting bundles.

The comparative-advantage theorem requires only the following cross-multiplied lower bounds on labor budgets:

$$
2a_i(0)a_j(0)a_i(1)\le L_i, \quad
2a_i(0)a_j(1)a_j(0)\le L_j.
$$

They support the explicit production and transfer quantities while recording unused labor in the balance. The larger factor-of-four budgets appear in the separate universal construction that builds an economy from arbitrary positive comparative-advantage coefficients. These are sufficient bounds for the stated construction, not necessary conditions for every gain from trade. The example evaluates bundles by coordinatewise weak improvement with a strict gain in at least one good; for more complex goods, we use the end-requirement comparison from Chapter 1.

### Example 8.25 (Association under Absolute Advantage)
Let $a_i=(1,2)$, $a_j=(6,3)$, $L_i=120$, and $L_j=240$. Agent $i$ requires less labor in both lines, while comparative advantage lies in good $0$ because $1\cdot3<6\cdot2$. The autarky certificates use bundles $(0,12)$ and $(6,0)$; each requires 24 and 36 units of labor respectively, with the remaining 96 and 204 units recorded as unused labor. Under specialization, production is $(24,0)$ for $i$ and $(0,12)$ for $j$, leaving 96 and 204 units unused.

The trade quantities are $x_0=15$ and $x_1=12$. The post-trade bundles are $(9,12)$ and $(15,0)$, certified by $9+15=24$, $12=0+12$, $15=0+15$, and $0+12=12$. Each trader retains its baseline quantity of good $1$ and gains nine units of good $0$. This finite witness follows the exact balances in the formal example.

### Equal Opportunity Costs and Interior Autarky

The formal development also gives a converse boundary: if the cross-multiplied opportunity costs are equal, the labor-cost inequalities for a feasible exchange cannot include the strict gain condition for agent $i$ that appears in the certificate. Equal opportunity costs therefore cannot supply the strict mutual-gain certificate used here. With unequal opportunity costs, a further certificate starts from an interior autarky bundle when $q_{i1}\ge a_i(0)a_j(0)$ and $q_{j0}\ge a_i(0)a_j(1)$. It constructs labor-balanced production and covered transfers such that agent $i$ strictly gains, agent $j$ retains its original bundle, total good $1$ is conserved, and aggregate good $0$ rises. The result is deliberately one-sided and requires those specific minimum components; it does not claim that every bundle with some positive output in both goods admits the same construction.

### Proposition 8.26 (Bilateral Exchange in the Recursive Program Action Frame)
The formal system provides a constructive witness (`Praxeology/Catallactics/ProgramExchangeWitness.lean`) that executes a matched two-good exchange inside the recursive physical `ProgramActionFrame`:
1. **Physical Program Execution**: Two agents with initial endowments $\omega_0 = \langle 0, 1 \rangle$ and $\omega_1 = \langle 1, 0 \rangle$ simultaneously submit matched `.offer` and `.accept` actions exchanging one unit of good 1 for one unit of good 0. The physical transition balance conserves stocks and executes the transfer.
2. **Autonomous Ordinal Preferences**: Each agent's preference is an independent, explicit ordinal ranking over the good they seek ($`\text{good}_0`$ for agent 0, $`\text{good}_1`$ for agent 1). Preferences are strictly independent of the physical transfer technology.
3. **Joint Purposefulness**: Both the offer and the acceptance are proved undominated and strictly improve over inaction, satisfying the Double Inequality of Exchange within the compiled action frame.

## Conclusion

We have moved from individual choice to joint action, property rules, compatible plans, and matched exchange. The comparative-advantage example shows how different relative production costs can create room for mutually preferred transfers, while the exchange analysis keeps preference evidence separate from physical feasibility. We now add a commonly accepted medium and price records to study indirect exchange and calculation across unlike inputs.

---
