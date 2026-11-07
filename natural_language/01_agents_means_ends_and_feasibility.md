# Chapter 1: Agents, Means, Ends, and Feasibility

Economists have long sought to understand how societies produce and distribute wealth. They have examined how work is divided, why goods exchange at particular prices, and how the decisions of many people come together in production and trade. Economists have approached these questions in many ways, each bringing different features into view.

Many models used in mainstream economics describe activity through aggregates, such as total output or employment, and many also represent the choices of individuals and firms. Aggregates can reveal broad patterns while leaving differences in people's resources, plans, and information hidden. An equilibrium model can describe conditions under which plans fit together, but an account of how those conditions come about requires further assumptions about the process.

Failures to explain or anticipate economic changes have raised questions about whether the assumptions of some models capture the processes they are intended to describe. We take these questions as a reason to examine the foundations more closely. We begin with the elements of economic activity: agents, the actions open to them, the means they possess, and the ends they pursue. Our task is to specify these elements and their connections precisely enough that we can see what follows from them and where further assumptions are needed.

We can begin to see the economic problem in the use of a single resource. The same means may serve more than one purpose, yet the stock available may not be sufficient for all of them. Choosing one use can therefore leave another purpose unfulfilled. When people have different resources and plans, one person's possibilities can also depend on what others choose to do. To investigate these relationships, we need to describe both the opportunities open to each person and the actions through which people interact.

Consider a baker with one sack of flour who contemplates baking bread or offering the flour to a neighbor for fuel. Each action has its own requirements, and the offer also needs a matching acceptance before an exchange takes place. To understand the baker's possibilities, we must distinguish the available stock from the actions considered and the ends they are intended to serve.

Our aim is to develop a mathematical account in which these distinctions support precise arguments. We begin with agents and actions, specify the means available and required, and use them to determine which contemplated actions are feasible. Once we have introduced enactment and preference, we can study purposeful choice and then examine how choices interact in exchange, prices, production, and institutions.

## The Action Frame

Before we define these objects one by one, we describe the setting in which they belong. We call this setting an **action frame**. It supplies domains for agents, moments, histories, actions, physical means, and ends, together with rules that connect them. Those rules say which actions an agent considers at a situation, what means each action uses and yields, which action is enacted, and which end is assigned to it. Further structure records temporal order, preferences, and uncertainty. A particular economic model results when we specify these domains and rules.

An action is an element of the action domain. The frame assigns each action an input schedule and an output schedule: for every physical means, the schedules state how many units the action uses and how many units it yields. The frame separately records whether the action is considered and feasible for an agent at a given situation, whether it is enacted there, and what end it is intended to bring about. We keep these assignments separate because physical requirements, actual choice, and intended result answer different questions.

One distinguished action, written $\alpha_0$, represents refraining from intervention. It uses and yields zero physical means. The action domain also includes forms of offer and acceptance, each specified by the agents involved and the kinds and quantities of means proposed for exchange. These are specific operational forms within the broader action domain.

### Definition 1.1 (The Basic Vocabulary of an Action Frame)

We collect the frame's domains and passive action into its basic signature:

$$
\Sigma_{\text{prx}} = \langle \mathcal{I}, \mathcal{T}, \mathcal{H}, \mathcal{A}, \mathcal{M}, \mathcal{E}, \alpha_0 \rangle
$$

1. **Agents.** $\mathcal{I}$ is a nonempty finite set of actors. We write $i, j, k$ for its members.

2. **Moments.** $\mathcal{T}$ is the domain of moments; we write $t, t', \tau$ for its members. The frame accommodates both discrete and continuous temporal structures.

3. **Histories.** $\mathcal{H}$ is the domain of histories; we write $h, h'$ for its members. A history represents a possible course through moments; Chapter 2 will make this precise.

4. **Actions.** $\mathcal{A}$ is a nonempty domain of actions; we write $\alpha, \beta, \gamma$ for its members.

5. **Means.** $\mathcal{M}$ is the domain of physical resources, such as commodities and productive inputs. We write $m, m_A, m_B$ for its members. Scarcity is determined endogenously within each situation based on available physical endowments relative to action requirements.

6. **Ends.** $\mathcal{E}$ is the domain of ends; we write $e, e_1, e_2$ for its members. It accommodates intended and realized results, including representations of physical bundles and results dated by a moment.

7. **Passive action.** $\alpha_0$ is the distinguished member of $\mathcal{A}$ introduced above.

We will use the frame to study purposeful action. For an agent $i$, a moment $t$, a history $h$, and an action $\alpha^{\ast}$, we write:

$$
\mathsf{P}(i, t, h, \alpha^{\ast})
$$

to state that the action is purposeful for that agent at that situation. Chapter 3 will give the conditions for this statement, after Chapter 2 has explained how moments and histories form decision situations. We begin with endowments and action requirements, which will let us determine which actions are physically feasible.

### Constructive Witnesses and Model-Theoretic Consistency

An axiomatic formalization of human action poses an essential mathematical requirement: **consistency**. Beyond defining domains and axioms governing physical conservation, temporal branching, and purposeful evaluation, we establish that these axioms hold together coherently. In constructive mathematics, consistency is established by exhibiting an explicit **model witness**—a concrete, computable mathematical structure in which every domain is an explicit set, every transition is verified by exact finite calculation, and every structural law holds.

Throughout this treatise, the term **witness** operates at two distinct mathematical levels:

1. **Global Action Frame Witnesses (Model-Theoretic Consistency):** An explicit mathematical instantiation of the entire praxeological signature $\Sigma_{\text{prx}}$ that satisfies all structural axioms. Demonstrating that the type of action models is inhabited certifies that the praxeological ontology is mathematically consistent and non-vacuous. Such witnesses rule out the risk of vacuous deduction, in which mutually contradictory premises would trivially entail arbitrary false conclusions. Furthermore, specialized action frame witnesses (such as bilateral exchange frames, firm hierarchy frames, and multi-stage credit lifecycle frames) demonstrate that intricate economic arrangements can hold together within the unified axiomatic architecture without requiring ad-hoc external axioms or unmodeled escapes.

2. **Local Mathematical Witnesses (Constructive Truth of Existential Claims):** An explicit mathematical object that establishes an existential proposition $\exists x, \Phi(x)$. For example, when demonstrating that one bundle of means teleologically dominates another ($b_1 \triangleright_{\mathrm{T}} b_2$), a local witness is a concrete, strictly attained set of ends $S^{\ast}$ that is feasible under $b_1$ but physically unobtainable under $b_2$. Similarly, when demonstrating that an economic operator is non-monotone, a local witness consists of an explicit pair of states for which inclusion fails.

By pairing general conditional theorems with concrete constructive witnesses, the treatise ensures that every deduced economic law rests on a verified axiomatic floor.

---

## Physical Endowments, Requirements, and Feasible Menus

We now connect actions to stocks of physical means. An inventory tells us what an agent has; an action's input schedule tells us what it requires; together they determine feasibility. We then use a separate requirement schedule to ask which ends a bundle could attain.

### Definition 1.2 (Indexed Physical Endowments)
We record the stock of each means for each agent, moment, and history by a function:

$$
\omega : \mathcal{I} \times \mathcal{T} \times \mathcal{H} \times \mathcal{M} \to \mathbb{N}
$$

Thus $\omega(i,t,h,m)$ is the natural-number quantity of means $m$ assigned to agent $i$ at the indexed situation. Chapter 2 will impose the condition that the same present stock is recorded on histories that have not yet divided.

### Definition 1.3 (Input Depletion and Output Yield Functions)
For each action and each means, we specify both the amount used and the amount yielded:
1. **Input Function**: $u : \mathcal{A} \times \mathcal{M} \to \mathbb{N}$, specifying the discrete units of means $m$ used by action $\alpha$.
2. **Output Function**: $y : \mathcal{A} \times \mathcal{M} \to \mathbb{N}$, specifying the discrete units of means $m$ produced by action $\alpha$.
3. **Passive Baseline Neutrality**: The inertial baseline action $\alpha_0$ consumes and produces zero physical goods:

$$
\forall m \in \mathcal{M}, \quad u(\alpha_0, m) = 0 \quad \wedge \quad y(\alpha_0, m) = 0
$$

### Definition 1.4 (Action Menus: Contemplation and Feasibility)
At a decision situation, we distinguish the actions an agent considers from those the agent can physically carry out:

**Contemplated Action Menu.** We write the finite set of actions actively considered by agent $i$ as $`\mathcal{A}_{\text{cont}}`$. We require inaction to belong to this set at every decision situation:

$$
\alpha_0 \in \mathcal{A}_{\text{cont}}(i, t, h)
$$

**Feasible Action Menu.** We write the subset of contemplated actions that meet the agent's current physical constraints as $`\mathcal{A}_{\text{feas}}`$. Its members require no more of any means than the agent currently possesses:

$$
\alpha \in \mathcal{A}_{\text{feas}}(i, t, h) \iff \alpha \in \mathcal{A}_{\text{cont}}(i, t, h) \wedge \forall m \in \mathcal{M}, \quad u(\alpha, m) \le \omega(i, t, h, m)
$$

The first set records deliberation; the second filters it by current resource requirements. In Chapter 2 we require the menu and stock at a shared moment to agree across histories through that moment. In Chapter 5, when we compare choices across projected situations, we will state separately when availability must be uniform across them.

Natural-number accounting uses an exact remainder whenever a quantity is used from a larger stock. If $u\le n$, the remainder is a natural number $r$ certified by

$$
u+r=n.
$$

This certificate states both that the use is covered and exactly what remains; the remainder is unique. Later inventory, production, and trade balances follow this additive form. A price spread is recorded in the same way: lower observed price plus spread equals upper observed price. These certificates prevent truncated subtraction or an unrecorded division remainder from making an infeasible use look valid.

### Proposition 1.5 (Inaction Is Feasible)
For every agent and decision situation, the feasible menu contains $\alpha_0$ and is therefore nonempty.

**Proof.** We check the two requirements in the definition of feasibility. The passive action is contemplated, and it uses zero units of every means. Since every endowment is a natural number, zero does not exceed any stock. Hence $\alpha_0$ is feasible, providing an element of the feasible menu. $\blacksquare$

### Definition 1.6 (The Technological Requirement Schedule)
To describe attainable ends independently of any particular action, we give each end a physical requirement schedule:

$$
\rho : \mathcal{E} \times \mathcal{M} \to \mathbb{N}
$$

Here $\rho(e,m)$ is the number of units of means $m$ required for end $e$. This schedule lets us compare bundles by the ends they can jointly support.

### Definition 1.7 (Single-End and Joint Attainability)
Let $b$ be a bundle, assigning a natural-number quantity to each means. We say that one end is attainable when the bundle covers every requirement; a finite collection is jointly attainable when the bundle covers the sum of their requirements.
1. An individual end $e \in \mathcal{E}$ is **attainable** under bundle $b$, written $\text{attains}(\rho, b, e)$, iff $b$ contains sufficient units of every factor:

$$
\text{attains}(\rho, b, e) \iff \forall m \in \mathcal{M}, \quad \rho(e, m) \le b(m)
$$

2. A finite set of ends $S \subseteq_{\text{fin}} \mathcal{E}$ is **jointly attainable** under bundle $b$, written $\text{attains}(\rho, b, S)$, iff $b$ simultaneously covers the aggregate factor requirements across all ends in $S$:

$$
\text{attains}(\rho, b, S) \iff \forall m \in \mathcal{M}, \quad \sum_{e \in S} \rho(e, m) \le b(m)
$$

### Definition 1.8 (Physical and Attainability-Based Bundle Orders)
**Raw Physical Vector Dominance.** We say that bundle $b_1$ physically dominates bundle $b_2$, written $\triangleright_{\mathrm{P}}(b_1, b_2)$, when $b_1$ contains at least as much of every means and strictly more of at least one:

$$
\triangleright_{\mathrm{P}}(b_1, b_2) \iff (\forall m \in \mathcal{M}, b_2(m) \le b_1(m)) \wedge (\exists m \in \mathcal{M}, b_2(m) < b_1(m))
$$

**Teleological Bundle Dominance.** We say that $b_1$ dominates $b_2$ with respect to requirement schedule $\rho$ and a domain of valued ends $`\mathcal{E}_{\mathrm{val}} \subseteq \mathcal{E}`$, written $`\triangleright_{\mathrm{T}}(\rho, \mathcal{E}_{\mathrm{val}}, b_1, b_2)`$, when every finite set of valued ends $`S \subseteq_{\text{fin}} \mathcal{E}_{\mathrm{val}}`$ attainable under $b_2$ is also attainable under $b_1$, and at least one finite set of valued ends attainable under $b_1$ is not attainable under $b_2$:

$$
\begin{aligned}
\triangleright_{\mathrm{T}}(\rho, \mathcal{E}_{\mathrm{val}}, b_1, b_2) \iff & \left( \forall S \subseteq_{\text{fin}} \mathcal{E}_{\mathrm{val}}, \text{attains}(\rho, b_2, S) \implies \text{attains}(\rho, b_1, S) \right) \\
& \wedge \; \left( \exists S \subseteq_{\text{fin}} \mathcal{E}_{\mathrm{val}}, \text{attains}(\rho, b_1, S) \wedge \neg \text{attains}(\rho, b_2, S) \right)
\end{aligned}
$$

When $`\mathcal{E}_{\mathrm{val}} = \mathcal{E}`$, this coincides with global bundle dominance $\triangleright_{\mathrm{T}}(\rho, b_1, b_2)$. Restricting to valued ends ensures that attainability comparisons reflect the teleological significance of means for an evaluating agent's concrete purposes.

The two relations answer different questions: physical dominance compares quantities coordinate by coordinate, whereas attainability-based dominance evaluates the ultimate economic services of means. Because additional physical stock remains unusable whenever a required complementary input is absent, teleological dominance directly assesses which ends become physically and technologically realizable.

### Theorem 1.9 (Attainability-Based Dominance Is a Strict Partial Order)
Let $\rho : \mathcal{E} \times \mathcal{M} \to \mathbb{N}$ be a technological requirement schedule and $`\mathcal{E}_{\mathrm{val}} \subseteq \mathcal{E}`$ any set of ends. The relation $`\triangleright_{\mathrm{T}}(\rho, \mathcal{E}_{\mathrm{val}}, \cdot, \cdot)`$ on physical bundles $\mathcal{M} \to \mathbb{N}$ is a strict partial order: it is irreflexive, strictly asymmetric, and transitive.

**Proof.**
1. **Irreflexivity**: Suppose $\triangleright_{\mathrm{T}}(\rho, b, b)$. Then there exists $S$ such that $\text{attains}(\rho, b, S) \wedge \neg \text{attains}(\rho, b, S)$, a direct contradiction.
2. **Asymmetry**: Suppose $\triangleright_{\mathrm{T}}(\rho, b_1, b_2)$ and $\triangleright_{\mathrm{T}}(\rho, b_2, b_1)$. The former yields a witness $S_1$ such that $\text{attains}(\rho, b_1, S_1)$ and $\neg \text{attains}(\rho, b_2, S_1)$. But the universal clause of the latter asserts that any set attainable under $b_1$ is attainable under $b_2$, forcing $\text{attains}(\rho, b_2, S_1)$, a contradiction.
3. **Transitivity**: Suppose $\triangleright_{\mathrm{T}}(\rho, b_1, b_2)$ and $\triangleright_{\mathrm{T}}(\rho, b_2, b_3)$. For any $S$, if $\text{attains}(\rho, b_3, S)$, then by hypothesis $\text{attains}(\rho, b_2, S)$, which in turn implies $\text{attains}(\rho, b_1, S)$. Furthermore, the strictly attained witness $S_1$ of $b_1$ over $b_2$ cannot be attainable under $b_3$ (since attainability under $b_3$ would imply attainability under $b_2$). Thus $S_1$ witnesses strict dominance of $b_1$ over $b_3$. $\blacksquare$

### Lemma 1.10 (Basic Properties of Joint Attainability)
1. **Physical Monotonicity of Attainability**: If $\forall m, b_2(m) \le b_1(m)$, then every jointly attainable end-set under $b_2$ is jointly attainable under $b_1$:

$$
(\forall m, b_2(m) \le b_1(m)) \implies \forall S, \text{attains}(\rho, b_2, S) \implies \text{attains}(\rho, b_1, S)
$$

2. **Empty End-Set Invariance**: The empty set of ends is unconditionally attainable by any physical bundle:

$$
\forall b, \quad \text{attains}(\rho, b, \emptyset)
$$

3. **Singleton Coincidence**: Joint attainability of a singleton set coincides with single-end attainability:

$$
\forall b, e, \quad \text{attains}(\rho, b, \{e\}) \iff \text{attains}(\rho, b, e)
$$

**Proof.** For monotonicity, each requirement sum bounded by the smaller bundle is also bounded by the coordinatewise larger bundle. The empty collection has zero requirement in every coordinate, and the sum over a singleton is just that end's requirement. $\blacksquare$

### Theorem 1.11 (A Directly Usable Good Adds an Attainable End)
When every commodity $m$ directly fulfills a distinct first-order atomic end $`e_{\text{atom}}(m)`$ with unit requirement $`\rho(e_{\text{atom}}(m), m') = \mathbf{1}_{\{m = m'\}}`$, possessing a positive quantity of $m^{\ast}$ ( $`b_1(m^{\ast}) \ge 1`$ ) strictly teleologically dominates the zero endowment $`b_0(m) = 0`$:

$$
\triangleright_{\mathrm{T}}(\rho, b_1, b_0)
$$

**Proof.** First, $`b_0(m)=0\le b_1(m)`$ for every means $m$. By [Lemma 1.10](#lemma-110-basic-properties-of-joint-attainability), every end-set attainable under $`b_0`$ is therefore attainable under $`b_1`$. This proves the required universal inclusion. For strictness, the singleton set $`\{e_{\text{atom}}(m^{\ast})\}`$ requires one unit of $m^{\ast}$ and zero of every other means. It is attainable under $`b_1`$ because $`b_1(m^{\ast})\ge1`$, but not under $`b_0`$, whose stock of $m^{\ast}$ is zero. The singleton witnesses the strict clause. $\blacksquare$

## Conclusion

We have described agents, physical means, ends, requirements, and the resource test that separates feasible from infeasible choices. These definitions tell us what an agent can do with a given stock, but they do not yet say how situations persist or branch through time. We now add moments and histories so that we can describe enactment and trace each stock from one moment to the next.
