# Chapter 9: Money, Prices, and Economic Calculation

We develop monetary exchange, price formation, and the limits of calculation. Numerical prices and cash constraints are treated as physical or institutional quantities; preference claims require separate evidence.

## Menger: Marketability and the Emergence of Money

Direct exchange may fail when neither party values an attainable end served by the good offered by the other. Marketability offers an indirect route: an agent accepts a good partly because it can be exchanged again. The first operator describes how such acceptance can spread.

### Definition 9.1 (Acceptance Profile and Marketability)
For a finite agent set $\mathcal{I}$, an acceptance profile assigns to each good $m \in \mathcal{M}$ a set $\Gamma(m) \subseteq \mathcal{I}$ of agents willing to accept it. Order profiles pointwise:

$$
\Gamma_1 \sqsubseteq \Gamma_2
\quad \iff \quad
\forall m \in \mathcal{M}, \ \Gamma_1(m) \subseteq \Gamma_2(m)
$$

A good $m$ is maximally marketable at $\Gamma$ if

$$
\forall n \in \mathcal{M}, \quad |\Gamma(n)| \le |\Gamma(m)|
$$

It is universally accepted when $\Gamma(m) = \mathcal{I}$. The cardinality here counts accepting agents.

An acceptance profile describes who accepts each good at a given stage. To explain a change in acceptance, we must specify a rule for the next stage. The first rule considers both the extent of current acceptance and the individual feasibility of indirect exchange. Its purpose is to make the passage from an existing profile to a larger one explicit.

### Definition 9.2 (Marketability Adoption Operator)
Let $F(i, m)$ mean that indirect exchange through $m$ is feasible for agent $i$. Define

$$
\Phi(\Gamma)(m) = \Gamma(m) \cup \{i \in \mathcal{I}:\ m\text{ is maximally marketable at }\Gamma
\ \wedge \ F(i, m)\}
$$

This operator preserves existing acceptance and adds the agents satisfying the stated adoption rule. To ground adoption in purposeful human action, we evaluate candidate media through their downstream consumption bundles.

### Definition 9.3 (Mengerian Adoption Decision)
In an Action Frame, a **Mengerian adoption decision** at decision node $\langle t, h \rangle$ specifies an adoption action $\alpha_{\text{adopt}}(m)$ yielding downstream commodity consumption bundle $\text{downstreamBundle}(m)$ for each candidate medium $m \in \mathcal{M}$, with baseline bundle $\text{holdBundle}$ under inaction:

$$
\text{outcome}(i, \alpha_{\text{adopt}}(m), t, h) = \text{BundleEnd}(\text{downstreamBundle}(m)), \quad \text{outcome}(i, \alpha_0, t, h) = \text{BundleEnd}(\text{holdBundle})
$$

In this setting, a dominant medium $m^{\ast}$ possesses superior marketability over candidate $m$ ( $|\Gamma(m)| < |\Gamma(m^{\ast})|$ ) when the indirect exchange network it opens yields a downstream consumption bundle that teleologically dominates that of the less marketable good:

$$
|\Gamma(m)| < |\Gamma(m^{\ast})| \wedge \alpha_{\text{adopt}}(m) \in \mathcal{A}_{\text{feas}} \implies
\text{SubjectiveTeleologicalDominates}(i, t, h, \text{downstreamBundle}(m^{\ast}), \text{downstreamBundle}(m))
$$

### Theorem 9.4 (The Mengerian Money Emergence Theorem)
Under a Mengerian adoption decision, adopting a strictly less marketable medium is disqualified from being purposeful:

$$
|\Gamma(m)| < |\Gamma(m^{\ast})| \implies \neg \mathsf{P}(i, t, h, \alpha_{\text{adopt}}(m))
$$

**Proof.** Suppose by contradiction that adopting the less marketable good $m$ were purposeful ( $\mathsf{P}(i, t, h, \alpha_{\text{adopt}}(m))$ ). Then $\alpha_{\text{adopt}}(m)$ is feasible. By [Definition 9.3](#definition-93-mengerian-adoption-decision), the downstream bundle of $m^{\ast}$ teleologically dominates that of $m$. By `teleological_bundle_dominance_induces_preference`, this teleological dominance natively induces strict preference:

$$
\text{outcome}(i, \alpha_{\text{adopt}}(m^{\ast}), t, h) \succ_{i,t,h} \text{outcome}(i, \alpha_{\text{adopt}}(m), t, h)
$$

Since $\alpha_{\text{adopt}}(m^{\ast})$ is feasible, this strictly preferred alternative directly contradicts the undominatedness condition of purposeful action. Therefore, adopting a less marketable medium cannot be purposeful. $\blacksquare$

### Lemma 9.5 (Inflationarity of Adoption)
For every profile, $\Gamma \sqsubseteq \Phi(\Gamma)$.

**Proof.** For each good, $\Gamma(m)$ is a subset of its union with the newly adopting agents. $\blacksquare$

Inflationarity governs the expansion of a profile along its own sequential trajectory, while cross-profile monotonicity evaluates comparative statics across different initial profiles. In competitive adoption, a good that is maximally marketable under one profile can face displaced demand when a competing good gains adopters, formalizing the dynamic rivalry of alternative media. The following example exhibits this obstruction to global monotonicity of $\Phi$.

### Proposition 9.6 (Universal Acceptance of an Initially Dominant Medium)
Suppose $m^{\ast}$ has strictly more acceptors than every competing good in $\Gamma_0$, every agent can use $m^{\ast}$ for indirect exchange, and no competing good is already universally accepted. Then $\Gamma^{\ast} = \Phi(\Gamma_0)$ satisfies

$$
\Gamma_0 \sqsubseteq \Gamma^{\ast}, \quad
\Gamma^{\ast}(m^{\ast}) = \mathcal{I}, \quad
\Phi(\Gamma^{\ast}) = \Gamma^{\ast}
$$

**Proof.** Strict initial dominance makes $m^{\ast}$ the unique maximally marketable good. Every agent satisfies its feasibility condition, so one application adds all agents to its acceptance set. No competing good receives new acceptors in that step. Such goods remain short of universal acceptance, whereas $m^{\ast}$ now has all agents. Consequently $m^{\ast}$ remains uniquely maximal; a further application adds no new agent to any acceptance set. Inflationarity gives the first assertion. $\blacksquare$

The theorem explains persistence after an initial marketability advantage under universal indirect feasibility. To explain how feasibility itself spreads through local contacts, we next replace the global feasibility relation by a trading network.

---

## Money Diffusion through Trading Networks

Marketability also diffuses progressively across decentralized trading networks. Finite monotone iteration yields a verified fixed point, while topological connectivity governs network-wide adoption.

### Definition 9.7 (Trading Network and Local Indirect Feasibility)
A trading network is a symmetric adjacency relation $G(i, j)$ on agents. Let $S(j)$ be the good supplied by $j$, and let $D(i, m)$ mean that $i$ demands good $m$. Indirect exchange through medium $m$ is locally feasible for $i$ at profile $\Gamma$ when

$$
F_G(\Gamma, i, m)\quad \iff \quad
\exists j \in \mathcal{I}, \ G(i, j) \wedge D(i, S(j)) \wedge j \in \Gamma(m)
$$

The network adoption operator is

$$
\Phi_G(\Gamma)(m) = \Gamma(m) \cup \{i \in \mathcal{I}:F_G(\Gamma, i, m)\}
$$

An agent is added because an accessible supplier of a desired good accepts the medium. This rule differs from the maximum-cardinality rule of [Definition 9.2](#definition-92-marketability-adoption-operator): it does not require the medium to be globally maximal.

### Theorem 9.8 (The Knaster-Tarski Argmax Monotonicity Failure Theorem)
*The natural Mengerian operator that recruits adopters based on global argmax marketability is not globally monotone under profile inclusion:*

$$
\Gamma_1 \sqsubseteq \Gamma_2 \centernot\implies \Phi_{\text{max}}(\Gamma_1) \sqsubseteq \Phi_{\text{max}}(\Gamma_2).
$$

**Proof.** Let two goods $m,m'$ have one acceptor each in $\Gamma_1$, and suppose agent $a$ can use either good for indirect exchange. Then both goods are maximally marketable, so $a$ is added to the acceptance set of $m$. In $\Gamma_2$, keep the one acceptor of $m$ and give $m'$ a second acceptor. Now $m'$ alone is maximally marketable, so $a$ is not added to $m$. Since $\Gamma_1\sqsubseteq\Gamma_2$ but $a\in\Phi_{\text{max}}(\Gamma_1)(m)$ and $a\notin\Phi_{\text{max}}(\Gamma_2)(m)$, global monotonicity fails. $\square$

This example shows why inflationarity and monotonicity must be distinguished. The finite convergence result below uses only inflationarity and finiteness; it needs no monotonicity assumption.

### Proposition 9.9 (Monotonicity of Network Adoption)
If $\Gamma_1 \sqsubseteq \Gamma_2$, then $\Phi_G(\Gamma_1) \sqsubseteq \Phi_G(\Gamma_2)$.

**Proof.** An existing acceptor under $\Gamma_1$ remains an acceptor under $\Gamma_2$. If an agent is newly admitted under $\Gamma_1$, its witnessing supplier also belongs to the larger acceptance set under $\Gamma_2$. The same supplier therefore witnesses local indirect feasibility in the larger profile. $\blacksquare$

Monotonicity compares the evolution of two different starting profiles. Our next question concerns a single starting profile: can acceptance continue to expand indefinitely? Since acceptance is retained and there are only finitely many agents and goods, there are only finitely many possible additions. This finiteness argument establishes stabilization before we ask how widely a particular medium has spread.

### Theorem 9.10 (The Bourbaki-Witt Monetary Fixed-Point Convergence Theorem)
*If both the agent set and the goods set are finite, iteration of an inflationary profile operator from any initial profile reaches a fixed point after finitely many steps.*

**Proof.** Write $\Gamma_{n + 1} = \Psi(\Gamma_n)$, where $\Psi$ is inflationary. Then

$$
\Gamma_0 \sqsubseteq \Gamma_1 \sqsubseteq \Gamma_2 \sqsubseteq \cdots
$$

There are only finitely many profiles. If every consecutive inclusion were strict, this sequence would contain arbitrarily many distinct profiles, contradicting finiteness. Hence $\Gamma_{n + 1} = \Gamma_n$ for some $n$, which is exactly $\Psi(\Gamma_n) = \Gamma_n$. $\blacksquare$

This convergence theorem establishes stabilization purely from inflationarity and finiteness, without requiring global monotonicity. To determine whether the stabilized profile achieves universal adoption, we next examine trading-network connectivity.

A stable profile may leave part of the population outside a medium's acceptance set. To obtain universal acceptance, we must exclude a proper group that already contains the initial acceptor but offers no reason for anyone outside it to join. The required connectivity condition therefore requires a demanded good to cross the boundary of such a group.

### Definition 9.11 (Demand Connectivity Across Trading Links)
Fix a seed agent $s$. The network is demand-connected from $s$ when every proper set $A \subsetneq \mathcal{I}$ containing $s$ admits an agent outside $A$ who demands a good supplied by an adjacent agent inside $A$:

$$
\begin{aligned}
s \in A \wedge A \neq \mathcal{I}
& \implies \exists k \notin A, \exists j \in A, \quad G(k, j) \wedge D(k, S(j))
\end{aligned}
$$

Here demand is a relation between an agent and a good, not a separate domain of Wants. When demand is used to explain purposeful choice, it must be grounded in attainable valued ends. An undirected contact path by itself need not give each agent a reason to accept the medium.

### Theorem 9.12 (The Network Demand-Connected Money Emergence Theorem)
Suppose $s \in \Gamma_0(m^{\ast})$ and the finite network is demand-connected from $s$. Then some finite iterate $\Gamma^{\ast}$ of $\Phi_G$ satisfies

$$
\Phi_G(\Gamma^{\ast}) = \Gamma^{\ast}, \quad \Gamma^{\ast}(m^{\ast}) = \mathcal{I}
$$

**Proof.** Obtain a fixed iterate by [Theorem 9.10](#theorem-910-the-bourbaki-witt-monetary-fixed-point-convergence-theorem). Inflationarity preserves the seed's acceptance. Suppose its terminal acceptance set $A = \Gamma^{\ast}(m^{\ast})$ were proper. Demand-connectivity gives $k \notin A$ and $j \in A$ with $G(k, j)$ and $D(k, S(j))$. Thus $j$ witnesses local indirect feasibility for $k$, so the next iteration adds $k$. This contradicts fixedness. Therefore $A = \mathcal{I}$. $\blacksquare$

[Theorem 9.12](#theorem-912-the-network-demand-connected-money-emergence-theorem) supplies a diffusion result for the designated medium under its initial-acceptance and demand-connectivity premises. A selective-emergence result composes this acceptance module with additional conditions that exclude universal acceptance of competing goods.

---

## Coupled Adoption, Retention, and Direct Barter

The network rule can combine local feasibility with the Mengerian marketability condition. At each stage it retains current acceptors and adds an agent only when the medium is maximally marketable and locally available through a neighboring supplier of a good that the agent demands. On finite agent and good sets, this inflationary operator reaches a fixed point after finitely many rounds. If the candidate medium remains maximally marketable throughout the iteration and every proper cohort that contains the initial adopter has an adjacent unmet demand, the fixed point accepts that medium universally.

Acceptance dynamics also reflect endogenous retention rules. When an operator requires agents to actively satisfy a retention condition at each stage, cohort continuity is determined strictly by those structural criteria, formalizing how institutional or market shifts can expand or contract a medium's circulation.

Direct barter can fail even when traders are arranged in a connected network. In a ring of at least three agents, let each agent demand the next agent's good. No adjacent pair mutually demands the other's output, so those neighbors cannot complete a direct barter that requires reciprocal demand. A generally accepted medium can bridge this mismatch, but the network and demand premises must be stated.

## Reservation Bids and Discrete Market Prices

Once a medium is accepted, reservation bids can be ordered into buyer and seller cohorts. The discrete marginal pair bounds the price interval consistent with the specified quantities; it does not require a continuous Walrasian auctioneer.

### Definition 9.13 (Reservation Bids and Ordered Cohorts)
Let $v_b(r) \in \mathbb{N}$ be the bid of buyer $r$ and $v_s(r) \in \mathbb{N}$ the reservation price of seller $r$. Order buyers by non-increasing bids and sellers by non-decreasing reservations. A buyer is willing at price $P$ when $P \le v_b(r)$; a seller is willing when $v_s(r) \le P$.

These inequalities describe monetary thresholds. To infer purposeful action from them, the threshold comparisons must be connected to the corresponding ends, feasible menus, and execution conditions.

### Proposition 9.14 (Clearance of the Intra-Marginal Cohorts)
Suppose the ordered marginal pair $r^{\ast}$ satisfies $v_s(r^{\ast}) \le P \le v_b(r^{\ast})$. Then every pair $r \le r^{\ast}$ satisfies $v_s(r) \le P \le v_b(r)$.

**Proof.** Seller ordering gives $v_s(r) \le v_s(r^{\ast}) \le P$. Buyer ordering gives $P \le v_b(r^{\ast}) \le v_b(r)$. $\blacksquare$

The preceding proposition identifies the pairs willing to trade once the marginal pair is willing. To identify a boundary of trade, we must also exclude the next buyer and seller. On a discrete money grid, strict exclusion requires a gap of at least one monetary unit. This explains the unit increments in the following price bounds.

### Theorem 9.15 (The Böhm-Bawerk Discrete Marginal-Pair Bracket Theorem)
Let $r^{\ast}$ be a buyer-seller pair whose next pair $r^{\ast}+1$ exists in both ordered cohorts. Let $P \in \mathbb{N}$ satisfy

$$
\max\{v_s(r^{\ast}), v_b(r^{\ast}+1) + 1\} \le P, \quad
P + 1 \le \min\{v_b(r^{\ast}) + 1, v_s(r^{\ast}+1)\}
$$

*Then the marginal pair is willing to trade and the next pair is strictly deterred:*

$$
v_s(r^{\ast}) \le P \le v_b(r^{\ast}), \quad
v_b(r^{\ast}+1) < P < v_s(r^{\ast}+1)
$$

**Proof.** The lower bound gives $v_s(r^{\ast}) \le P$ and $v_b(r^{\ast}+1) + 1 \le P$. The upper bound gives $P + 1 \le v_b(r^{\ast}) + 1$ and $P + 1 \le v_s(r^{\ast}+1)$. Canceling or interpreting the unit increments in the natural-number order yields the four desired inequalities. $\blacksquare$

The unit increments express the discreteness of the price grid. This theorem rigorously derives the precise, non-empty price interval determined by the marginal buyers and sellers, formalizing the Austrian insight that market bids bound a discrete zone of mutually advantageous exchange.

Physical market clearing additionally requires a matching of buyers and sellers and enough holdings to execute the transfers. Each matched transfer carries exact remainder certificates: if the buyer pays price $P$ from cash stock $M$, the remaining cash $r_b$ satisfies $P+r_b=M$; if the seller transfers one unit from stock $Q$, the remaining good $r_s$ satisfies $1+r_s=Q$. The remainders exist only when the payment and delivery are covered, and the resulting ledger uses them as the post-trade stocks. For a finite sequence of solvent matched trades, the inventory-conservation argument extends by induction: each step preserves the relevant total stock, so the complete sequence preserves it as well. Willingness and accounting are distinct parts of the market construction.

## Purposeful Grounds for a Realized Price

The numerical bracket describes which buyers and sellers meet specified monetary thresholds. To interpret those thresholds as reservation prices, connect them to preferences over the ends of actual trade actions. Fix a general action structure, a decision moment, and a history. Suppose a buyer has a ceiling $C$ such that every offer at price $p\le C$ is preferred to inaction, while no offer at $p > C$ is preferred to inaction. Suppose a seller has a floor $F$ such that every offer at $p\ge F$ is preferred to inaction, while no offer at $p < F$ is preferred to inaction. These conditions link monetary valuations directly to underlying preference structures over actual trade actions: the buyer's ceiling $C$ and the seller's floor $F$ define the exact preference boundaries within which exchange is strictly preferred to inaction.

If the buyer has observed cash stock $M$, the funded bid is $\min(C,M)$. It is bounded by both the preference ceiling and available cash. A realized price $P$ satisfying

$$
F\le P\le \min(C,M)
$$

therefore satisfies both participants' reservation comparisons and the buyer's cash constraint. When the seller's offer and buyer's acceptance at this price form an enacted, feasible, purposeful bilateral exchange, both matched actions are active purposeful actions. The realized exchange supplies the action evidence; the reservation premises explain why this price is acceptable to the participants.

The same distinction applies to extra-marginal agents. A buyer whose reservation value is below $P$ is deterred only when the priced action's bundle is strictly dominated, in the model's teleological attainability order, by the passive bundle. A seller whose reservation floor is above $P$ requires the corresponding dominance comparison for the seller. Those comparisons imply that the priced actions are not active purposeful actions. Thus the marginal-pair inequalities acquire behavioral force through the preference and bundle premises, not through arithmetic alone.

In a multilateral setting, sorted cohorts and a clearing allocation determine the matched parties and extra-marginal groups. A realized round still requires evidence that its buyer and seller execute a purposeful matched exchange. The finite arithmetic market construction supplies a candidate clearing price and allocation; the preference-grounded action conditions make the clearing round a result of the general action model.

---

## Cash Balances and Monetary Reserves

Money also serves as a reserve held against uncertain future purchases. Below, we introduce cash reservation under uncertainty and the cash-backed solvency profile under factor price bounds, which provides the microeconomic foundation for evaluating monetary supply and credit expansion in Chapter 10.

### Definition 9.16 (Cash Reservation under Uncertainty)
Let $H_i^p$ be a finite collection of plausible histories, and let $E_i(h)$ be the expenditure required on history $h$. A balance $M_i \in \mathbb{N}$ covers the reservation demand when

$$
\forall h \in H_i^p, \quad E_i(h) \le M_i
$$

A balance satisfying this condition covers the specified expenditures on every plausible branch. The definition connects holding money to the actor's prospective uses of means under uncertainty.

For a producer acquiring multiple inputs under factor-price uncertainty, factor price boxes specify rigorous upper and lower price bounds across all inputs. The supremum prices determine the exact precautionary cash reserve sufficient to ensure project solvency across all admissible price realizations.

### Definition 9.17 (Factor Price Box and Precautionary Cash Demand)
For $d$ discrete production inputs, a **factor price box** $\mathcal{B}$ specifies lower and upper price bounds $P^{\inf}, P^{\sup} : \text{Fin}(d) \to \mathbb{N}$ such that

$$
\forall k < d, \quad P^{\inf}(k) \le P^{\sup}(k).
$$

For an intended input requirement plan $x \in \mathbb{N}^d$, the **precautionary cash demand** is the maximum expenditure required to secure the input bundle across all admissible factor prices:

$$
C^+(\mathcal{B}, x) = \sum_{k < d} P^{\sup}(k) \cdot x(k).
$$

### Proposition 9.18 (Factor Completion Infeasibility under Cash Shortfall)
Suppose a production project requires completing a factor purchase with outlay equal to the precautionary cash demand $C^+(\mathcal{B}, x)$. If the entrepreneur's physical cash endowment $\omega_i(t, h, m)$ satisfies

$$
\omega_i(t, h, m) < C^+(\mathcal{B}, x),
$$

then the completion action is resource-infeasible and cannot be enacted as a purposeful action.

**Proof.** An action requiring outlay $C^+(\mathcal{B}, x)$ uses that quantity of medium $m$. By the action-frame feasibility condition, an action is feasible only if its resource use does not exceed the actor's endowment. Since the cash held is strictly less than the required expenditure, the feasibility condition fails, ruling out purposeful execution. $\blacksquare$

### Definition 9.19 (Cash-Backed Acceptance Profile)
For a finite cohort of entrepreneurs $\text{Cohort} \subseteq \mathcal{I}$, each facing an input plan $x_i \in \mathbb{N}^d$ under factor price box $\mathcal{B}$, the **cash-backed acceptance profile** (or solvent buyer cohort) is the finite subset of entrepreneurs whose money endowments cover their precautionary cash demand:

$$
\mathcal{S}(\omega, m, \mathcal{B}, x, \text{Cohort}) = \left\lbrace i \in \text{Cohort} \;\middle|\; C^+(\mathcal{B}, x_i) \le \omega_i(m) \right\rbrace.
$$

### Proposition 9.20 (Price-Box Widening Contracts the Solvent Cohort)
Let $`\mathcal{B}_1`$ and $`\mathcal{B}_2`$ be two factor price boxes such that $`\mathcal{B}_2`$ represents wider price uncertainty than $`\mathcal{B}_1`$:

$$
\forall k < d, \quad P^{\inf}_2(k) \le P^{\inf}_1(k) \quad \wedge \quad P^{\sup}_1(k) \le P^{\sup}_2(k).
$$

Then for every input plan $x$, precautionary cash demand weakly increases:

$$
C^+(\mathcal{B}_1, x) \le C^+(\mathcal{B}_2, x).
$$

Consequently, the solvent cohort weakly contracts:

$$
\mathcal{S}(\omega, m, \mathcal{B}_2, x, \text{Cohort}) \subseteq \mathcal{S}(\omega, m, \mathcal{B}_1, x, \text{Cohort}).
$$

If, in addition, there exists a required input $k^{\ast}$ with $x(k^{\ast}) > 0$ such that $`P^{\sup}_1(k^{\ast}) < P^{\sup}_2(k^{\ast})`$, then precautionary cash demand strictly increases:

$$
C^+(\mathcal{B}_1, x) < C^+(\mathcal{B}_2, x).
$$

**Proof.** For every coordinate $k$, $`P^{\sup}_1(k) \le P^{\sup}_2(k)`$. Multiplying by the non-negative integer $x(k)$ preserves the inequality. Summing over all $k < d$ gives $`C^+(\mathcal{B}_1, x) \le C^+(\mathcal{B}_2, x)`$. Any agent $i \in \text{Cohort}$ satisfying $`C^+(\mathcal{B}_2, x_i) \le \omega_i(m)`$ therefore also satisfies $`C^+(\mathcal{B}_1, x_i) \le C^+(\mathcal{B}_2, x_i) \le \omega_i(m)`$, proving the subset inclusion. When a strictly positive input has a strictly higher upper price bound, the strict inequality at $k^{\ast}$ makes the sum strictly larger. $\blacksquare$

### Theorem 9.21 (The Network Money Solvency Expansion Theorem)
Suppose indirect exchange through medium $m^{\ast}$ spreads across a finite demand-connected trading network $G$ from an initial seed adopter, transitioning from an initial barter-spread price schedule $`\mathcal{B}_0`$ to the terminal universal-money fixed point $\mathcal{B}^{\ast}$. If the price-box schedule contracts with expanding marketability:

$$
\forall k < d, \quad P^{\sup}_{\ast}(k) \le P^{\sup}_0(k),
$$

then precautionary cash demand weakly falls for all agents, and the cash-backed solvent cohort weakly expands:

$$
\mathcal{S}(\omega, m^{\ast}, \mathcal{B}_0, x, \text{Cohort}) \subseteq \mathcal{S}(\omega, m^{\ast}, \mathcal{B}^{\ast}, x, \text{Cohort}).
$$

**Proof.** By [Theorem 9.12](#theorem-912-the-network-demand-connected-money-emergence-theorem), the network adoption operator reaches a fixed point with universal acceptance of $m^{\ast}$ in finitely many steps. The contraction of price spreads makes $`P^{\sup}_{\ast}(k) \le P^{\sup}_0(k)`$ for all $k < d$. By [Proposition 9.20](#proposition-920-price-box-widening-contracts-the-solvent-cohort), precautionary cash demand satisfies $`C^+(\mathcal{B}^{\ast}, x_i) \le C^+(\mathcal{B}_0, x_i)`$ for every agent $i$. Any agent solvent under $`\mathcal{B}_0`$ satisfies $`C^+(\mathcal{B}^{\ast}, x_i) \le C^+(\mathcal{B}_0, x_i) \le \omega_i(m^{\ast})`$, establishing membership in the expanded solvent cohort $`\mathcal{S}(\omega, m^{\ast}, \mathcal{B}^{\ast}, x, \text{Cohort})`$. $\blacksquare$

## Integer Scaling, Cantillon Networks, and Exact Affordability

All physical quantities, cash balances, and prices in these models are natural numbers. Natural subtraction is truncated at zero, and natural division discards a remainder. A formula that derives a quantity by division therefore needs a divisibility or scaling hypothesis if the quotient is meant to preserve an exact ratio. Where possible, state the claim by cross multiplication instead. For example, a return comparison with positive rate $r$, allowance $d$, and benchmark $v$ is expressed as $s\le r(v+d)$ or $r(v+d) < s$, not as a quotient whose remainder has been silently discarded.

The same discipline applies to comparative-advantage ratios and split quantities: either include the scale factor that makes the relevant products divisible, or formulate the theorem using equivalent cross-multiplied inequalities. Integer arithmetic makes discrete price brackets exact, but it does not license ignoring truncation in other calculations.

### Definition 9.22 (Cantillon Network)
In an Action Frame $\mathcal{W}$, a **Cantillon Network** models the sequential transmission of new money across time and space. A downstream agent $i_{\text{downstream}} \in \mathcal{I}$ holds physical cash balance $M_{\text{downstream}} = \omega(i_{\text{downstream}}, t_{\text{pre}}, h, m_{\text{money}})$. Between initial moment $t_{\text{pre}}$ and subsequent moment $t_{\text{post}}$:
1. Money injection occurs upstream, while the downstream agent's physical cash balance remains unchanged:

$$
\omega(i_{\text{downstream}}, t_{\text{post}}, h, m_{\text{money}}) = \omega(i_{\text{downstream}}, t_{\text{pre}}, h, m_{\text{money}}) = M_{\text{downstream}}
$$

2. Upstream bidding drives the unit price of intermediate capital goods up from $P_{\text{pre}}$ to $P_{\text{post}}$, with $0 < P_{\text{pre}} < P_{\text{post}}$.
3. The downstream agent was solvent at pre-injection prices:

$$
P_{\text{pre}} \le M_{\text{downstream}}
$$

4. The escalated price exceeds the downstream agent's cash balance:

$$
M_{\text{downstream}} < P_{\text{post}}
$$

### Proposition 9.23 (Cantillon Network Purchasing-Power Dilution)
Under a Cantillon network, the downstream agent experiences purchasing-power dilution and complete market exclusion:
1. **Pre-Injection Affordability:** The input was affordable prior to monetary injection:

$$
1 \cdot P_{\text{pre}} \le M_{\text{downstream}}
$$

2. **Post-Injection Market Exclusion:** For any strictly positive quantity $q > 0$, the input is unaffordable post-injection:

$$
\forall q > 0, \quad \neg(q \cdot P_{\text{post}} \le M_{\text{downstream}})
$$

3. **Strict Balance-Price Purchasing Dilution:**

$$
M_{\text{downstream}} \cdot P_{\text{pre}} < M_{\text{downstream}} \cdot P_{\text{post}}
$$

**Proof.** Part 1 is immediate from $P_{\text{pre}} \le M_{\text{downstream}}$. For Part 2, for any $q \ge 1$, $M_{\text{downstream}} < P_{\text{post}} \le q \cdot P_{\text{post}}$, so $q \cdot P_{\text{post}} \le M_{\text{downstream}}$ is impossible. For Part 3, since $P_{\text{pre}} < P_{\text{post}}$ and $0 < P_{\text{pre}} \le M_{\text{downstream}}$ implies $0 < M_{\text{downstream}}$, multiplying by the strictly positive cash balance preserves the strict inequality: $M_{\text{downstream}} \cdot P_{\text{pre}} < M_{\text{downstream}} \cdot P_{\text{post}}$. $\blacksquare$

## Heterogeneous Factors and Monetary Calculation

Monetary prices provide a common accounting unit for physical factors that the componentwise order leaves incomparable. That cost comparison supplies an input to the information-boundary argument: the observer-side conclusion also depends on which prices and valuations the record contains and which decision rules are restricted to that record.

### Definition 9.24 (Physical Input Order and Antichains)
For input vectors $x, y \in \mathbb{N}^d$, define

$$
x\le_{\text{phys}}y\quad \iff \quad
\forall r < d, \ x_r \le y_r
$$

The pair forms a physical antichain when

$$
(\exists a < d, \ y_a < x_a)\quad \wedge \quad
(\exists b < d, \ x_b < y_b)
$$

### Proposition 9.25 (Physical Incomparability)
If $x, y$ form a physical antichain, neither $x\le_{\text{phys}}y$ nor $y\le_{\text{phys}}x$ holds.

**Proof.** The first proposed inequality contradicts the coordinate $a$; the second contradicts the coordinate $b$. $\blacksquare$

For example, $(2, 1)$ and $(1, 2)$ require opposite economizing choices between two factors. The physical description alone contains no common unit in which the two sacrifices can be added.

The antichain leaves the producer with a comparison between unlike quantities. If the two factors have market prices in the same monetary medium, each required quantity can instead be expressed as a monetary expenditure. Adding these expenditures constructs the common cost measure needed for comparison.

### Definition 9.26 (Monetary Input Cost)
Given prices $P_r \in \mathbb{N}$, define

$$
C_P(x) = \sum_{r < d}P_rx_r
$$

### Proposition 9.27 (Comparability of Monetary Costs)
*For any two input vectors,*

$$
C_P(x) \le C_P(y)\quad \vee \quad C_P(y) \le C_P(x)
$$

**Proof.** Both costs are natural numbers, and the natural-number order is total. $\blacksquare$

### Definition 9.28 (Monetary Outlays, Net Return, and Return Ratio)
For a discrete production action $\alpha$ in an action frame $W$ with factor prices $p_A, p_B \in \mathbb{N}$ and output price $p_{\mathrm{out}} \in \mathbb{N}$, the factor outlays and gross revenue are determined by physical factor usage and product yields:

$$
K_A = u(\alpha, m_A) \cdot p_A, \quad K_B = u(\alpha, m_B) \cdot p_B, \quad R = y(\alpha, m_{\mathrm{out}}) \cdot p_{\mathrm{out}}.
$$

Total monetary input cost is $K = K_A + K_B$. For this production outlay, define:
1. *Net Monetary Return*:

$$
\Pi(R, K) = R - K.
$$

2. *Factor-A Outlay Ratio*: The relative share of factor $A$ in total cost, compared across techniques by $K_{A, \text{old}} \cdot K_{B, \text{new}} < K_{A, \text{new}} \cdot K_{B, \text{old}}$.
3. *Return-to-Cost Ratio*: The relative profitability $\Pi / K$, compared across two viable techniques ($K \le R$ and $0 < K$) by the exact cross-multiplied inequality:

$$
\Pi_{\text{old}} \cdot K_{\text{new}} < \Pi_{\text{new}} \cdot K_{\text{old}}.
$$

### Proposition 9.29 (Cost-Reducing Factor Substitution Raises Net Return and Return Ratio)
Suppose a production technique substitutes factor $A$ for factor $B$ ($K_{A, \text{old}} < K_{A, \text{new}}$ and $K_{B, \text{new}} < K_{B, \text{old}}$) while strictly reducing total monetary input cost ($K_{\text{new}} < K_{\text{old}}$) for at least the same gross revenue ($R_{\text{old}} \le R_{\text{new}}$). Then the factor-$A$ outlay ratio, the net monetary return, and the return-to-cost ratio all strictly increase:

$$
\Pi_{\text{old}} < \Pi_{\text{new}} \quad \wedge \quad \Pi_{\text{old}} \cdot K_{\text{new}} < \Pi_{\text{new}} \cdot K_{\text{old}}.
$$

Furthermore, if factor outlays subsequently adjust downward ($`K'_{A} \le K_{A, \text{new}}`$ and $`K'_{B} \le K_{B, \text{new}}`$) while preserving revenue ($R_{\text{old}} \le R'$), total cost remains strictly below $K_{\text{old}}$ and the return ratio strictly exceeds the initial ratio.

**Proof.** The product inequality for the factor-$A$ ratio follows from multiplying $K_{A, \text{old}} < K_{A, \text{new}}$ by $K_{B, \text{new}} \le K_{B, \text{old}}$. Net return rises because $R_{\text{old}} - K_{\text{old}} < R_{\text{new}} - K_{\text{new}}$ whenever $K_{\text{new}} < K_{\text{old}}$ and $R_{\text{old}} \le R_{\text{new}}$. Cross-multiplying $\Pi_{\text{old}} \cdot K_{\text{new}} < \Pi_{\text{new}} \cdot K_{\text{new}} \le \Pi_{\text{new}} \cdot K_{\text{old}}$ establishes the strictly higher return ratio. Downstream factor price adjustment satisfies $K' \le K_{\text{new}} < K_{\text{old}}$, preserving the strict return ratio inequality. $\blacksquare$

A physical antichain can therefore have comparable monetary costs. [Proposition 9.27](#proposition-927-comparability-of-monetary-costs) and [Proposition 9.29](#proposition-929-cost-reducing-factor-substitution-raises-net-return-and-return-ratio) supply the input-cost and net-return comparisons for given prices; ranking whole production plans composes that comparison with outputs, maturation, and uncertainty.

Could the actor construct the same comparison without factor prices by assigning numbers to the ends forgone? A strict preference order is unchanged when its elements are replaced by any order-preserving numerical labels. We test the proposed addition of ranks by keeping the ranking fixed and changing only those labels. If the sum comparison reverses, the ranking alone cannot determine it.

### Theorem 9.30 (The Socialist Incommensurability Antichain Theorem)
*The strict order of four ends does not determine the comparison between the sums of numerical ranks assigned to two bundles of those ends.*

**Proof.** Let $`e_0 \succ e_1 \succ e_2 \succ e_3`$. Assign ranks first by $`\varphi_1 = (10, 4, 3, 1)`$ and then by $`\varphi_2 = (10, 9, 8, 1)`$. Both assignments preserve the same strict ranking. For bundles $`A = \{e_0, e_3\}`$ and $`B = \{e_1, e_2\}`$,

$$
\sum_{e \in A}\varphi_1(e) = 11 > 7 = \sum_{e \in B}\varphi_1(e)
$$

whereas

$$
\sum_{e \in A}\varphi_2(e) = 11 < 17 = \sum_{e \in B}\varphi_2(e)
$$

The ordinal order is unchanged while the sum comparison reverses. Hence that comparison is not determined by the ordinal order. $\blacksquare$

The difficulty arises before computational optimization: a sum of arbitrary ranks has not supplied an invariant cost measure. The information argument below strengthens this observation from a particular additive procedure to all decision rules using a specified restricted record.

---

## Mises: The Economic Calculation Problem

A calculation rule can use only the information supplied to it. The first formulation below states a conditional baseline: it takes two action-frame economy records with the same restricted record and opposite marginal preferences as hypotheses, without yet constructing those economies or deriving their records from an institutional ownership regime.

### Definition 9.31 (Action Frame Socialist Economy and Preserved Marginal End)
In an action frame $W$, an *action frame socialist economy* $E$ at decision context $(i, t, h)$ stores two distinct means $m_A \neq m_B$, two distinct ends $e_A \neq e_B$, two input vectors $x_A, x_B \in \mathbb{N}^2$, a report $`R : \{0, 1\} \to \mathbb{N}`$, and means bundles $b_A, b_B$ with a stipulated subjective teleological dominance relation. The structure does not establish that the vectors are feasible actions. Its observable record is:

$$
\mathcal{O}(E) = (x_A, x_B, R).
$$

The report field is an arbitrary natural-number pair. Its name does not constrain its contents to physical statistics: it could encode a preference. The observable projection discards the economy's preference field, and the theorem separately assumes that the two reports agree. Define the end preserved by technique $x$ to be $e_A$ if $x_0 \le x_1$, and $e_B$ otherwise. This is a convention of the model, not a consequence of production or opportunity costs.

A technique choice violates the defined economizing condition if the other stored input vector preserves a strictly preferred end. A rule selects one of the two vectors as a function of $\mathcal{O}(E)$ alone.

### Theorem 9.32 (Conditional Calculation under Indistinguishable Records)
Suppose two supplied action-frame economy records have identical input vectors, reports, and named ends, but opposite stipulated preferences. Suppose also that the two input vectors preserve opposite ends under the model's convention. Then every deterministic rule based only on their common observable record violates the defined economizing condition in at least one record.

**Proof.** The stipulated subjective dominance and action-frame bridge yield $e_A \succ e_B$ in $E_1$ and $e_B \succ e_A$ in $E_2$. The preservation hypotheses say that choosing $A$ violates economizing in $E_1$, while choosing $B$ violates it in $E_2$.

The matching-method and matching-report hypotheses give $\mathcal{O}(E_1) = \mathcal{O}(E_2)$, so a rule depending only on that record returns the same choice in both economies. If it chooses $A$, it fails in the first; if it chooses $B$, it fails in the second. These exhaust the rule's two possible outputs. The physical-antichain hypothesis is returned in the theorem's conclusion but is not used in this rule argument. $\blacksquare$

[Theorem 9.32](#theorem-932-conditional-calculation-under-indistinguishable-records) establishes a conditional information boundary, taking two economies and their disagreement as supplied premises. To construct those economies from physical reality and institutional accounting without assuming the conclusion, we now proceed in six intuitive stages: (1) isolate the general information-problem and strategic reporting structure; (2) define the operational transition laws of public production, personal labor-certificate ledgers, administered quote tables, and voluntary spot settlement; (3) build one shared finite physical economy and ground its downstream evaluations inside two branching action frames; (4) prove impossibility for the restricted pre-commitment labor-voucher, input-output/administered-price, multi-round transcript, zero-queue quote, and price-box interfaces; (5) delimit the boundary through six positive controls and an exact capital antichain equivalence; and (6) analyze worker effort incentives under flat clock-hour vouchers.

---

## Observation Maps, Solvability, and Strategic Reporting Protocols

Before modeling specific ledgers, we separate the pure question of whether a public record contains enough information from whether an institution generates or withholds that information. Notice that an information-problem theorem is a property of maps and fibers alone; ownership and institutions enter only when we construct the states, acceptability condition, and observation maps from actual rules.

### Definition 9.33 (Restricted Information Problem and Deterministic Solvability)
An **information problem** $\mathcal{P} = (\mathcal{S}, \mathcal{R}, \mathcal{D}, \mathcal{O}, \mathrm{Acc})$ consists of:
1. A state space $\mathcal{S}$ capturing the underlying economic facts (including private consumer valuations);
2. A record space $\mathcal{R}$ and an **observation map** $\mathcal{O} : \mathcal{S} \to \mathcal{R}$ mapping each state to the public record available at the decision node;
3. A decision space $\mathcal{D}$ and an observation-independent **acceptability relation** $\mathrm{Acc} \subseteq \mathcal{S} \times \mathcal{D}$ specifying which decisions succeed in economizing in each state.

A deterministic rule $\rho : \mathcal{R} \to \mathcal{D}$ **solves** $\mathcal{P}$ if it selects an acceptable decision in every state:

$$
\forall s \in \mathcal{S}, \quad \mathrm{Acc}\bigl(s, \rho(\mathcal{O}(s))\bigr).
$$

The problem $\mathcal{P}$ is **solvable** if such a rule $\rho$ exists.

### Lemma 9.34 (Fiberwise Characterization of Solvable Information Problems and Full-Information Control)
Let $\mathcal{P} = (\mathcal{S}, \mathcal{R}, \mathcal{D}, \mathcal{O}, \mathrm{Acc})$ be an information problem.
1. (*Fiberwise Solvability*): $\mathcal{P}$ is solvable if and only if every realized record admits one common acceptable decision across its entire fiber:

$$
\mathrm{Solvable}(\mathcal{P}) \quad \Longleftrightarrow \quad \forall r \in \mathcal{R},\ \bigl((\exists s \in \mathcal{S},\ \mathcal{O}(s) = r) \implies \exists d \in \mathcal{D},\ \forall s \in \mathcal{S},\ \mathcal{O}(s) = r \implies \mathrm{Acc}(s, d)\bigr).
$$

2. (*Full-Information Control*): If $\mathcal{D}$ is inhabited and $\forall s \in \mathcal{S},\ \exists d \in \mathcal{D},\ \mathrm{Acc}(s, d)$, then the full-observation problem $`\mathcal{P}_{\mathrm{id}} = (\mathcal{S}, \mathcal{S}, \mathcal{D}, \mathrm{id}, \mathrm{Acc})`$ is solvable.

**Proof.** For Part 1 ($\implies$), if $\rho$ solves $\mathcal{P}$ and $\mathcal{O}(s_0) = r$, take $d = \rho(r)$; then for every $s$ with $\mathcal{O}(s) = r$, $\mathrm{Acc}(s, d) = \mathrm{Acc}(s, \rho(\mathcal{O}(s)))$ holds. For ($\Longleftarrow$), on each realizable record $r$ choose a witness $`d_r`$ acceptable throughout the fiber $\mathcal{O}^{-1}(r)$, and outside $\mathrm{im}(\mathcal{O})$ map $r$ to a default element of $\mathcal{D}$ (when $\mathcal{S}$ is empty solvability is vacuous; when $\mathcal{S}$ is nonempty some $`s_0`$ realizes a fiber witness). Then for every $s \in \mathcal{S}$, $`d_{\mathcal{O}(s)}`$ satisfies $`\mathrm{Acc}(s, d_{\mathcal{O}(s)})`$.

For Part 2, take the rule choosing for each $s \in \mathcal{S}$ a decision $d(s)$ with $\mathrm{Acc}(s, d(s))$; since $\mathcal{O}(s) = s$, this directly solves $`\mathcal{P}_{\mathrm{id}}`$. $\blacksquare$

Equal records alone cause no obstruction if the same decision works in every state sharing that record. Impossibility requires two states in the same observation fiber whose acceptable sets are disjoint.

### Theorem 9.35 (Calculation Impossibility under Conflicting Indistinguishable States)
Suppose an information problem $\mathcal{P} = (\mathcal{S}, \mathcal{R}, \mathcal{D}, \mathcal{O}, \mathrm{Acc})$ admits two states $s, t \in \mathcal{S}$ with identical records and disjoint acceptable decision sets:

$$
\mathcal{O}(s) = \mathcal{O}(t) \quad \wedge \quad \forall d \in \mathcal{D},\ \neg\bigl(\mathrm{Acc}(s, d) \wedge \mathrm{Acc}(t, d)\bigr).
$$

Then $\mathcal{P}$ is unsolvable: $\neg \mathrm{Solvable}(\mathcal{P})$.

**Proof.** Suppose toward a contradiction that $\rho : \mathcal{R} \to \mathcal{D}$ solves $\mathcal{P}$. Let $d^{\ast} = \rho(\mathcal{O}(s))$. By correctness on $s$, $\mathrm{Acc}(s, d^{\ast})$ holds. Since $\mathcal{O}(s) = \mathcal{O}(t)$, we also have $\rho(\mathcal{O}(t)) = d^{\ast}$, so correctness on $t$ yields $\mathrm{Acc}(t, d^{\ast})$. Both $\mathrm{Acc}(s, d^{\ast})$ and $\mathrm{Acc}(t, d^{\ast})$ hold simultaneously, contradicting disjointness. $\blacksquare$

Notice that an observation problem studies what a planner can infer from a given record map $\mathcal{O}$, whereas a strategic reporting protocol studies what reports self-interested managers or agents choose to submit when physical reality depends on true private endowments and capacities rather than unverified announcements.

### Definition 9.36 (Strategic Reporting Protocol, Dominant Truthfulness, and Full Pareto Implementation)
A one-round **strategic reporting protocol** over an agent set $\mathcal{I}$ specifies for each $i \in \mathcal{I}$ a private type space $\Theta_i$, a local observable view space $V_i$ with realized view $v_i \in V_i$, and a report alphabet $M_i$, together with:
1. An instruction function $\mathrm{inst} : \bigl(\prod_{i \in \mathcal{I}} M_i\bigr) \to \mathrm{Inst}$ mapping submitted reports alone (with no access to private states) to a plan instruction;
2. A physical execution map $\mathrm{exec} : \bigl(\prod_{i \in \mathcal{I}} \Theta_i\bigr) \times \mathrm{Inst} \to \mathcal{X}$ mapping the *true* private profile and the instruction to a physical outcome, with physical feasibility predicate $\mathrm{feas}(\theta, x)$;
3. For each $\theta$ and agent $i$, a reflexive, transitive weak preference relation $`x \succsim_{\theta, i} y`$ on $\mathcal{X}$, with strict part $`x \succ_{\theta, i} y :\iff x \succsim_{\theta, i} y \wedge \neg(y \succsim_{\theta, i} x)`$.

A **strategy profile** assigns to each agent a function $\sigma_i : \Theta_i \to V_i \to M_i$, generating reports $`m(\theta, \sigma)_i = \sigma_i(\theta_i, v_i)`$ and outcome $\mathrm{res}(\theta, \sigma) = \mathrm{exec}(\theta, \mathrm{inst}(m(\theta, \sigma)))$. For any report vector $r$, agent $i$, and alternative report $r_i' \in M_i$, let $`(r_{-i}, r_i')`$ denote replacing $i$'s coordinate with $r_i'$. We define:
- **Ex-Post Equilibrium:** $\sigma$ is an ex-post equilibrium if no unilateral report deviation can improve over $\sigma$ at any true type profile:

$$
\forall \theta, \forall i \in \mathcal{I}, \forall r_i' \in M_i, \quad \mathrm{res}(\theta, \sigma) \succsim_{\theta, i} \mathrm{exec}\bigl(\theta, \mathrm{inst}(m(\theta, \sigma)_{-i}, r_i')\bigr).
$$

- **Dominant Truthfulness:** Relative to a truthful revelation map $`\mathrm{rev}_i : \Theta_i \to M_i`$, truth-telling is dominant if for every profile of others' reports $`r_{-i}`$:

$$
\forall \theta, \forall r, \forall i \in \mathcal{I}, \forall r_i' \in M_i, \quad \mathrm{exec}\bigl(\theta, \mathrm{inst}(r_{-i}, \mathrm{rev}_i(\theta_i))\bigr) \succsim_{\theta, i} \mathrm{exec}\bigl(\theta, \mathrm{inst}(r_{-i}, r_i')\bigr).
$$

- **Pareto Efficiency and Full Pareto Implementation:** An outcome $x$ is **Pareto efficient** at $\theta$ if $\mathrm{feas}(\theta, x)$ holds and there is no feasible $y$ with $`y \succsim_{\theta, i} x`$ for all $i$ and $`y \succ_{\theta, j} x`$ for some $j$. The protocol **fully implements Pareto efficiency** if at least one ex-post equilibrium exists and every ex-post equilibrium yields a Pareto-efficient outcome for every true type profile $\theta$.

### Proposition 9.37 (Truthful Dominant Equilibrium and Equilibrium Necessity for Implementation)
In any strategic reporting protocol:
1. If $\mathrm{rev}$ is dominant truthful, then the truthful strategy $`\sigma_i^{\mathrm{tr}}(\theta_i, v) = \mathrm{rev}_i(\theta_i)`$ is an ex-post equilibrium.
2. Full Pareto implementation entails the existence of an ex-post equilibrium (so a mechanism without any equilibrium cannot pass vacuously).

**Proof.** For Part 1, substituting $r = m(\theta, \sigma^{\mathrm{tr}})$ gives $`(r_{-i}, \mathrm{rev}_i(\theta_i)) = m(\theta, \sigma^{\mathrm{tr}})`$, so dominant truthfulness yields $`\mathrm{res}(\theta, \sigma^{\mathrm{tr}}) \succsim_{\theta, i} \mathrm{exec}(\theta, \mathrm{inst}(m(\theta, \sigma^{\mathrm{tr}})_{-i}, r_i'))`$ for all $\theta, i, r_i'$. Part 2 is immediate from the conjunction defining full implementation. $\blacksquare$

### Proposition 9.38 (Managerial Payoff Insensitivity and Babbling Equilibria)
Call a reporting protocol **report-payoff-insensitive** if varying agent $i$'s own report leaves agent $i$ weakly indifferent across every resulting outcome:

$$
\forall \theta, \forall r, \forall i \in \mathcal{I}, \forall r_1, r_2 \in M_i, \quad \mathrm{exec}\bigl(\theta, \mathrm{inst}(r_{-i}, r_1)\bigr) \succsim_{\theta, i} \mathrm{exec}\bigl(\theta, \mathrm{inst}(r_{-i}, r_2)\bigr).
$$

Under report payoff insensitivity:
1. For every fixed report profile $`\bar{r}`$, the type-independent **babbling strategy** $`\sigma_i^{\mathrm{const}}(\theta_i, v) = \bar{r}_i`$ is an ex-post equilibrium.
2. Truthful reporting $`\mathrm{rev}_i(\theta_i)`$ is never strictly preferred to any arbitrary alternative report $r_i'$:

$$
\neg \Bigl(\mathrm{exec}\bigl(\theta, \mathrm{inst}(r_{-i}, \mathrm{rev}_i(\theta_i))\bigr) \succ_{\theta, i} \mathrm{exec}\bigl(\theta, \mathrm{inst}(r_{-i}, r_i')\bigr)\Bigr).
$$

**Proof.** For Part 1, $`(m(\theta, \sigma^{\mathrm{const}})_{-i}, \bar{r}_i) = m(\theta, \sigma^{\mathrm{const}})`$, so applying payoff insensitivity with $`r_1 = \bar{r}_i`$ and $r_2 = r_i'$ immediately establishes the ex-post equilibrium condition. For Part 2, strict preference requires $`\neg(y \succsim_{\theta, i} x)`$, which is contradicted directly by report payoff insensitivity with $r_1 = r_i'$ and $`r_2 = \mathrm{rev}_i(\theta_i)`$. $\blacksquare$

---

## Institutional Ledgers: Public Production, Labor Certificates, Administered Quotes, and Spot Settlement

To evaluate labor vouchers, input-output matrices, administered prices, and market settlement without ambiguity, we define exact ledger state transitions in which real capacities, physical inventories, and certificate synchronization cannot be bypassed by verbal decrees.

### Definition 9.39 (Public Production Ledger and Physical Execution Semantics)
Keep real consumption and labor hours separate from nominal token counters: a **real outcome** records personal physical consumption $c(p, g) \in \mathbb{N}$, labor hours $\ell(p) \in \mathbb{N}$, and residual physical stock $s(g) \in \mathbb{N}$. A **public production ledger** $`E = (\mathrm{stock}, \mathrm{cap}, \mathrm{in}, \mathrm{out}, \ell_{\mathrm{task}}, \mathrm{Auth})`$ over managers $m$, goods $g$, and tasks $\tau$ records public stock $\mathrm{stock}(g) \in \mathbb{N}$, manager-task capacity $\mathrm{cap}(m, \tau) \in \mathbb{N}$, per-run physical input $\mathrm{in}(\tau, g) \in \mathbb{N}$, per-run physical output $\mathrm{out}(\tau, g) \in \mathbb{N}$, per-run verified labor hours $`\ell_{\mathrm{task}}(\tau) \in \mathbb{N}`$, and legal authorization $\mathrm{Auth}(m, \tau)$.

A proposed execution of $r \in \mathbb{N}$ runs of task $\tau$ by manager $m$ is **physically and legally executable**, denoted $\mathrm{CanExec}(E, m, \tau, r)$, when:

$$
\mathrm{Auth}(m, \tau) \quad \wedge \quad r \le \mathrm{cap}(m, \tau) \quad \wedge \quad \forall g,\ r \cdot \mathrm{in}(\tau, g) \le \mathrm{stock}(g).
$$

The resulting physical stock $\mathrm{exec}(E, m, \tau, r)$ updates every good by integer conservation whenever executable, and otherwise leaves stocks unchanged:

$$
\mathrm{exec}(E, m, \tau, r)(g) =
\begin{cases}
\mathrm{stock}(g) - r \cdot \mathrm{in}(\tau, g) + r \cdot \mathrm{out}(\tau, g) & \text{if } \mathrm{CanExec}(E, m, \tau, r), \\
\mathrm{stock}(g) & \text{otherwise}.
\end{cases}
$$

Potential verified labor hours equal $`r \cdot \ell_{\mathrm{task}}(\tau)`$ if $\mathrm{CanExec}(E, m, \tau, r)$ holds, and $0$ otherwise.

### Lemma 9.40 (Monotonicity of Execution Feasibility and Conservation under Rejected Runs)
1. (*Progress Preservation*): If a new public production ledger $E'$ weakly expands legal authorizations ($\mathrm{Auth} \subseteq \mathrm{Auth}'$), task capacities ($\mathrm{cap} \le \mathrm{cap}'$), and public stocks ($\mathrm{stock} \le \mathrm{stock}'$) while preserving input recipes ($\mathrm{in}' = \mathrm{in}$), then every previously executable run satisfies $\mathrm{CanExec}(E', m, \tau, r)$.
2. (*Rejected Run Invariance*): Whenever $\neg \mathrm{CanExec}(E, m, \tau, r)$, potential verified labor hours are $0$ and $\mathrm{exec}(E, m, \tau, r) = E.\mathrm{stock}$.

**Proof.** Part 1 follows by transitivity of $\le$ on capacities and stocks, using unchanged input coefficients. Part 2 follows immediately from the two conditional definitions when $\mathrm{CanExec}(E, m, \tau, r)$ fails. $\blacksquare$

### Definition 9.41 (Personal Labor-Certificate Ledger and Stock-Synchronized Work Ledger)
A **personal certificate ledger** $S = (\mathrm{bal}, \mathrm{stock}, \mathrm{cons})$ records each person's non-transferable certificate balance $\mathrm{bal}(p) \in \mathbb{N}$, public consumer stock $\mathrm{stock}(g) \in \mathbb{N}$, and personal redeemed consumption $\mathrm{cons}(p, g) \in \mathbb{N}$. Two primitive operations govern $S$:
1. **Certificate Issuance:** Crediting $`h_{\mathrm{ver}}`$ verified labor hours minus deduction $d$ updates person $p$'s balance to $`\mathrm{bal}(p) + (h_{\mathrm{ver}} - d)`$, leaving every other person's balance, stock, and past consumption unchanged (here $a - b$ denotes truncated natural subtraction $\max(a - b, 0)$ ).
2. **Certificate Redemption:** Given certificate prices $c(g) \in \mathbb{N}$, redeeming $q$ units of good $g$ by person $p$, denoted $\mathrm{redeem}(S, c, p, g, q)$, executes if and only if $q \le S.\mathrm{stock}(g) \wedge c(g) \cdot q \le S.\mathrm{bal}(p)$; in that case it sets $\mathrm{bal}'(p) = \mathrm{bal}(p) - c(g) \cdot q$, $\mathrm{stock}'(g) = \mathrm{stock}(g) - q$, and $\mathrm{cons}'(p, g) = \mathrm{cons}(p, g) + q$ (extinguishing the redeemed certificates); otherwise it leaves $S$ unchanged.

A **work ledger** $L = (E, S)$ couples a public production state $E$ with a personal certificate state $S$ via two atomic operations that enforce stock synchronization ($S.\mathrm{stock} = E.\mathrm{stock}$):
- $\mathrm{execAndIssue}(L, p, \tau, r, d)$ checks $S.\mathrm{stock} = E.\mathrm{stock} \wedge \mathrm{CanExec}(E, p, \tau, r)$. If satisfied, it computes $\mathrm{stock}' = \mathrm{exec}(E, p, \tau, r)$, decrements remaining task capacity $\mathrm{cap}(p, \tau)$ by $r$, issues $`(r \cdot \ell_{\mathrm{task}}(\tau)) - d`$ certificates to $p$, and updates both $E.\mathrm{stock}$ and $S.\mathrm{stock}$ to $\mathrm{stock}'$; otherwise it leaves $L$ unchanged.
- $`\mathrm{redeem}_L(L, c, p, g, q)`$ checks $S.\mathrm{stock} = E.\mathrm{stock}$. If satisfied, it computes $S' = \mathrm{redeem}(S, c, p, g, q)$ and updates $E.\mathrm{stock} := S'.\mathrm{stock}$ atomically so consumer redemption never leaves the production stock ledger stale; otherwise it leaves $L$ unchanged.

### Proposition 9.42 (Capacity Exhaustion, Stock Synchronization, and Redemption Conservation)
Let $L = (E, S)$ be a work ledger, $p$ a worker, $\tau$ a task, and $r > 0$.
1. Issuance preserves $\mathrm{bal}(p')$ for all $p' \neq p$ and updates $\mathrm{bal}(p)$ to $`\mathrm{bal}(p) + (h_{\mathrm{ver}} - d)`$.
2. If $S.\mathrm{stock} \neq E.\mathrm{stock}$ or $\neg \mathrm{CanExec}(E, p, \tau, r)$, then $\mathrm{execAndIssue}(L, p, \tau, r, d) = L$. If both checks hold, remaining capacity becomes $\mathrm{cap}(p, \tau) - r$; in particular, when $r = \mathrm{cap}(p, \tau) > 0$, remaining capacity falls to $0$ and the same run $r$ cannot be repeated ($\neg \mathrm{CanExec}$).
3. Unfunded certificate redemption leaves $S$ unchanged. Funded certificate redemption ( $q \le S.\mathrm{stock}(g)$ and $c(g) \cdot q \le S.\mathrm{bal}(p)$ ) conserves both physical consumer goods and certificate claims:

$$
S'.\mathrm{stock}(g) + S'.\mathrm{cons}(p, g) = S.\mathrm{stock}(g) + S.\mathrm{cons}(p, g), \qquad S'.\mathrm{bal}(p) + c(g) \cdot q = S.\mathrm{bal}(p).
$$

4. Both $\mathrm{execAndIssue}$ and $`\mathrm{redeem}_L`$ preserve the stock-synchronization invariant $S.\mathrm{stock} = E.\mathrm{stock}$, and synchronized funded redemption satisfies stock-plus-consumption conservation on $L$.

**Proof.** Parts 1 and 2 follow directly by unfolding issuance and $\mathrm{execAndIssue}$: once $r = \mathrm{cap}(p, \tau) > 0$, updated capacity is $r - r = 0 < r$, violating the capacity bound in $\mathrm{CanExec}$. Part 3 holds by exact integer identity $(x - q) + (y + q) = x + y$ for $q \le x$ and $(b - c(g)q) + c(g)q = b$ for $c(g)q \le b$. Part 4 follows because both synchronized transitions write the identical updated stock function into both components of $L$. $\blacksquare$

### Definition 9.43 (Administered Price-Adjustment Ledger and Voluntary Spot Settlement)
1. An **administered price state** $A = (\mathrm{price}, \mathrm{stock})$ pairs a planning board's accounting quote $\mathrm{price}(g) \in \mathbb{N}$ with a stock schedule $\mathrm{stock}(g) \in \mathbb{N}$. A demand schedule $D : \mathcal{G} \to \mathbb{N}$ **clears** $A$, denoted $\mathrm{clear}(A, D)$, when $\forall g,\ D(g) = \mathrm{stock}(g)$. Given a ceiling $\bar{p} \in \mathbb{N}$, one bounded **tâtonnement adjustment step** $\mathrm{adjust}(A, \bar{p}, D)$ updates quotes by:

$$
\mathrm{price}'(g) =
\begin{cases}
\min\bigl(\bar{p}, \mathrm{price}(g) + 1\bigr) & \text{if } \mathrm{stock}(g) < D(g), \\
\mathrm{price}(g) - 1 & \text{if } D(g) < \mathrm{stock}(g), \\
\mathrm{price}(g) & \text{if } D(g) = \mathrm{stock}(g).
\end{cases}
$$

2. A **bilateral spot state** records seller stock $`\mathrm{stock}_S`$, buyer stock $`\mathrm{stock}_B`$, buyer cash $`\mathrm{cash}_B`$, and seller cash $`\mathrm{cash}_S`$. For quantity $q$, total payment $P$, and assent flags $`(\mathrm{offer}, \mathrm{accept}) \in \{\mathrm{false}, \mathrm{true}\}^2`$, **spot settlement** $\mathrm{settle}(q, P, \mathrm{offer}, \mathrm{accept})$ executes the exchange $`(\mathrm{stock}_S - q,\ \mathrm{stock}_B + q,\ \mathrm{cash}_B - P,\ \mathrm{cash}_S + P)`$ if $`\mathrm{offer} \wedge \mathrm{accept} \wedge q \le \mathrm{stock}_S \wedge P \le \mathrm{cash}_B`$, and otherwise leaves all four balances unchanged.

### Proposition 9.44 (Balanced Quote Invariance, Price-Ceiling Stalls, and Spot Conservation)
1. (*Balanced Quote Invariance*): Whenever $\mathrm{clear}(A, D)$ holds, $\mathrm{adjust}(A, \bar{p}, D).\mathrm{price} = A.\mathrm{price}$.
2. (*Ceiling Stall*): If $\mathrm{price}(g) = \bar{p}$ and $\mathrm{stock}(g) < D(g)$, then $\mathrm{adjust}(A, \bar{p}, D).\mathrm{price}(g) = A.\mathrm{price}(g)$ even though $\neg \mathrm{clear}(A, D)$. Price stability at a binding cap does not imply clearing.
3. (*Assent and Spot Conservation*): If either party withholds assent ($\mathrm{offer} = \mathrm{false}$ or $\mathrm{accept} = \mathrm{false}$), spot settlement leaves the state unchanged. Whenever settlement executes, total goods and total cash are conserved:

$$
\mathrm{stock}_S' + \mathrm{stock}_B' = \mathrm{stock}_S + \mathrm{stock}_B, \qquad \mathrm{cash}_B' + \mathrm{cash}_S' = \mathrm{cash}_B + \mathrm{cash}_S.
$$

**Proof.** Part 1 unfolds $\mathrm{adjust}$ at $D(g) = \mathrm{stock}(g)$. Part 2 holds because $\min(\bar{p}, \bar{p} + 1) = \bar{p}$ while $\mathrm{stock}(g) < D(g)$ contradicts $D(g) = \mathrm{stock}(g)$. Part 3 checks both branches of settlement: failed assent triggers the unchanged branch, while successful settlement satisfies $`q \le \mathrm{stock}_S`$ and $`P \le \mathrm{cash}_B`$, yielding integer conservation by arithmetic cancellation. $\blacksquare$

---

## The Shared Physical Calculation Economy and Action-Frame Grounding

Rather than stipulating two unconnected worlds or an exogenous preserved-end convention, we construct one concrete finite physical economy and derive every residual balance, irreversible setup exclusion, downstream feasibility branch, and purposeful action inside an explicit branching action frame.

### Definition 9.45 (The Shared Physical Calculation Economy and Common Executed Prefix)
Consider a finite physical economy with:
- **Goods** ($\mathcal{G}$): Capital factors $K_1, K_2$, a non-renewable setup factor $\mathrm{setup}$, intermediate target output $Q$, finished consumer goods $C_1, C_2$, and a pre-commitment consumer good $\mathrm{preGood}$;
- **Tasks** ($\mathcal{T}$) **and Techniques**: A pre-commitment prefix task $`\tau_{\mathrm{pre}}`$, two competing target techniques $\tau_A, \tau_B$ producing $Q$, and two downstream finishing tasks $D_1, D_2$, alongside the downstream passive choice $\mathrm{idle}$.
- **Physical Recipes and Labor Hours:** Every task requires $1$ labor hour and is authorized for every manager with unit capacity $1$; shared post-prefix labor capacity is $2$ hours (sufficient for one target technique plus one downstream finishing step). Nonzero physical input requirements $u(\tau, g)$ and outputs $y(\tau, g)$ are:

| Task $\tau$ | Inputs $u(\tau, \cdot)$ | Outputs $y(\tau, \cdot)$ | Labor Hours |
|---|---|---|---|
| $`\tau_{\mathrm{pre}}`$ | none | $1\;\mathrm{preGood}$ | $1$ |
| $\tau_A$ (Method $A$ ) | $`2\,K_1,\ 1\,K_2,\ 1\,\mathrm{setup}`$ | $`1\,Q`$ | $1$ |
| $\tau_B$ (Method $B$ ) | $`1\,K_1,\ 2\,K_2,\ 1\,\mathrm{setup}`$ | $`1\,Q`$ | $1$ |
| $D_1$ | $`1\,K_1`$ | $`1\,C_1`$ | $1$ |
| $D_2$ | $`1\,K_2`$ | $`1\,C_2`$ | $1$ |

- **Initial Endowment and Executed Prefix:** Initial physical stock is $(K_1, K_2, \mathrm{setup}, Q, C_1, C_2, \mathrm{preGood}) = (2, 2, 1, 0, 0, 0, 0)$ with zero initial certificates and zero redemptions. Before private downstream consumer valuations arrive, the economy executes a two-step common prefix:
  1. Execute $1$ run of $`\tau_{\mathrm{pre}}`$ via $\mathrm{execAndIssue}$ (deduction $0$ ), producing $1\;\mathrm{preGood}$ and issuing $1$ labor certificate;
  2. Redeem $1\;\mathrm{preGood}$ at certificate price $1$ via atomic $`\mathrm{redeem}_L`$, extinguishing the certificate and yielding the **pre-commitment work ledger** $`L_{\mathrm{pre}}`$.

### Lemma 9.46 (Pre-Commitment Residual Stocks, Exhausted Prefix Capacity, and Initial Technique Feasibility)
After executing and redeeming the common prefix, the pre-commitment work ledger $`L_{\mathrm{pre}}`$ is stock-synchronized ($S.\mathrm{stock} = E.\mathrm{stock}$) and satisfies:
1. Residual physical stocks are $(K_1, K_2, \mathrm{setup}, Q, C_1, C_2, \mathrm{preGood}) = (2, 2, 1, 0, 0, 0, 0)$, certificate balance is $0$, and completed consumer redemptions equal $1$ unit of $\mathrm{preGood}$;
2. Remaining capacities are $0$ for $`\tau_{\mathrm{pre}}`$ and $1$ each for $\tau_A, \tau_B, D_1, D_2$;
3. Both target techniques satisfy $`\mathrm{CanExec}(L_{\mathrm{pre}}.E, \cdot, \tau_A, 1)`$ and $`\mathrm{CanExec}(L_{\mathrm{pre}}.E, \cdot, \tau_B, 1)`$.

**Proof.** Initially $(K_1, K_2, \mathrm{setup}, \mathrm{preGood}) = (2, 2, 1, 0)$ and $`\tau_{\mathrm{pre}}`$ requires no inputs, so $`\tau_{\mathrm{pre}}`$ is feasible at capacity $1$. By [Proposition 9.42](#proposition-942-capacity-exhaustion-stock-synchronization-and-redemption-conservation), running $\mathrm{execAndIssue}$ raises $\mathrm{preGood}$ to $1$, raises the certificate balance to $1$, reduces $`\tau_{\mathrm{pre}}`$ capacity to $0$, and preserves stock synchronization; applying $`\mathrm{redeem}_L`$ burns $1$ certificate, reduces $\mathrm{preGood}$ back to $0$, records $\mathrm{cons}(\mathrm{preGood}) = 1$, and keeps stock synchronization intact. Checking the recipe inputs for $\tau_A$ ( $`2\,K_1 + 1\,K_2 + 1\,\mathrm{setup}`$ ) and $\tau_B$ ( $`1\,K_1 + 2\,K_2 + 1\,\mathrm{setup}`$ ) against $(2, 2, 1)$ verifies $\mathrm{CanExec}$ for both methods. $\blacksquare$

### Proposition 9.47 (Irreversible Technique Execution, Setup Depletion, and Downstream Affordability)
Let $`L_m = \mathrm{execAndIssue}(L_{\mathrm{pre}}, \cdot, \tau_m, 1, 0)`$ denote the ledger after selecting target method $`m \in \{A, B\}`$.
1. (*Method Stock Conservation and Residuals*): For every good $g \in \mathcal{G}$, $`L_m.\mathrm{stock}(g) + u(\tau_m, g) = L_{\mathrm{pre}}.\mathrm{stock}(g) + y(\tau_m, g)`$. Explicitly:
   - Executing $A$ yields residual stocks $(K_1, K_2, \mathrm{setup}, Q, C_1, C_2) = (0, 1, 0, 1, 0, 0)$;
   - Executing $B$ yields residual stocks $(K_1, K_2, \mathrm{setup}, Q, C_1, C_2) = (1, 0, 0, 1, 0, 0)$.
2. (*Permanent Setup Exhaustion*): After executing $A$, running $B$ is physically infeasible ( $\neg \mathrm{CanExec}(L_A.E, \cdot, \tau_B, 1)$ ); after executing $B$, running $A$ is physically infeasible ( $\neg \mathrm{CanExec}(L_B.E, \cdot, \tau_A, 1)$ ).
3. (*Derived Downstream Feasibility and Terminal Outcomes*):
   - After $A$, $\mathrm{idle}$ and $D_2$ are executable while $D_1$ is infeasible ( $\neg \mathrm{CanExec}(L_A.E, \cdot, D_1, 1)$ ), yielding $(C_1, C_2, Q) = (0, 0, 1)$ under $\mathrm{idle}$ and $(0, 1, 1)$ under $D_2$;
   - After $B$, $\mathrm{idle}$ and $D_1$ are executable while $D_2$ is infeasible ( $\neg \mathrm{CanExec}(L_B.E, \cdot, D_2, 1)$ ), yielding $(C_1, C_2, Q) = (0, 0, 1)$ under $\mathrm{idle}$ and $(1, 0, 1)$ under $D_1$.

**Proof.** Part 1 follows by unfolding $\mathrm{execAndIssue}$ on [Lemma 9.46](#lemma-946-pre-commitment-residual-stocks-exhausted-prefix-capacity-and-initial-technique-feasibility). Part 2 follows because both target techniques require $1$ unit of $\mathrm{setup}$, whereas $\mathrm{setup} = 0$ after either technique is executed. Part 3 checks $D_1$ ( $u(D_1, K_1) = 1$ ) and $D_2$ ( $u(D_2, K_2) = 1$ ) against residual $(K_1, K_2) = (0, 1)$ after $A$ and $(1, 0)$ after $B$, then computes the terminal stock from $\mathrm{exec}$. $\blacksquare$

Notice that no external field declares which end a technique preserves: residual feasibility and terminal attainment of $C_1$ vs. $C_2$ are derived purely by physical conservation and $\mathrm{CanExec}$. We now define private worlds and economizing acceptability independently of any observation map.

### Definition 9.48 (Private Downstream Valuation Worlds and Factor-Economizing Acceptability)
Let the private state space be $`\mathcal{W} = \{w_1, w_2\}`$, where $w_1$ values downstream consumer good $g(w_1) = C_1$ and $w_2$ values downstream consumer good $g(w_2) = C_2$.
- **Ordinal End-Attainment Preference:** For terminal physical bundles $b_1, b_2 : \mathcal{G} \to \mathbb{N}$, define strict preference $b_1 \succ_w b_2$ purely ordinally as attaining at least one unit of $w$'s valued good when the alternative attains none:

$$
b_1 \succ_w b_2 \quad :\Longleftrightarrow \quad 1 \le b_1(g(w)) \;\wedge\; b_2(g(w)) = 0.
$$

- **Observation-Independent Acceptability:** A method $`m \in \{A, B\}`$ is **initially feasible with required output $Q$** if $`\mathrm{CanExec}(L_{\mathrm{pre}}.E, \cdot, \tau_m, 1)`$ and $1 \le L_m.\mathrm{stock}(Q)$. Method $m$ is **acceptable** in world $w$, written $\mathrm{Acc}(w, m)$, if $m$ is feasible with output $Q$ and admits some feasible downstream continuation $`d \in \{\mathrm{idle}, D_1, D_2\}`$ whose terminal stock $\mathrm{term}(m, d)$ is undominated across all feasible pairs $(m', d')$:

$$
\mathrm{Acc}(w, m) \quad :\Longleftrightarrow \quad \exists d,\ \mathrm{DownFeas}(m, d) \;\wedge\; \forall m', d',\ \mathrm{Feas}(m', d') \implies \neg\bigl(\mathrm{term}(m', d') \succ_w \mathrm{term}(m, d)\bigr).
$$

### Theorem 9.49 (Unique Opposite Acceptable Techniques and World-Blind Reduction)
In the shared physical economy of [Definition 9.45](#definition-945-the-shared-physical-calculation-economy-and-common-executed-prefix):
1. Both methods $A$ and $B$ satisfy initial feasibility and produce $Q = 1$.
2. Evaluating all feasible downstream continuations characterizes acceptability uniquely in each world:

$$
\mathrm{Acc}(w_1, m) \iff m = B, \qquad \mathrm{Acc}(w_2, m) \iff m = A.
$$

3. Every world admits an acceptable method, and for any record type $\mathcal{R}$ and observation map $\mathcal{O} : \mathcal{W} \to \mathcal{R}$ satisfying $\mathcal{O}(w_1) = \mathcal{O}(w_2)$, the induced information problem $`(\mathcal{W}, \mathcal{R}, \{A, B\}, \mathcal{O}, \mathrm{Acc})`$ is unsolvable.

**Proof.** Part 1 holds by [Lemma 9.46](#lemma-946-pre-commitment-residual-stocks-exhausted-prefix-capacity-and-initial-technique-feasibility) and [Proposition 9.47](#proposition-947-irreversible-technique-execution-setup-depletion-and-downstream-affordability). For Part 2, in world $w_1$: after $A$, the only feasible downstream acts are $\mathrm{idle}$ and $D_2$, both yielding $C_1 = 0$, whereas $(B, D_1)$ is feasible and yields $C_1 = 1$, strictly preferred under $`\succ_{w_1}`$; hence $\neg \mathrm{Acc}(w_1, A)$. Conversely, $(B, D_1)$ achieves $C_1 = 1$, so no terminal bundle is strictly preferred under $`\succ_{w_1}`$, giving $\mathrm{Acc}(w_1, B)$. Symmetrically, in $w_2$ the feasible pair $(A, D_2)$ achieves $C_2 = 1$ while all feasible continuations after $B$ leave $C_2 = 0$, proving $\mathrm{Acc}(w_2, m) \iff m = A$. Part 3 applies [Theorem 9.35](#theorem-935-calculation-impossibility-under-conflicting-indistinguishable-states) since $\mathrm{Acc}(w_1, \cdot)$ and $\mathrm{Acc}(w_2, \cdot)$ are disjoint singletons $`\{B\}`$ and $`\{A\}`$. $\blacksquare$

To ensure the model respects full action-frame foundations without placing opposite current appraisals on histories sharing one decision node, we next embed the physical program into separate branching action frames for $w_1$ and $w_2$ and extract a ground action-frame witness.

### Theorem 9.50 (Branching Action-Frame Realization, Purposeful Downstream Execution, and Ground Witness)
For each world $`w \in \{w_1, w_2\}`$, compile a two-stage branching physical action frame $W(w)$ over the shared physical program whose Stage 0 menu is $`\{\mathrm{idle}, \tau_A, \tau_B\}`$ and whose Stage 1 menu after $p$ is $`\{\mathrm{idle}, D_2\}`$ when $p = \tau_A$, $`\{\mathrm{idle}, D_1\}`$ when $p = \tau_B$, and $`\{\mathrm{idle}, D_1, D_2\}`$ when $p = \mathrm{idle}$.
1. (*Menu Affordability and Physical Match*): Every Stage 0 and Stage 1 menu choice is physically affordable from the prior stage's state, and advancing Stage 0 under $\tau_m$ matches $L_m.\mathrm{stock}$ exactly.
2. (*Ordinal Preference Bridge*): On each frame $W(w)$, subjective teleological dominance with respect to the single valued end $(g(w), 1)$ coincides with strict ordinal world preference $\succ_w$.
3. (*Purposeful Downstream Completion*): Along the optimal history of $W(w_1)$ (choosing $\tau_B$ then $D_1$), downstream action $D_1$ is purposefully executed at the post-$B$ decision node, achieving $C_1 = 1$; along the optimal history of $W(w_2)$ (choosing $\tau_A$ then $D_2$), downstream action $D_2$ is purposefully executed at the post-$A$ decision node, achieving $C_2 = 1$.
4. (*Ground Baseline Witness*): Evaluating terminal outcomes from $`\{w_1, w_2\}`$ produces a constructed witness satisfying all hypotheses of [Theorem 9.32](#theorem-932-conditional-calculation-under-indistinguishable-records) together with a verified physical antichain between $x_A = (2, 1)$ and $x_B = (1, 2)$.

**Proof.** Stage 0 and Stage 1 physical state balance matches ledger conservation directly, confirming menu affordability. Under the singleton valued end $`\{(g(w), 1)\}`$, any terminal bundle $b_1$ attains the valued end set iff $b_1(g(w)) \ge 1$, while $b_2$ fails it iff $b_2(g(w)) = 0$; hence subjective teleological dominance holds iff $1 \le b_1(g(w)) \wedge b_2(g(w)) = 0$, matching $\succ_w$. At the post-$B$ moment in $W(w_1)$, executing $D_1$ achieves $C_1 = 1$ whereas $\mathrm{idle}$ achieves $C_1 = 0$, so $D_1$ strictly dominates the baseline and every feasible rival on the Stage 1 menu $`\{\mathrm{idle}, D_1\}`$, establishing $\mathsf{P}$ for $D_1$ (and symmetrically for $D_2$ at the post-$A$ moment in $W(w_2)$ ). Because $W(w_1)$ and $W(w_2)$ live on distinct world instances, opposite current appraisals never collide on a shared decision node, while a separate idle decision stage supplies a valid ground witness for [Theorem 9.32](#theorem-932-conditional-calculation-under-indistinguishable-records). $\blacksquare$

---

## Institutional Calculation Impossibilities: Labor Vouchers, Input-Output Ledgers, Transcripts, Zero Queues, and Price Boxes

With the shared physical economy and its acceptable methods pinned down, we instantiate each restricted planning institution directly and prove its failure from indistinguishable pre-commitment observations.

### Definition 9.51 (Acyclic Embodied-Labor Accounting and the Pre-Commitment Voucher Record)
Define acyclic embodied-labor accounting coefficients for the factor preparation recipes as $\mathrm{emb}(K_1) = 1$, $\mathrm{emb}(K_2) = 1$, and $\mathrm{emb}(g) = 0$ for all other goods (including $\mathrm{setup}$ ). Define the total **labor charge** of target method $`m \in \{A, B\}`$ as direct clock hours plus embodied factor hours:

$$
\mathrm{laborCost}(m) = \ell_{\mathrm{task}}(\tau_m) + \sum_{g \in \mathcal{G}} u(\tau_m, g) \cdot \mathrm{emb}(g).
$$

Under a public **labor-voucher interface**, before private downstream appraisals become available, the planner observes the concrete pre-commitment record:

$$
\mathcal{O}_{\mathrm{voucher}}(w) = \bigl(L_{\mathrm{pre}}.E.\mathrm{stock},\ u,\ y,\ L_{\mathrm{pre}}.E.\mathrm{cap},\ 2,\ \ell_{\mathrm{dir}},\ \mathrm{emb},\ \mathrm{laborCost},\ L_{\mathrm{pre}}.S.\mathrm{bal},\ L_{\mathrm{pre}}.S.\mathrm{cons}\bigr),
$$

comprising actual stocks, input/output recipes, remaining task capacities, shared post-prefix labor budget ($2$), direct hours, embodied coefficients, total labor charges, personal certificate balances, and completed consumer redemptions.

### Theorem 9.52 (Labor-Voucher Calculation Impossibility under Equal Embodied Hours)
In the shared physical calculation economy:
1. Both target methods carry identical total labor charges: $\mathrm{laborCost}(A) = \mathrm{laborCost}(B) = 4$.
2. Both private valuation worlds generate the identical pre-commitment voucher record: $`\mathcal{O}_{\mathrm{voucher}}(w_1) = \mathcal{O}_{\mathrm{voucher}}(w_2)`$.
3. The labor-voucher information problem $`\mathcal{P}_{\mathrm{voucher}} = (\mathcal{W}, \mathcal{R}_{\mathrm{voucher}}, \{A, B\}, \mathcal{O}_{\mathrm{voucher}}, \mathrm{Acc})`$ is unsolvable: $`\neg \mathrm{Solvable}(\mathcal{P}_{\mathrm{voucher}})`$.

**Proof.** Direct clock hours equal $1$ for both methods, while embodied factor hours sum to $2 \cdot 1 + 1 \cdot 1 + 1 \cdot 0 = 3$ for method $A$ and $1 \cdot 1 + 2 \cdot 1 + 1 \cdot 0 = 3$ for method $B$; hence $\mathrm{laborCost}(A) = 4 = \mathrm{laborCost}(B)$. Unfolding every field of $`\mathcal{O}_{\mathrm{voucher}}`$ reads only the pre-commitment ledger $`L_{\mathrm{pre}}`$ executed before the private signal arrives, yielding $`\mathcal{O}_{\mathrm{voucher}}(w_1) = \mathcal{O}_{\mathrm{voucher}}(w_2)`$. Applying the world-blind reduction of [Theorem 9.49](#theorem-949-unique-opposite-acceptable-techniques-and-world-blind-reduction) proves $`\neg \mathrm{Solvable}(\mathcal{P}_{\mathrm{voucher}})`$. $\blacksquare$

### Definition 9.53 (Separate Input-Output Activity Matrices and the Pre-Commitment Administrative Record)
Represent technology as a pair of separate nonnegative activity matrices—an input matrix $U(\tau, g) = u(\tau, g)$ and an output matrix $Y(\tau, g) = y(\tau, g)$—kept unnetted so natural-number subtraction cannot mask physical input shortages. Include:
- A common settled pre-signal consumer spot transaction starting from $`(\mathrm{stock}_S, \mathrm{stock}_B, \mathrm{cash}_B, \mathrm{cash}_S) = (1, 0, 1, 0)`$ with quantity $1$, payment $1$, and bilateral assent ($\mathrm{true}, \mathrm{true}$), settling cleanly to $(0, 1, 0, 1)$;
- Initial administrative quotes $(K_1 \mapsto 1,\ K_2 \mapsto 1,\ \text{others} \mapsto 0)$, target output $Q = 1$, and zero permitted pre-commitment current orders.

The **input-output and administrative-price observation map** records:

$$
\mathcal{O}_{\mathrm{IO}}(w) = \bigl(U,\ Y,\ L_{\mathrm{pre}}.E.\mathrm{stock},\ 2,\ 1,\ q_{\mathrm{admin}},\ 0,\ \mathrm{receipt}_{\mathrm{pre}}\bigr).
$$

### Theorem 9.54 (Input-Output and Administered-Price Calculation Impossibility)
1. Both target methods satisfy every material balance constraint before commitment: $`\forall m \in \{A, B\},\ \forall g \in \mathcal{G},\ U(\tau_m, g) \le L_{\mathrm{pre}}.E.\mathrm{stock}(g)`$ and $1 \le Y(\tau_m, Q)$.
2. Both worlds generate the identical pre-commitment input-output record: $`\mathcal{O}_{\mathrm{IO}}(w_1) = \mathcal{O}_{\mathrm{IO}}(w_2)`$.
3. The input-output information problem $`\mathcal{P}_{\mathrm{IO}} = (\mathcal{W}, \mathcal{R}_{\mathrm{IO}}, \{A, B\}, \mathcal{O}_{\mathrm{IO}}, \mathrm{Acc})`$ is unsolvable: $`\neg \mathrm{Solvable}(\mathcal{P}_{\mathrm{IO}})`$.

**Proof.** Material feasibility holds coordinatewise by [Lemma 9.46](#lemma-946-pre-commitment-residual-stocks-exhausted-prefix-capacity-and-initial-technique-feasibility) and unit yield of $Q$. Unfolding $`\mathcal{O}_{\mathrm{IO}}`$ gives equality across $w_1$ and $w_2$, and [Theorem 9.49](#theorem-949-unique-opposite-acceptable-techniques-and-world-blind-reduction) closes unsolvability. $\blacksquare$

Extending the pre-commitment interface over multiple iterative rounds or a tâtonnement price-adjustment rule leaves the impossibility intact whenever pre-commitment order-book rules admit no future capital demands before the technique commitment.

### Proposition 9.55 (Multi-Round Transcript Invariance and Pre-Commitment Zero-Queue Quote Rigidity)
1. (*Finite-Horizon Transcript Blindness*): Fix an update map $\mathrm{step} : \mathcal{R} \times \mathcal{M} \to \mathcal{R}$, an initial observation $\mathrm{init} : \mathcal{W} \to \mathcal{R}$, and a permitted-reply rule $\mathrm{reply} : \mathcal{W} \times \mathcal{R} \to \mathcal{M}$. Define the round-$n$ transcript recursively by $T_0(w) = \mathrm{init}(w)$ and $T_{n+1}(w) = \mathrm{step}(T_n(w), \mathrm{reply}(w, T_n(w)))$. Whenever $\mathrm{init}(w_1) = \mathrm{init}(w_2)$ and $\forall r \in \mathcal{R},\ \mathrm{reply}(w_1, r) = \mathrm{reply}(w_2, r)$, we have $T_n(w_1) = T_n(w_2)$ for all $n \in \mathbb{N}$, and every $n$-round transcript problem $`(\mathcal{W}, \mathcal{R}, \{A, B\}, T_n, \mathrm{Acc})`$ is unsolvable.
2. (*Zero-Queue Administered Quote Invariance*): Distinguish positive physical reserves ($K_1 = 2, K_2 = 2$) from the **current-round posted order book**. If future capital-use requests are not yet admissible during pre-commitment quote rounds, both posted order supply and admissible demand equal $0$. The zero-queue order book satisfies the clearing predicate $\mathrm{clear}$, so by [Proposition 9.44](#proposition-944-balanced-quote-invariance-price-ceiling-stalls-and-spot-conservation) one step of $\mathrm{adjust}$ under any quote schedule $q_0$ and ceiling $\bar{p}$ leaves $q_0$ completely unchanged, and the post-adjustment quote problem remains unsolvable.

**Proof.** Part 1 follows by mathematical induction on $n$: the base case $n = 0$ is $\mathrm{init}(w_1) = \mathrm{init}(w_2)$, and the inductive step rewrites $T_k(w_1) = T_k(w_2)$ together with $\mathrm{reply}(w_1, r) = \mathrm{reply}(w_2, r)$, after which [Theorem 9.49](#theorem-949-unique-opposite-acceptable-techniques-and-world-blind-reduction) applies at every $n$. Part 2 observes that $D(g) = 0 = S(g)$ everywhere satisfies $\mathrm{clear}(A, D)$; [Proposition 9.44](#proposition-944-balanced-quote-invariance-price-ceiling-stalls-and-spot-conservation) implies $\mathrm{adjust}$ preserves $q_0$ verbatim, giving an identical observation in both worlds and hence unsolvability by [Theorem 9.49](#theorem-949-unique-opposite-acceptable-techniques-and-world-blind-reduction). $\blacksquare$

### Proposition 9.56 (Price-Box Indeterminacy Cone Witness for the Target Techniques)
The two-factor input vectors $x_A = (2, 1)$ and $x_B = (1, 2)$ form a physical antichain ([Definition 9.24](#definition-924-physical-input-order-and-antichains)) and lie in the price-box indeterminacy cone over $[1, 3] \times [1, 3]$: there exist factor-price vectors $P_1, P_2 \in [1, 3]^2$ such that $`C_{P_1}(x_A) < C_{P_1}(x_B)`$ and $`C_{P_2}(x_B) < C_{P_2}(x_A)`$.

**Proof.** Coordinate $0$ gives $1 < 2$ and coordinate $1$ gives $1 < 2$ in the opposite direction, establishing the physical antichain. Taking $P_1 = (1, 3) \in [1, 3]^2$ and $P_2 = (3, 1) \in [1, 3]^2$ yields:

$$
C_{P_1}(x_A) = 1 \cdot 2 + 3 \cdot 1 = 5 < 7 = 1 \cdot 1 + 3 \cdot 2 = C_{P_1}(x_B), \qquad C_{P_2}(x_B) = 3 \cdot 1 + 1 \cdot 2 = 5 < 7 = 3 \cdot 2 + 1 \cdot 1 = C_{P_2}(x_A),
$$

which directly witnesses the price-box indeterminacy cone criterion. $\blacksquare$

---

## Positive Calculation Controls and the Exact Capital Antichain Equivalence

An impossibility theorem without matched positive controls cannot separate genuine geometric and informational obstructions from artifacts of model construction. To isolate the exact necessary and sufficient boundary of two-factor calculation conflicts, we imbed our economy into a parameterized two-factor bottleneck family and verify six distinct conditions under which planning succeeds.

### Definition 9.57 (Parameterized Two-Factor Bottleneck Family)
For arbitrary two-factor input vectors $x_A, x_B \in \mathbb{N}^2$, define the scarce factor endowment $`E(r) = \max(x_{A,r}, x_{B,r})`$ for coordinates $`r \in \{0, 1\}`$, residual stocks $R(m, r) = E(r) - x_{m, r}$, and world bottleneck coordinate $r(w_1) = 0$, $r(w_2) = 1$. In this parameterized family, both techniques are initially feasible ($x_A, x_B \le_{\mathrm{phys}} E$) and produce the same required target output $Q$. Define goal attainment $\mathrm{Att}(w, m) :\iff 1 \le R(m, r(w))$ and parameterized acceptability:

$$
\mathrm{Acc}_{x_A, x_B}(w, m) \quad :\Longleftrightarrow \quad \forall m' \in \{A, B\},\ \neg\bigl(\mathrm{Att}(w, m') \wedge \neg\mathrm{Att}(w, m)\bigr).
$$

Equivalently, $\mathrm{Att}(w, A) \iff x_{A, r(w)} < x_{B, r(w)}$, $\mathrm{Att}(w, B) \iff x_{B, r(w)} < x_{A, r(w)}$, and:

$$
\mathrm{Acc}_{x_A, x_B}(w, A) \iff x_{A, r(w)} \le x_{B, r(w)}, \qquad \mathrm{Acc}_{x_A, x_B}(w, B) \iff x_{B, r(w)} \le x_{A, r(w)}.
$$

### Theorem 9.58 (Six Positive Institutional and Informational Calculation Controls)
Economic calculation succeeds (is solvable) under each of the following six positive control conditions:
1. (*Control 1 — Physical Dominance*): If $x_A \le_{\mathrm{phys}} x_B$, then the constant rule choosing $A$ solves $`(\mathcal{W}, \mathcal{R}, \{A, B\}, \mathcal{O}, \mathrm{Acc}_{x_A, x_B})`$ for *every* observation map $\mathcal{O}$.
2. (*Control 2 — Reverse Dominance and Physical Ties*): If $x_B \le_{\mathrm{phys}} x_A$ (in particular when $x_A = x_B$ ), then the constant rule choosing $B$ solves $`(\mathcal{W}, \mathcal{R}, \{A, B\}, \mathcal{O}, \mathrm{Acc}_{x_A, x_B})`$ for *every* observation map $\mathcal{O}$.
3. (*Control 3 — Single-Factor Linearity*): When technique requirements depend on only a single factor ($x_A, x_B \in \mathbb{N}^1$) and labor charges are strictly monotone in that factor, $`\mathrm{laborCharge}(m) = h_{\mathrm{base}} + x_m(0) \cdot h_{\mathrm{unit}}`$ with $`h_{\mathrm{unit}} > 0`$, selecting the technique with lower labor charge ( $\mathrm{laborCharge}(A) \le \mathrm{laborCharge}(B) \implies A$, else $B$) always selects the smaller physical factor requirement.
4. (*Control 4 — Shared-Appraisal Antichain*): Holding the full antichain $x_A = (2, 1)$, $x_B = (1, 2)$ fixed while restricting to states that share a single common downstream appraisal ($w_1$), the constant rule selecting $B$ solves the restricted voucher problem.
5. (*Control 5 — Distinguishing Pre-Commitment Report*): Augmenting the pre-commitment voucher record with the downstream valuation report $`\mathcal{O}_{\mathrm{rep}}(w) = (\mathcal{O}_{\mathrm{voucher}}(w), w)`$ makes the augmented information problem solvable.
6. (*Control 6 — Full-State Observation*): Supplying the full state ($\mathcal{O} = \mathrm{id}$) makes the shared calculation problem solvable.

**Proof.** For Control 1, $x_A \le_{\mathrm{phys}} x_B$ gives $x_{A, r(w)} \le x_{B, r(w)}$ for both $`w \in \{w_1, w_2\}`$, so $`\mathrm{Acc}_{x_A, x_B}(w, A)`$ holds everywhere; Control 2 is symmetric for $B$. For Control 3, since $`h_{\mathrm{unit}} > 0`$, $\mathrm{laborCharge}(A) \le \mathrm{laborCharge}(B)$ implies $`x_A(0) \cdot h_{\mathrm{unit}} \le x_B(0) \cdot h_{\mathrm{unit}}`$, yielding $x_A(0) \le x_B(0)$ by positive cancellation, and conversely when strict inequality reverses. Control 4 follows immediately from [Theorem 9.49](#theorem-949-unique-opposite-acceptable-techniques-and-world-blind-reduction) in world $w_1$. Control 5 defines $`\rho(\_, w_1) = B`$ and $`\rho(\_, w_2) = A`$, succeeding in both worlds by [Theorem 9.49](#theorem-949-unique-opposite-acceptable-techniques-and-world-blind-reduction). Control 6 combines Part 2 of [Lemma 9.34](#lemma-934-fiberwise-characterization-of-solvable-information-problems-and-full-information-control) with existence of an acceptable method ([Theorem 9.49](#theorem-949-unique-opposite-acceptable-techniques-and-world-blind-reduction)). $\blacksquare$

### Theorem 9.59 (Exact Capital Antichain Equivalence for Two-Factor Bottleneck Conflicts)
In the parameterized two-factor bottleneck family of [Definition 9.57](#definition-957-parameterized-two-factor-bottleneck-family):
1. (*Conflict Equivalence*): Two techniques $x_A, x_B \in \mathbb{N}^2$ form a physical antichain ([Definition 9.24](#definition-924-physical-input-order-and-antichains)) if and only if worlds $w_1$ and $w_2$ share no commonly acceptable technique:

$$
\mathrm{PhysicalAntichain}(x_A, x_B) \quad \Longleftrightarrow \quad \forall m \in \{A, B\},\ \neg\bigl(\mathrm{Acc}_{x_A, x_B}(w_1, m) \wedge \mathrm{Acc}_{x_A, x_B}(w_2, m)\bigr).
$$

2. (*Necessity and Sufficiency under Blind Records*): For *any* observation map $\mathcal{O}$ that equates $w_1$ and $w_2$ ( $\mathcal{O}(w_1) = \mathcal{O}(w_2)$ ), unsolvability is equivalent to the techniques forming a physical antichain:

$$
\neg \mathrm{Solvable}\bigl((\mathcal{W}, \mathcal{R}, \{A, B\}, \mathcal{O}, \mathrm{Acc}_{x_A, x_B})\bigr) \quad \Longleftrightarrow \quad \mathrm{PhysicalAntichain}(x_A, x_B).
$$

**Proof.** For Part 1 ($\implies$), if $x_A, x_B$ form a physical antichain, then by [Proposition 9.25](#proposition-925-physical-incomparability) neither $x_A \le_{\mathrm{phys}} x_B$ nor $x_B \le_{\mathrm{phys}} x_A$ holds. Yet $`\mathrm{Acc}_{x_A, x_B}(w_1, A) \wedge \mathrm{Acc}_{x_A, x_B}(w_2, A)`$ holds iff $x_{A, 0} \le x_{B, 0} \wedge x_{A, 1} \le x_{B, 1}$ (i.e., $x_A \le_{\mathrm{phys}} x_B$ ), and symmetrically for $B$; hence neither $A$ nor $B$ can be acceptable in both worlds. For ($\Longleftarrow$), if neither $A$ nor $B$ is mutually acceptable, then $\neg(x_{A,0} \le x_{B,0} \wedge x_{A,1} \le x_{B,1})$ and $\neg(x_{B,0} \le x_{A,0} \wedge x_{B,1} \le x_{A,1})$, which forces a coordinate $`a \in \{0, 1\}`$ with $x_{B,a} < x_{A,a}$ and a coordinate $`b \in \{0, 1\}`$ with $x_{A,b} < x_{B,b}$.

For Part 2 ($\implies$), if the blind problem is unsolvable, neither $x_A \le_{\mathrm{phys}} x_B$ nor $x_B \le_{\mathrm{phys}} x_A$ can hold (otherwise Control 1 or Control 2 of [Theorem 9.58](#theorem-958-six-positive-institutional-and-informational-calculation-controls) would solve it), forcing a physical antichain just as above. For ($\Longleftarrow$), combining Part 1 with [Theorem 9.35](#theorem-935-calculation-impossibility-under-conflicting-indistinguishable-states) proves unsolvability whenever $\mathcal{O}(w_1) = \mathcal{O}(w_2)$. $\blacksquare$

Notice how [Theorem 9.58](#theorem-958-six-positive-institutional-and-informational-calculation-controls) and [Theorem 9.59](#theorem-959-exact-capital-antichain-equivalence-for-two-factor-bottleneck-conflicts) clarify the exact scope of Mises's problem: when complete valuations of ultimate ends are already available prior to commitment (Control 5 or Control 6), or when one factor or physical dominance governs the techniques (Controls 1–3), central calculation succeeds. The impossibility bites precisely when irreducible capital trade-offs (physical antichains) coincide with missing pre-commitment valuation signals.

---

## Flat Time-Voucher Effort Incentives and Bottleneck Starvation

Distinct from pre-commitment information blindness, flat clock-hour labor vouchers induce an incentive breakdown whenever differential human effort is required to supply critical intermediate factors. We construct this worker-effort mechanism explicitly over both the synchronized work-and-redemption ledger and a compiled branching action frame.

### Definition 9.60 (Flat Time-Voucher Worker Economy and Synchronized Redemption Ledger)
Construct a discrete worker economy over goods $`\mathcal{G}_W = \{\mathrm{food}, \mathrm{effort}, \mathrm{intermediate}, \mathrm{final}\}`$ and tasks $`\mathcal{T}_W = \{\mathrm{easy}, \mathrm{hard}, \mathrm{downstream}\}`$ with initial stock $(\mathrm{food}, \mathrm{effort}, \mathrm{intermediate}, \mathrm{final}) = (1, 2, 0, 0)$, unit capacities $1$, voucher food price $1$, zero initial certificate balances, and $1$ certified labor hour per run for every task:

| Task | Inputs | Outputs | Certified Clock Hours |
|---|---|---|---|
| $\mathrm{easy}$ | $1\;\mathrm{effort}$ | none | $1$ |
| $\mathrm{hard}$ | $2\;\mathrm{effort}$ | $1\;\mathrm{intermediate}$ | $1$ |
| $\mathrm{downstream}$ | $1\;\mathrm{intermediate}$ | $1\;\mathrm{final}$ | $1$ |

For each root choice $`c \in \{\mathrm{idle}, \mathrm{easy}, \mathrm{hard}\}`$:
1. Execution via $\mathrm{execAndIssue}$ leaves the ledger unchanged under $\mathrm{idle}$, and credits $1$ labor certificate under both $\mathrm{easy}$ and $\mathrm{hard}$;
2. Consumer redemption via $`\mathrm{redeem}_L`$ at price $1$ leaves $\mathrm{food}$ unredeemed under $\mathrm{idle}$ ($0$), and redeems $1$ unit of $\mathrm{food}$ under both $\mathrm{easy}$ and $\mathrm{hard}$;
3. Residual physical endowments after redemption are $`(\mathrm{food}_{\mathrm{cons}}, \mathrm{effort}, \mathrm{intermediate}) = (0, 2, 0)`$ under $\mathrm{idle}$, $(1, 1, 0)$ under $\mathrm{easy}$, and $(1, 0, 1)$ under $\mathrm{hard}$.

This ledger transition reproduces an exact one-stage physical choice transition over the same worker menu $`\{\mathrm{idle}, \mathrm{easy}, \mathrm{hard}\}`$, starting from $\mathrm{effort} = 2$ and producing the identical post-redemption food, remaining effort, and intermediate stocks.

### Theorem 9.61 (Teleological Dominance of Easy Work and Downstream Bottleneck Starvation)
Equip the worker in [Definition 9.60](#definition-960-flat-time-voucher-worker-economy-and-synchronized-redemption-ledger) with two ordinal valued ends: obtaining consumer nourishment $`e_{\mathrm{food}} = (\mathrm{food}, 1)`$ and retaining rest $`e_{\mathrm{rest}} = (\mathrm{effort}, 1)`$. In the compiled worker action frame:
1. Executing $\mathrm{easy}$ jointly attains both valued ends $`\{e_{\mathrm{food}}, e_{\mathrm{rest}}\}`$ (ending with $1$ food and $1$ effort), whereas $\mathrm{hard}$ fails $`e_{\mathrm{rest}}`$ ($0$ effort) and $\mathrm{idle}$ fails $`e_{\mathrm{food}}`$ ($0$ food).
2. Under subjective teleological bundle dominance, $\mathrm{easy}$ is strictly preferred to both $\mathrm{hard}$ and $\mathrm{idle}$.
3. Enacting $\mathrm{easy}$ satisfies purposeful action ($\mathsf{P}$), **every** purposeful response on the complete worker menu $`\{\mathrm{idle}, \mathrm{easy}, \mathrm{hard}\}`$ necessarily selects $\mathrm{easy}$, and neither $\mathrm{hard}$ nor $\mathrm{idle}$ can be purposefully executed.
4. (*Downstream Bottleneck Starvation*): Because every purposeful worker chooses $\mathrm{easy}$, intermediate stock remains $0$, rendering the downstream bottleneck task $\mathrm{downstream}$ infeasible both on the public work ledger ($\neg \mathrm{CanExec}$) and on the physical choice stage.

**Proof.** Parts 1–2 verify by ledger and stage conservation that $\mathrm{easy}$ leaves $`(\mathrm{food}_{\mathrm{cons}}, \mathrm{effort}) = (1, 1)`$ while $\mathrm{hard}$ leaves $(1, 0)$ and $\mathrm{idle}$ leaves $(0, 2)$. Since $`\{e_{\mathrm{food}}\}`$ is the maximal valued-end subset attained by $\mathrm{hard}$ and $`\{e_{\mathrm{rest}}\}`$ is the maximal subset attained by $\mathrm{idle}$, while $`\{e_{\mathrm{food}}, e_{\mathrm{rest}}\}`$ is jointly attained by $\mathrm{easy}$, subjective teleological dominance holds strictly over both rivals. Because $\mathrm{easy}$ is feasible and strictly preferred to $\mathrm{idle}$ and $\mathrm{hard}$, $\mathrm{easy}$ is purposeful and uniquely maximizes preference over the entire menu (Chapter 3, [Theorem 3.11](03_preference_purpose_and_opportunity_cost.md#theorem-311-the-action-axiom-and-non-passivity-theorem)); conversely any history purporting to enact $\mathrm{hard}$ or $\mathrm{idle}$ violates undominatedness because $\mathrm{easy}$ is feasible and strictly preferred. Finally, under $\mathrm{easy}$, $\mathrm{intermediate} = 0 < 1 = u(\mathrm{downstream}, \mathrm{intermediate})$, violating both $\mathrm{CanExec}$ on the work ledger and stage affordability. $\blacksquare$

### Theorem 9.62 (Equal-Effort Control Restores Purposeful Bottleneck Production and Downstream Feasibility)
Modify the worker economy of [Definition 9.60](#definition-960-flat-time-voucher-worker-economy-and-synchronized-redemption-ledger) by holding voucher compensation and food price fixed while reducing the effort input of $\mathrm{hard}$ from $2$ units to $1$ unit (matching $\mathrm{easy}$'s effort cost). Then in the compiled equal-effort action frame:
1. Executing $\mathrm{hard}$ leaves $`(\mathrm{food}_{\mathrm{cons}}, \mathrm{effort}, \mathrm{intermediate}) = (1, 1, 1)`$ and jointly attains both valued ends $`\{e_{\mathrm{food}}, e_{\mathrm{rest}}\}`$.
2. Executing $\mathrm{hard}$ satisfies purposeful human action ($\mathsf{P}$), since it strictly dominates $\mathrm{idle}$ and is undominated by $\mathrm{easy}$ (which also attains at most $`\{e_{\mathrm{food}}, e_{\mathrm{rest}}\}`$).
3. After executing and redeeming $\mathrm{hard}$, the downstream bottleneck operation $\mathrm{downstream}$ is feasible both on the public work ledger ($\mathrm{CanExec}$) and on the physical stage.

**Proof.** Physical balance gives $\mathrm{effort} = 2 - 1 = 1$, redeemed $\mathrm{food} = 1$, and $\mathrm{intermediate} = 1$, attaining $`\{e_{\mathrm{food}}, e_{\mathrm{rest}}\}`$. Because $\mathrm{idle}$ attains $0$ food, $\mathrm{hard}$ strictly dominates $\mathrm{idle}$. Because $\mathrm{easy}$ cannot attain any valued end beyond $`\{e_{\mathrm{food}}, e_{\mathrm{rest}}\}`$, $\mathrm{easy}$ does not dominate $\mathrm{hard}$, establishing $\mathsf{P}$ for $\mathrm{hard}$. With $\mathrm{intermediate} = 1 \ge u(\mathrm{downstream}, \mathrm{intermediate})$ and unit capacity $1$, $\mathrm{downstream}$ satisfies both ledger $\mathrm{CanExec}$ and stage affordability. $\blacksquare$

---

## Finite Witnesses for Monetary and Calculation Results

Different examples answer different questions. A finite bilateral model illustrates compatible choices, matched transfers, and why an unmatched offer does not execute a trade. Other examples illustrate defensive compliance under extortion, endogenous property exchange and competition, specialization under explicit labor budgets, monetary diffusion through a finite network, and the information obstruction in calculation.

These constructions establish that the stated configurations are inhabited. They do not make all economic conclusions follow from the mere existence of two agents. Each conclusion uses the relations introduced for it: joint realization for compatible action, autonomous comparisons for voluntary gain, matched execution for physical exchange, technological cost differences for specialization, demand-connectivity for monetary diffusion, and restricted observations for the calculation theorem.

## A Staged Credit Injection across a Trading Network

The preceding network results describe the spread of acceptance. We can also specify a staged schedule under which an added balance enters an agent's effective bid only after the assigned hop distance from an injection point has been reached. Let $d(i)$ be that assigned distance and let $\delta>0$ be the increment. At stage $k$, define an agent's effective bid as its base bid plus $\delta$ exactly when $d(i)\le k$; otherwise its effective bid remains its base bid. The same convention may be used for effective cash. This is a stipulated schedule, not yet a derived sequence of transfers.

### Proposition 9.63 (A Downstream Bid Can Remain below the Wave Price)

Let agent $j$ lie beyond stage $k$, so $k < d(j)$. If its base bid satisfies

$$
P_{\mathrm{pre}}\le v_j < P_{\mathrm{wave}},
$$

then its effective bid at stage zero is at least $P_{\mathrm{pre}}$, while its effective bid at stage $k$ remains below $P_{\mathrm{wave}}$.

**Proof.** Since $d(j) > k\ge0$, the added balance is not included in $j$'s effective bid at either stage zero or stage $k$. Both effective bids therefore equal $v_j$. The two inequalities follow from the assumed bounds on $v_j$. $\square$

[Proposition 9.63](#proposition-963-a-downstream-bid-can-remain-below-the-wave-price) is a bid-response module for a stipulated hop schedule and two price thresholds: an agent beyond the current stage can meet the lower threshold while remaining below the wave price. A price-formation application composes it with a transfer process that generates the schedule, preference and feasibility premises for purposeful bids, and a market-clearing rule. Those interfaces determine whether the bid inequality contributes to a broader inflation path.

## Conclusion

We have traced how acceptance of a medium can spread, how a stipulated monetary increment can enter bids at different network distances, how discrete reservation prices constrain a clearing range, and how market prices allow unlike inputs to be compared in a common accounting unit. We also saw that arithmetic thresholds become claims about action only when preferences, feasible alternatives, and execution support them. We now use these distinctions to study entrepreneurs who act under uncertainty, including credit origination and investment that may not reach completion.
