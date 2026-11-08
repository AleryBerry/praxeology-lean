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

A calculation rule can use only the information supplied to it. The theorem constructs economies with the same restricted record but opposite marginal preferences, so any rule based solely on that record fails to economize in at least one economy.

### Definition 9.31 (Action Frame Socialist Economy and Preserved Marginal End)
In an action frame $W$, an *action frame socialist economy* $E$ at decision context $(i, t, h)$ specifies two distinct means $m_A \neq m_B$, two distinct ends $e_A \neq e_B$, two feasible production techniques $x_A, x_B \in \mathbb{N}^2$, a non-market statistical report $`R : \{0, 1\} \to \mathbb{N}`$, and means bundles $b_A, b_B$ satisfying subjective teleological dominance. Its non-market observable record is:

$$
\mathcal{O}(E) = (x_A, x_B, R).
$$

The non-market statistical record is strictly confined to technological coefficients and aggregate quantities, isolating physical data from subjective valuations and marginal preferences. Define the end preserved by technique $x$ to be $e_A$ if $x_0 \le x_1$, and $e_B$ otherwise. This is the explicit two-factor convention of the model: the relatively economized factor supports the corresponding alternative end.

A technique choice violates Mengerian economizing if the alternative feasible technique preserves a strictly preferred marginal end. A central planning rule selects one of the two feasible techniques, $A$ or $B$, as a function of $\mathcal{O}(E)$ alone.

### Theorem 9.32 (The Mises-Hayek Economic Calculation Impossibility Theorem)
There exist two socialist economies in an action frame with the same observable record such that every rule based only on that record violates economizing in at least one of them.

**Proof.** In both economies take $x_A = (2, 1)$, $x_B = (1, 2)$, which form a physical antichain, and the same non-market report $R$. Technique $A$ preserves $e_B$ and technique $B$ preserves $e_A$. In the first economy $E_1$, bundle $b_A$ dominates $b_B$ teleologically, so $e_A \succ_{i_1, t_1, h_1} e_B$. In the second economy $E_2$, bundle $b_B$ dominates $b_A$, so $e_B \succ_{i_2, t_2, h_2} e_A$. Thus choosing $A$ violates Mengerian economizing in $E_1$ (since $B$ preserves preferred $e_A$), while choosing $B$ violates it in $E_2$ (since $A$ preserves preferred $e_B$).

The observable non-market records are identical: $\mathcal{O}(E_1) = \mathcal{O}(E_2)$, so a rule depending only on that record returns the same choice in both economies. If it chooses $A$, it fails in the first; if it chooses $B$, it fails in the second. These exhaust the rule's two possible outputs. $\blacksquare$

The conclusion quantifies over every decision function on the stated record, including rules that do not add numerical ranks. Its scope is determined by the information restriction: a richer record that distinguishes the two marginal valuations changes the premises. In this account of the economic calculation problem, the non-market record excludes the evaluative information that factor-market exchange is meant to communicate.

[Theorem 9.32](#theorem-932-the-mises-hayek-economic-calculation-impossibility-theorem) gives an information boundary for guarantees based on the specified record: a convention can select a technique, but no rule using that record can guarantee an economizing selection in both constructed economies. The result turns on the record's exclusion of the differing marginal valuations, not on a limit to the decision rule's computational power.

---

## Finite Witnesses for Monetary and Calculation Results

Different examples answer different questions. A finite bilateral model illustrates compatible choices, matched transfers, and why an unmatched offer does not execute a trade. Other examples illustrate defensive compliance under extortion, endogenous property exchange and competition, specialization under explicit labor budgets, monetary diffusion through a finite network, and the information obstruction in calculation.

These constructions establish that the stated configurations are inhabited. They do not make all economic conclusions follow from the mere existence of two agents. Each conclusion uses the relations introduced for it: joint realization for compatible action, autonomous comparisons for voluntary gain, matched execution for physical exchange, technological cost differences for specialization, demand-connectivity for monetary diffusion, and restricted observations for the calculation theorem.

## A Staged Credit Injection across a Trading Network

The preceding network results describe the spread of acceptance. We can also specify a staged schedule under which an added balance enters an agent's effective bid only after the assigned hop distance from an injection point has been reached. Let $d(i)$ be that assigned distance and let $\delta>0$ be the increment. At stage $k$, define an agent's effective bid as its base bid plus $\delta$ exactly when $d(i)\le k$; otherwise its effective bid remains its base bid. The same convention may be used for effective cash. This is a stipulated schedule, not yet a derived sequence of transfers.

### Proposition 9.33 (A Downstream Bid Can Remain below the Wave Price)

Let agent $j$ lie beyond stage $k$, so $k < d(j)$. If its base bid satisfies

$$
P_{\mathrm{pre}}\le v_j < P_{\mathrm{wave}},
$$

then its effective bid at stage zero is at least $P_{\mathrm{pre}}$, while its effective bid at stage $k$ remains below $P_{\mathrm{wave}}$.

**Proof.** Since $d(j) > k\ge0$, the added balance is not included in $j$'s effective bid at either stage zero or stage $k$. Both effective bids therefore equal $v_j$. The two inequalities follow from the assumed bounds on $v_j$. $\square$

[Proposition 9.33](#proposition-933-a-downstream-bid-can-remain-below-the-wave-price) is a bid-response module for a stipulated hop schedule and two price thresholds: an agent beyond the current stage can meet the lower threshold while remaining below the wave price. A price-formation application composes it with a transfer process that generates the schedule, preference and feasibility premises for purposeful bids, and a market-clearing rule. Those interfaces determine whether the bid inequality contributes to a broader inflation path.

## Conclusion

We have traced how acceptance of a medium can spread, how a stipulated monetary increment can enter bids at different network distances, how discrete reservation prices constrain a clearing range, and how market prices allow unlike inputs to be compared in a common accounting unit. We also saw that arithmetic thresholds become claims about action only when preferences, feasible alternatives, and execution support them. We now use these distinctions to study entrepreneurs who act under uncertainty, including credit origination and investment that may not reach completion.
