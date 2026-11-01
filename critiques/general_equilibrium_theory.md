# Praxeological Critique of Walrasian General Equilibrium Theory

## 1. Original Argument and Theoretical Explanation

Walrasian General Equilibrium Theory (GET), originated by Léon Walras (1874) and mathematically formalized by Kenneth Arrow, Gérard Debreu, and Lionel McKenzie (the ADM framework, 1954), asserts that a competitive decentralized market economy can be represented as a system of simultaneous equations whose market-clearing equilibrium is characterized by:

1. **A Vector of Real Market-Clearing Prices:**
   There exist $n$ continuous commodities $x \in \mathbb{R}^n$ and an equilibrium price vector $\mathbf{P}^{\ast} \in \mathbb{R}^n_+$ on the unit simplex $\Delta^{n-1}$ such that aggregate excess demand across all markets is non-positive:

$$
\mathbf{z}(\mathbf{P}^{\ast}) \le \mathbf{0}, \quad \text{with} \quad \mathbf{P}^{\ast} \cdot \mathbf{z}(\mathbf{P}^{\ast}) = 0
$$

2. **The Fictional Auctioneer and Tâtonnement:**
   Prices adjust via a centralized trial-and-error process (*tâtonnement*) directed by an omniscient auctioneer: $`\dot{\mathbf{P}} = \kappa \, \mathbf{z}(\mathbf{P})`$. Crucially, **no exchange or production is permitted out of equilibrium** ("no false trading"). Contracts are executed if and only if the simultaneous equilibrium price vector $\mathbf{P}^{\ast}$ is reached.
3. **Timelessness and Complete Contingent Markets:**
   All current and future contingent trades across all possible states of nature are cleared simultaneously at an initial moment $t = 0$. After this initial clearance, economic actors merely execute predetermined contractual deliveries without further active decision-making.
4. **The Exclusion of Money (Hahn's Problem):**
   In a complete-markets framework with an omniscient auctioneer, zero transaction costs, and instantaneous market clearing, money has no positive value $(P_{\text{money}} = 0)$, leaving GET incapable of integrating monetary calculation into general equilibrium.

---

## 2. Formal Definitions of the Target Doctrine

To analyze GET within the constructive reality of human action and physical conservation, we formalize the target doctrine's core assumptions using the primitives of Chapters 2, 8, and 9:

### Definition 1 (The Walrasian Continuous Price Vector)
Let commodities be represented on a continuous Euclidean space $\mathbb{R}^n$. The auctioneer seeks an infinitesimal single-point clearing price:

$$
\mathbf{P}^{\ast} \in \mathbb{R}^n_+, \quad \sum_{k=1}^n P_k^{\ast} = 1
$$

such that supply exactly equals demand at every coordinate.

### Definition 2 (The Zero Out-of-Equilibrium Trading Postulate)
Let $t_0$ be the initial moment and $t^{\ast}$ be the moment equilibrium is reached. Across all trial iterations $t < t^{\ast}$, no actual physical property transfer or production may occur:

$$
\forall i \in \mathcal{I}, \quad \forall t < t^{\ast}, \quad \text{enacted}(i, t, h) = \alpha_0
$$

Physical endowments remain frozen: $\omega(i, t, h, m) = \omega(i, t_0, h, m)$.

### Definition 3 (The Timeless Degenerate Horizon)
GET assumes that all future contingencies are pre-reconciled at $t_0$. Consequently, for any moment $t > t_0$, the set of possible future histories is a singleton:

$$
|\mathcal{H}(t)| = 1
$$

Branching historical time is collapsed into a single deterministic trajectory.

---

## 3. Discrete Clearing Interval Indeterminacy

**Proposition.** In actual market exchange, market clearing does not identify a unique real-number point price; it identifies a closed discrete clearing interval bounded by marginal reservation prices.

**Proof.**
1. In Chapter 8 and Chapter 9, exchange occurs over discrete quantities $(q \in \mathbb{N})$ and discrete monetary units.
2. Consider a buyer with maximum reservation price $v_{\text{buyer}}$ and a seller with minimum reservation price $v_{\text{seller}}$, with $v_{\text{seller}} < v_{\text{buyer}}$.
3. For any discrete integer price $P \in [v_{\text{seller}}, v_{\text{buyer}}]$, the trade action is purposeful for the buyer $(v_{\text{buyer}} - P \ge 0)$ and purposeful for the seller $(P - v_{\text{seller}} \ge 0)$.
4. Both agents strictly prefer the trade outcome to the inertial baseline $\alpha_0$.
5. The market clears at any price in the interval $[v_{\text{seller}}, v_{\text{buyer}}]$. Introducing rival buyers and sellers narrows this interval, but with discrete traders and discrete money, the clearing set remains an interval, not an infinitesimal mathematical point.
Single-point continuous uniqueness is a mathematical artifact of assuming continuous real-valued utility functions, which conflicts with discrete constructive choice. $\blacksquare$

---

## 4. Path-Dependent Inventory Shifts under Sequential Trade

**Proposition.** The "no false trading" postulate is a physical impossibility in a decentralized economy. Any real trade executed out of equilibrium physically shifts factor inventories and endogenously alters subsequent clearing prices.

**Proof.**
1. By the physical transition laws of Chapter 2 and Chapter 8, executing an exchange action $\alpha_{\text{trade}}$ at moment $t$ transitions physical endowments to $t'$ across precedence chain $t \prec t'$:

$$
\omega(i, t', h, m) \neq \omega(i, t, h, m)
$$

2. By Theorem 4.32 (Chapter 4), an agent's feasible action menu $`\mathcal{A}_{\text{feas}}(i, t', h)`$ and subjective marginal valuations of additional units depend directly on present physical inventory $\omega(i, t', h, m)$.
3. Because every transaction alters the physical stocks held by the participants, the reservation prices $v_{\text{buyer}}$ and $v_{\text{seller}}$ for subsequent rounds of exchange are permanently altered.
4. The hypothetical equilibrium price vector $\mathbf{P}^{\ast}$ does not remain stationary while traders search; it shifts as a direct causal consequence of every trade.
An economic theory that prohibits trading at disequilibrium prices assumes that prices coordinate human activity without anyone actually trading at those prices—a direct contradiction. $\blacksquare$

---

## 5. Resolution of Hahn's Problem via Branching Uncertainty

**Proposition.** In complete contingent markets with zero uncertainty, money cannot exist. In praxeology, money is constructively derived from branching historical uncertainty.

**Proof.**
1. Under GET's assumption of complete markets $(|\mathcal{H}(t)| = 1)$, all future deliveries are guaranteed at $t_0$. There is no liquidity risk, no uncertainty, and no need to hold an uncommitted general medium of exchange. Consequently, the equilibrium price of money is zero $(P_{\text{money}} = 0)$.
2. In actual human action, time is branching: $|\mathcal{H}(t)| \ge 2$ (Chapter 2 and Chapter 5). At moment $t$, an agent faces genuine uncertainty regarding which future historical branch will materialize.
3. As proven in Chapter 9, holding cash balances $(\omega(i, t, h, m_{\text{money}}))$ renders the specific subjective service of providing an uncommitted physical medium that preserves optionality across divergent future choice cells.
4. Because the future is open and uncertain, agents purposefully demand cash balances. Hahn's Problem is not an empirical puzzle to be patched with ad-hoc frictions; it is a direct mathematical proof that general equilibrium models describe a world without human action. $\blacksquare$

---

## 6. Epistemic Barriers and Capital Theory

### The Epistemic Barrier and Capital Antichains
The Walrasian auctioneer assumes that all preference rankings and production functions across an entire society can be centralized into a single system of simultaneous equations.

As demonstrated in Chapter 9 (Theorem 9.21), heterogeneous capital goods form physical **antichains**:

$$
x_A \not\le x_B \quad \wedge \quad x_B \not\le x_A
$$

They cannot be ranked or compared through physical or engineering units alone. The relative value of intermediate capital goods can only be established through genuine monetary exchange prices generated by decentralized entrepreneurial bidding. Because the information required to formulate the auctioneer's equations does not exist prior to decentralized market exchange, the Walrasian equilibrium cannot be computed or implemented by any central agency.
