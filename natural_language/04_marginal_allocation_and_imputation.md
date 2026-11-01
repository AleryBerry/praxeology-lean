# Chapter 4: Marginal Allocation, Complementarity, and Imputation

We now ask how a change in a resource stock changes the ends an agent can attain. To make the comparison precise, we first study a finite case with one unit per end and a stated ranking of those ends. We then relax the one-unit assumption, consider missing complements, and trace a downstream change in attainable ends back to a productive factor.

> **Prerequisites and scope:** Chapters 1–3. We use the physical requirement schedule, purposeful choice, and finite preference orders to study marginal allocations, complementary requirements, and conditional factor imputation.

The results in this chapter are deliberately conditional. A ranked list of ends is an assumption in the finite allocation model; it is not inferred from the mere fact that a person holds a certain quantity of a good. We state that ranking and the allocation rule before drawing conclusions about marginal ends.

## Joint Feasibility and the Atomic Regime

We begin with joint feasibility, since the same stock may need to serve several ends. The atomic case then assigns one unit of a selected means to each distinct end. Once we know that no more than $k$ such ends can be attained, an explicitly ordered list gives us a tractable allocation problem.

### Definition 4.1 (Joint Feasibility)
Let $i \in \mathcal{I}$ be an agent, $t \in \mathcal{T}$ a moment, $h \in \mathcal{H}$ a history, and let $S \subseteq \mathcal{E}$ be a finite set of contemplated ends. The bundle $S$ is **jointly feasible** with respect to the agent's physical endowment vector $\omega(i, t, h, \cdot)$ if and only if the aggregate requirement across all ends in $S$ does not exceed the available endowment of every means:

$$
\text{JointlyFeasible}(i, t, h, S) \iff \forall m \in \mathcal{M}, \quad \sum_{e \in S} \rho(e, m) \le \omega(i, t, h, m)
$$

where $\rho : \mathcal{E} \times \mathcal{M} \to \mathbb{N}$ is the technological requirement schedule defined in Chapter 1.

When focusing on the economizing of a single scarce commodity $m \in \mathcal{M}$, we formalize the agent's discrete ranking of independent potential satisfactions through the concept of an atomic requirement schedule.

### Definition 4.2 (A Finite One-Unit Allocation)
Let $m \in \mathcal{M}$ be a scarce means with available physical endowment $k = \omega(i, t, h, m) \in \mathbb{N}$. A **standard atomic regime** of order $N > k$ for agent $i$ at decision node $\langle t, h \rangle$ is a structure:

$$
\mathcal{R}_{\text{atom}}(i, t, h, m, N) = \langle k, e_{\text{seq}} \rangle
$$

where:
1. $k < N$ represents the scarcity condition: the available endowment is insufficient to fulfill all $N$ potential ends.
2. $`e_{\text{seq}} : \{0, \dots, N-1\} \to \mathcal{E}`$ is an injective sequence of mutually distinct atomic ends ( $`r \neq s \implies e_{\text{seq}}(r) \neq e_{\text{seq}}(s)`$ ).
3. **Unit Requirement**: Each atomic end requires exactly one physical unit of means $m$:

$$
\forall r \in \{0, \dots, N-1\}, \quad \rho(e_{\text{seq}}(r), m) = 1
$$

4. **Strict Ordinal Ranking**: The ends are strictly ordered by the agent's demonstrated preference relation $\succ_{i,t,h}$:

$$
\forall r, s \in \{0, \dots, N-1\}, \quad r < s \implies e_{\text{seq}}(r) \succ_{i,t,h} e_{\text{seq}}(s)
$$

### Definition 4.3 (Ends in the Ranked List)
For a standard atomic regime $`\mathcal{R}_{\text{atom}}`$, the **atomic end space** $E_1(m)$ is the set of all atomic ends spanned by the schedule:

$$
E_1(m) \equiv \{ e_{\text{seq}}(r) \mid r \in \{0, \dots, N-1\} \} \subseteq \mathcal{E}
$$

### Proposition 4.4 (The List Contains $N$ Distinct Ends)
The cardinality of the atomic end space $E_1(m)$ is exactly $N$.

**Proof.** The set $`E_1(m)`$ is the image of the finite set $`\{0, \dots, N-1\}`$ under the mapping $`e_{\text{seq}}`$. Since $`e_{\text{seq}}`$ is injective by Definition 4.2, the cardinality of the image equals the cardinality of the domain: $`|E_1(m)| = |\{0, \dots, N-1\}| = N`$. $\blacksquare$

### Lemma 4.5 (Requirement Equals the Number of Selected Ends)
For any atomic bundle $S \subseteq E_1(m)$, the total requirement of means $m$ across all ends in $S$ is exactly equal to the cardinality $|S|$:

$$
\sum_{e \in S} \rho(e, m) = |S|
$$

**Proof.** For every $e \in S$, since $S \subseteq E_1(m)$, there exists a unique $r < N$ such that $e = e_{\text{seq}}(r)$. By Definition 4.2, $\rho(e_{\text{seq}}(r), m) = 1$. Summing the constant 1 over all elements of the finite set $S$ yields $\sum_{e \in S} 1 = |S|$. $\blacksquare$

### Corollary 4.6 (At Most $k$ Ends Are Feasible)
For any atomic bundle $S \subseteq E_1(m)$, if $S$ satisfies the endowment feasibility constraint $\sum_{e \in S} \rho(e, m) \le \omega(i, t, h, m)$, then:

$$
|S| \le k
$$

**Proof.** Immediate from Lemma 4.5 and the endowment equality $\omega(i, t, h, m) = k$. $\blacksquare$

---

## Ranking the Ends Added by Successive Units

Under the one-unit requirement and the stipulated strict ranking, the first $k$ ends form the unique preferred allocation according to the comparison defined below. As $k$ rises, each new unit adds the next end in that list. The resulting comparison concerns the order of ends; it does not establish a general law for technologies or preferences outside this regime.

### Definition 4.7 (The First $k$ Ends)
Let $`\mathcal{R}_{\text{atom}}`$ be a standard atomic regime of order $N$, and let $k \le N$. The **optimal allocation bundle** $S^{\ast}(k)$ is the set containing the top $k$ ranked atomic ends:

$$
S^{\ast}(k) \equiv \{ e_{\text{seq}}(r) \mid r < k \} \subseteq E_1(m)
$$

### Lemma 4.8 (The First $k$ Ends Are Distinct)
The cardinality of $S^{\ast}(k)$ is exactly $k$:

$$
|S^{\ast}(k)| = k
$$

**Proof.** $S^{\ast}(k)$ is the image of $`\{0, \dots, k-1\}`$ under the injective function $e_{\text{seq}}$. Since $`|\{0, \dots, k-1\}| = k`$, injectivity ensures $|S^{\ast}(k)| = k$. $\blacksquare$

### Proposition 4.9 (Adding Stock Extends the Selected Set)
*Optimal allocation bundles are strictly monotonically nested with respect to endowment size:*

$$
\forall k_1, k_2 \in \mathbb{N}, \quad k_1 < k_2 \le N \implies S^{\ast}(k_1) \subsetneq S^{\ast}(k_2)
$$

**Proof.** If $r < k_1$, then $r < k_2$, so $e_{\text{seq}}(r) \in S^{\ast}(k_2)$, establishing $S^{\ast}(k_1) \subseteq S^{\ast}(k_2)$. Furthermore, $e_{\text{seq}}(k_1) \in S^{\ast}(k_2)$ while $e_{\text{seq}}(k_1) \notin S^{\ast}(k_1)$. Thus the inclusion is strict. $\blacksquare$

### Definition 4.10 (Comparison of Two Allocated Sets)
Bundle $S_1 \subseteq E_1(m)$ **Mengerian-dominates** bundle $S_2 \subseteq E_1(m)$, denoted $S_1 \succ_{\text{Menger}} S_2$, if:
1. $S_1 \setminus S_2$ is non-empty.
2. Every end in $S_1 \setminus S_2$ is strictly preferred to every end in $S_2 \setminus S_1$:

$$
S_1 \succ_{\text{Menger}} S_2 \iff (S_1 \setminus S_2).\text{Nonempty} \wedge \forall x \in S_1 \setminus S_2, \forall y \in S_2 \setminus S_1, \quad x \succ_{i,t,h} y
$$

### Theorem 4.11 (The First $k$ Ends Dominate Any Other Feasible Set)
The bundle $S^{\ast}(k)$ uniquely Mengerian-dominates every other feasible atomic bundle $S \subseteq E_1(m)$ with $|S| \le k$:

$$
\forall S \subseteq E_1(m), \quad |S| \le k \wedge S \neq S^{\ast}(k) \implies S^{\ast}(k) \succ_{\text{Menger}} S
$$

**Proof.** Because $S \neq S^{\ast}(k)$ and $|S| \le |S^{\ast}(k)| = k$, the set difference $S^{\ast}(k) \setminus S$ is non-empty. Let $x \in S^{\ast}(k) \setminus S$ and $y \in S \setminus S^{\ast}(k)$. By definition of $S^{\ast}(k)$, there exists $r < k$ such that $x = e_{\text{seq}}(r)$. Since $y \in S \setminus S^{\ast}(k)$, there exists $s \ge k$ such that $y = e_{\text{seq}}(s)$. Since $r < k \le s$, we have $r < s$. By Definition 4.2 (strict preference ranking), $e_{\text{seq}}(r) \succ_{i,t,h} e_{\text{seq}}(s)$, which is $x \succ_{i,t,h} y$. Thus $S^{\ast}(k) \succ_{\text{Menger}} S$. $\blacksquare$

### Definition 4.12 (The End Added by the $k$-th Unit)
For $1\le k\le N$, we call the end at position $k-1$ the marginal end associated with the $k$-th unit:

$$
\text{MU}_{i,t,h}(m, k) \equiv e_{\text{seq}}(k-1) \in \mathcal{E}
$$

### Theorem 4.13 (Earlier Units Add Higher-Ranked Ends)
For $1\le k_1 < k_2\le N$, the end added at $k_1$ is strictly preferred to the end added at $k_2$:

$$
\text{MU}_{i,t,h}(m, k_1) \succ_{i,t,h} \text{MU}_{i,t,h}(m, k_2)
$$

**Proof.** By Definition 4.12, $`\text{MU}_{i,t,h}(m, k_1) = e_{\text{seq}}(k_1 - 1)`$ and $`\text{MU}_{i,t,h}(m, k_2) = e_{\text{seq}}(k_2 - 1)`$. Since $`1 \le k_1 < k_2`$, subtracting 1 yields $`k_1 - 1 < k_2 - 1`$. By Definition 4.2 (Part 4), the sequence $`e_{\text{seq}}`$ is strictly ordered by preference:

$$
r < s \implies e_{\text{seq}}(r) \succ_{i,t,h} e_{\text{seq}}(s)
$$

Setting $r = k_1 - 1$ and $s = k_2 - 1$ directly establishes:

$$
e_{\text{seq}}(k_1 - 1) \succ_{i,t,h} e_{\text{seq}}(k_2 - 1) \iff \text{MU}_{i,t,h}(m, k_1) \succ_{i,t,h} \text{MU}_{i,t,h}(m, k_2)
$$

This proves the ranking for the sequence specified in Definition 4.2. $\blacksquare$

To deduce the realized allocation from purposeful choice, we ground actions in the `ActionFrame`'s teleological structure. Each action $\alpha$ produces a commodity bundle $\text{stockOf}(\alpha)$, so that its realized end is the bundle end:

$$
\text{outcome}(i, \alpha, t, h) = \text{BundleEnd}(\text{stockOf}(\alpha))
$$

When a feasible action $\alpha_{\text{opt}}$ attains the optimal allocation $S^{\ast}(k)$, requiring $k$ units of means $m$, while any alternative feasible nonpassive action $\alpha$ attains a suboptimal bundle requiring at most $k$ units, the optimal bundle teleologically dominates the suboptimal bundle:

$$
\text{SubjectiveTeleologicalDominates}(i, t, h, \text{stockOf}(\alpha_{\text{opt}}), \text{stockOf}(\alpha))
$$

By the foundational praxeological principle of the Action Frame (`teleological_bundle_dominance_induces_preference`), teleological bundle dominance natively induces strict preference between the realized ends:

$$
\text{outcome}(i, \alpha_{\text{opt}}, t, h) \succ_{i,t,h} \text{outcome}(i, \alpha, t, h)
$$

Under this teleological grounding, purposeful action mathematically mandates the realization of the optimal bundle.

### Theorem 4.14 (Purposeful Allocation Recovers the Ranked Sets)
At a fixed decision situation, let $1\le k_1 < k_2\le N$. For each $k\in\{k_1,k_2\}$, let $\mathcal{M}_{\text{bundle}}(k)$ be a bundle allocation menu in which feasible nonpassive actions are assigned finite bundles from $E_1(m)$ requiring at most $k$ units, with action $\alpha_{\text{opt}}(k)$ attaining $S^{\ast}(k)$. Let action ends be grounded in commodity bundles whose optimal allocation teleologically dominates suboptimal alternatives. If $\alpha_1$ and $\alpha_2$ are purposeful nonpassive actions in the respective allocation systems, then:
1. *Purposeful action uniquely forces the realization of the respective optimal bundles:*

$$
\text{bundleOf}(\alpha_1) = S^{\ast}(k_1) \quad \wedge \quad \text{bundleOf}(\alpha_2) = S^{\ast}(k_2)
$$

2. The marginal unit end added at $k_1$ is strictly preferred to the marginal unit end added at $k_2$:

$$
\text{MU}_{i,t,h}(m, k_1) \succ_{i,t,h} \text{MU}_{i,t,h}(m, k_2)
$$

**Proof.** Fix either $k=k_1$ or $k=k_2$, and let $\alpha$ be the corresponding purposeful nonpassive action. By definition of the bundle allocation menu, $\text{bundleOf}(\alpha) \subseteq E_1(m)$ requires at most $k$ units. If $\text{bundleOf}(\alpha) \neq S^{\ast}(k)$, Theorem 4.11 establishes that $S^{\ast}(k)$ strictly Mengerian-dominates it, so $\text{stockOf}(\alpha_{\text{opt}})$ teleologically dominates $\text{stockOf}(\alpha)$. By `teleological_bundle_dominance_induces_preference`, this teleological dominance induces strict preference:

$$
\text{outcome}(i, \alpha_{\text{opt}}, t, h) \succ_{i,t,h} \text{outcome}(i, \alpha, t, h)
$$

Because $\alpha_{\text{opt}}$ is feasible, this strict preference contradicts the undominatedness clause of purposeful human action ($\mathsf{P}(i, t, h, \alpha)$). Therefore, $\text{bundleOf}(\alpha) = S^{\ast}(k)$. Applying this to $k_1$ and $k_2$, the marginal-end comparison now follows directly from Theorem 4.13. $\blacksquare$

---

## Marginal Sacrifice on Finite Preference Orders

The atomic case specified which end the allocation adds. For a general finite set, we can guarantee only that some end is least urgent under a transitive ranking. We prove that existence next; to say that a particular resource reduction sacrifices that end, we must also specify how the allocation changes.

### Definition 4.15 (A Least-Urgent End)
Let $S \subseteq \mathcal{E}$ be a non-empty finite set of ends fulfilled by an agent's available means. An end $e_{\text{min}} \in S$ is a **least-urgent end** of $S$ if no other fulfilled end in $S$ is strictly less preferred than $e_{\text{min}}$:

$$
\text{IsLeastUrgentEnd}(\succ_{i,t,h}, S, e_{\text{min}}) \iff e_{\text{min}} \in S \wedge \forall e \in S, \quad \neg(e_{\text{min}} \succ_{i,t,h} e)
$$

### Lemma 4.16 (Finite Strict Orders Have Minimal Elements)
Let $S$ be a non-empty finite set and let $\succ$ be a strict partial order (irreflexive and transitive) on $S$. Then there exists at least one element $m \in S$ that is minimal with respect to $\succ$:

$$
\exists m \in S, \quad \forall x \in S, \quad \neg(m \succ x)
$$

**Proof.** We proceed by induction on the cardinality $|S| = n \ge 1$.
- Base case $n = 1$: $`S = \{x\}`$. By irreflexivity, $\neg(x \succ x)$. Thus $x$ is minimal.
- Inductive step: Assume the property holds for all sets of cardinality $n$. Let $|S| = n + 1$. Pick an arbitrary element $y \in S$, and consider $`S' = S \setminus \{y\}`$. Since $|S'| = n$, by the inductive hypothesis there exists a minimal element $m' \in S'$.
  - Case 1: If $\neg(m' \succ y)$, then for all $x \in S$, $\neg(m' \succ x)$ (since $x \in S'$ implies $\neg(m' \succ x)$ by minimality of $m'$ in $S'$, and $x = y$ holds by hypothesis). Thus $m'$ is minimal in $S$.
  - Case 2: If $m' \succ y$, we claim that $y$ is minimal in $S$. Suppose by contradiction that there exists $z \in S$ such that $y \succ z$. If $z = y$, this contradicts irreflexivity. If $z \in S'$, then by transitivity $m' \succ y$ and $y \succ z$ imply $m' \succ z$, contradicting the minimality of $m'$ in $S'$. Thus $\forall x \in S, \neg(y \succ x)$, and $y$ is minimal in $S$.

In all cases, a minimal element exists. $\blacksquare$

### Lemma 4.17 (A Finite Set Contains a Least-Urgent End)
Let $S \subseteq \mathcal{E}$ be a non-empty finite set of fulfilled ends, and let $\succ_{i,t,h}$ be transitive and asymmetric. Then some end in $S$ is not strictly preferred to any end in $S$:

$$
\exists e_{\text{sacrifice}} \in S, \quad \text{IsLeastUrgentEnd}(\succ_{i,t,h}, S, e_{\text{sacrifice}})
$$

This lemma identifies a minimal element of a finite strict order. It does not by itself show that losing a unit causes that end to be sacrificed; that conclusion requires an allocation rule linking feasible bundles to the ranked ends.

**Proof.** Asymmetry implies irreflexivity. Transitivity and irreflexivity satisfy the hypotheses of Lemma 4.16, which supplies an element $e_{\text{sacrifice}}$ for which no $e\in S$ satisfies $e_{\text{sacrifice}}\succ_{i,t,h}e$. This is exactly the required minimality condition. $\blacksquare$

---

## Complementarity and Teleological Quanta

The one-unit assumption can fail when an end requires complementary means. We now group the quantity needed for one listed end into a quantum. This lets us distinguish complete units that support an end from a remainder that, under the specified requirements, supports none of the listed ends.

### Example 4.18 (A Pair of Complementary Shoes)
Suppose walking requires one left shoe and one right shoe. Hold the number of right shoes at zero, and let $a(k)$ record whether walking is attainable with $k$ left shoes:

$$
a(k)=\begin{cases}1&k\ge 2,\\0&k<2.\end{cases}
$$

Thus $a(0)=a(1)=0$ while $a(2)=1$. The first additional shoe does not make the end attainable; the second does. This example concerns the stated complementary technology and does not define a general preference ranking over quantities.

For this technology, the smallest useful bundle consists of a left shoe and a right shoe. The relevant quantity for the walking end is therefore a pair, even though the inventory records individual shoes.

### Definition 4.19 (A Regime of Fixed-Size Requirements)
Let $m \in \mathcal{M}$ be a means and let $q_{\text{min}} \ge 1$ be the minimal technological quantum required to fulfill an independent end. A **teleological quantum regime** of order $N$ with quantum size $q_{\text{min}}$ is a structure:

$$
\mathcal{R}_{\text{teleo}}(i, t, h, m, N, q_{\text{min}}) = \langle q_{\text{min}}, k, e_{\text{seq}} \rangle
$$

where:
1. $q_{\text{min}} \ge 1$.
2. The physical endowment satisfies $\omega(i, t, h, m) = k \cdot q_{\text{min}}$, meaning the agent possesses exactly $k$ complete teleological units.
3. $k < N$.
4. $`e_{\text{seq}} : \{0, \dots, N-1\} \to \mathcal{E}`$ is injective and strictly ranked:

$$
r < s \implies e_{\text{seq}}(r) \succ_{i,t,h} e_{\text{seq}}(s)
$$

5. **Quantum Technological Requirement**: Every atomic end requires exactly $q_{\text{min}}$ physical units:

$$
\forall r \in \{0, \dots, N-1\}, \quad \rho(e_{\text{seq}}(r), m) = q_{\text{min}}
$$

Write $`E_q(m)=\{e_{\text{seq}}(r):0\le r < N\}`$ for the finite set of ends in this regime. This distinguishes a $`q_{\text{min}}`$-unit requirement from the one-unit atomic regime of Definition 4.3.

### Lemma 4.20 (Complete Quanta Bound the Number of Ends)
For any bundle of ends $S \subseteq E_q(m)$, if the total physical requirement satisfies $\sum_{e \in S} \rho(e, m) \le k \cdot q_{\text{min}}$, then:

$$
|S| \le k
$$

**Proof.** By Definition 4.19, $\rho(e, m) = q_{\text{min}}$ for all $e \in S$. Therefore:

$$
\sum_{e \in S} \rho(e, m) = |S| \cdot q_{\text{min}}
$$

The feasibility inequality gives $|S| \cdot q_{\text{min}} \le k \cdot q_{\text{min}}$. Since $q_{\text{min}} \ge 1 > 0$, dividing both sides by $q_{\text{min}}$ yields $|S| \le k$. $\blacksquare$

### Definition 4.21 (The End Added by the $k$-th Quantum)
For an agent possessing $k$ complete teleological quanta ($1 \le k \le N$), we call the end added by the $k$-th quantum its **marginal end**:

$$
\text{MU}_{\text{teleo}}(m, k) \equiv e_{\text{seq}}(k-1) \in \mathcal{E}
$$

### Theorem 4.22 (Earlier Quanta Add Higher-Ranked Ends)
For any teleological quantum increments $1 \le k_1 < k_2 \le N$, the marginal end of the earlier quantum is strictly preferred to the marginal end of the later quantum:

$$
\text{MU}_{\text{teleo}}(m, k_1) \succ_{i,t,h} \text{MU}_{\text{teleo}}(m, k_2)
$$

**Proof.** Exactly identical to Theorem 4.13: $k_1 - 1 < k_2 - 1$, and the strict ranking of $e_{\text{seq}}$ ensures $e_{\text{seq}}(k_1 - 1) \succ_{i,t,h} e_{\text{seq}}(k_2 - 1)$. $\blacksquare$

### Theorem 4.23 (A Remainder Cannot Complete Another Listed Quantum)
Suppose an endowment contains $k$ complete quanta and a remainder $r < q_{\text{min}}$:

$$
\omega(i, t, h, m) = k \cdot q_{\text{min}} + r
$$

Then for any bundle of ends $S \subseteq E_q(m)$, the feasibility constraint $\sum_{e \in S} \rho(e, m) \le k \cdot q_{\text{min}} + r$ still forces:

$$
|S| \le k
$$

Thus no feasible bundle of these ends contains more than $k$ ends. The conclusion concerns attainability in this regime; it does not assert indifference to every use or possession of the remainder.

**Proof.** The feasibility condition states $|S| \cdot q_{\text{min}} \le k \cdot q_{\text{min}} + r$. Suppose by contradiction that $|S| \ge k + 1$. Then:

$$
(k + 1) \cdot q_{\text{min}} \le |S| \cdot q_{\text{min}} \le k \cdot q_{\text{min}} + r
$$

Expanding the left side yields $k \cdot q_{\text{min}} + q_{\text{min}} \le k \cdot q_{\text{min}} + r$, which implies $q_{\text{min}} \le r$. This directly contradicts the assumption that $r < q_{\text{min}}$. Therefore, $|S| \le k$. $\blacksquare$

### Corollary 4.24 (Two-Unit Requirements)
Suppose each end in the finite ordered sequence requires exactly two units of a given means. The effective quantum size is then $q_{\text{min}}=2$. An inventory of $2k+r$ units, with $r<2$, can support at most $k$ of the listed ends, and the successive marginal ends follow the strict order stipulated in Definition 4.19:

$$
\text{MU}_{\text{teleo}}(m,1) \succ_{i,t,h} \text{MU}_{\text{teleo}}(m,2)
$$

**Proof.** Substitute $q_{\text{min}}=2$ into Theorems 4.22 and 4.23. $\blacksquare$

### Theorem 4.25 (Attainability Inclusion Rules Out Strict Dominance)
If every finite end set attainable under $b_1$ is also attainable under $b_2$:

$$
\forall S \subseteq_{\text{fin}} \mathcal{E}, \quad \text{attains}(\rho, b_1, S) \implies \text{attains}(\rho, b_2, S)
$$

then $b_1$ does not strictly dominate $b_2$ under the attainability-based relation:

$$
\neg \triangleright_{\mathrm{T}}(\rho, b_1, b_2)
$$

This implication is general for the stated attainability relation. The quantum assumptions give one application: a remainder smaller than the listed requirement cannot create an additional attainable end set. We have not thereby ranked every physical use of that remainder.

**Proof.** Suppose by contradiction that $\triangleright_{\mathrm{T}}(\rho, b_1, b_2)$. By Definition 1.8, there exists an end-set $S^{\ast}$ such that $\text{attains}(\rho, b_1, S^{\ast}) \wedge \neg \text{attains}(\rho, b_2, S^{\ast})$. But the hypothesis asserts that any set attainable under $b_1$ is attainable under $b_2$, forcing $\text{attains}(\rho, b_2, S^{\ast})$, an immediate contradiction. $\blacksquare$

### Theorem 4.26 (A Missing Complement Can Make Extra Stock Unproductive)
*Suppose every nonempty end requires both a left-shoe means and a right-shoe means. A bundle with one left shoe and no right shoe therefore attains no nonempty end, just as the zero bundle does. Under the attainability-based order:*

$$
\neg \triangleright_{\mathrm{T}}(\rho, b_{\text{left}}, b_{\text{zero}})
$$

The two bundles differ physically, but the stated technology gives them the same attainable end sets. This is enough to block strict attainability-based dominance; it does not, by itself, order every preference over bundles.

**Proof.** By hypothesis, no nonempty end-set is attainable under either bundle, while the empty set is attainable under both. Every end-set attainable under the first bundle is therefore attainable under the zero bundle. Theorem 4.25 gives the conclusion. $\blacksquare$

---

## Current Choice and the Uses of Productive Factors

We now return to a choice at one decision situation. Past expenditure is absent from the purposeful-choice conditions, while current feasibility and preference remain relevant. We then compare two downstream allocations whose available stocks differ because of an earlier production step, and finish by distinguishing restricted uses from viable alternatives.

### Theorem 4.27 (Purposefulness Depends on the Present Comparison)
Suppose a nonpassive action does not lead to an end preferred to inaction at the decision situation:

$$
\neg(\text{outcome}(i, \alpha_{\text{boondoggle}}, t, h) \succ_{i,t,h} \text{outcome}(i, \alpha_0, t, h))
$$

Then it is not purposeful there, regardless of prior expenditure:

$$
\alpha_{\text{boondoggle}} \neq \alpha_0 \implies \neg \mathsf{P}(i, t, h, \alpha_{\text{boondoggle}})
$$

**Proof.** Since $\alpha_{\text{boondoggle}}\ne\alpha_0$, purposefulness requires its outcome to be strictly preferred to the passive outcome. The premise denies that comparison, so the action fails the purposeful-choice condition. Prior expenditure does not enter this decision-context comparison. $\blacksquare$

The next result compares two actions whose realized outcomes are commodity bundles. The difference in ends follows from the ranked schedule, while the preference conclusion is derived directly from the Action Frame's teleological bundle dominance.

### Theorem 4.28 (The Marginal End Distinguishes the Two Allocations)
Let $1\le k\le N$. In a bundle allocation system, let feasible action $\alpha_{\text{opt}}$ realize bundle $S^{\ast}(k)$ and feasible action $\alpha_{\text{loseFactor}}$ realize bundle $S^{\ast}(k-1)$, with outcomes grounded in their respective commodity bundles. Then:
1. Writing $B(\alpha)$ for the end bundle assigned to action $\alpha$, the net difference between the bundles is the singleton marginal consumer end:

$$
B(\alpha_{\text{opt}}) \setminus B(\alpha_{\text{loseFactor}}) = \{ \text{MU}_{i,t,h}(m, k) \}
$$

2. The intended end of $\alpha_{\text{opt}}$ is strictly preferred to the intended end of $\alpha_{\text{loseFactor}}$:

$$
\text{outcome}(i, \alpha_{\text{opt}}, t, h) \succ_{i,t,h} \text{outcome}(i, \alpha_{\text{loseFactor}}, t, h)
$$

**Proof.**
1. By Definition 4.12, $S^{\ast}(k) \setminus S^{\ast}(k-1) = \{ e_{\text{seq}}(k-1) \} = \{ \text{MU}_{i,t,h}(m, k) \}$.
2. The optimal bundle $S^{\ast}(k)$ strictly Mengerian-dominates $S^{\ast}(k-1)$: the set difference is the singleton marginal end by part 1, and the reverse difference is empty. The commodity bundle of $\alpha_{\text{opt}}$ therefore teleologically dominates that of $\alpha_{\text{loseFactor}}$. By `teleological_bundle_dominance_induces_preference`, this teleological dominance natively induces strict preference between the action outcomes. $\blacksquare$

### Theorem 4.29 (An Earlier Production Step Changes a Later Menu)
Suppose two histories $h_{\text{build}}$ and $h_{\text{cons}}$ share $t_0$ and then separate. At $t_0$ the agent has $k-1$ units of $m$ on both histories; Chapter 2's physical invariance condition accounts for the equality of these stocks. Let $t_1$ and $t_2$ be immediate successors of $t_0$ on the respective histories. The agent enacts a nontrade action at $t_0$ that uses zero and yields one unit of $m$ on $h_{\text{build}}$, and a nontrade action that uses and yields zero units of $m$ on $h_{\text{cons}}$. Suppose all other requirements of a later action are met on both histories, and that this action requires $k$ units of $m$:
1. Along the capital-building trajectory, $\omega(i, t_1, h_{\text{build}}, m) = k$, making optimal action $\alpha_{\text{opt}}$ feasible at $t_1$.
2. Along the history where no unit is produced, the stock remains $k-1$, so the action requiring $k$ units is infeasible.
3. Under the separate allocation assumptions of Theorem 4.28, the difference between the downstream bundles is the end associated with the $k$-th unit.

**Proof.** Apply the inventory transition equation on each history. Production raises the stock from $k-1$ to $k$; the other action leaves it at $k-1$. The requirement is therefore met only on the production history. Theorem 4.28 identifies the bundle difference when its allocation premises also hold. $\blacksquare$

### Theorem 4.30 (Restricted Uses and Viable Alternatives)
We compare a specified use that no longer improves on inaction with an alternative use that remains feasible, improves on inaction, and is undominated:
1. **Absolute Specificity**: If a dedicated capital factor is technologically restricted to producing a single consumer end $e_{\text{spec}}$ via action $\alpha_{\text{spec}}$, and $e_{\text{spec}}$ ceases to relieve felt unease over the baseline ( $\neg(e_{\text{spec}} \succ_{i,t,h} e_0)$ ), then $\alpha_{\text{spec}}$ is strictly disqualified from purposeful enactment:

$$
\neg \mathsf{P}(i, t, h, \alpha_{\text{spec}})
$$

*The specified action then fails the improvement requirement for purposeful choice.*
2. **Convertible Versatility**: If a versatile capital factor can alternatively produce a secondary consumer end $e_{\text{alt}}$ via action $\alpha_{\text{alt}}$, then even when the primary end collapses ( $\neg(e_{\text{prim}} \succ_{i,t,h} e_0)$ ), the factor's value is cushioned: $\alpha_{\text{alt}}$ remains ex-ante purposeful:

$$
\mathsf{P}(i, t, h, \alpha_{\text{alt}})
$$

provided $e_{\text{alt}} \succ_{i,t,h} e_0$ and the alternative is undominated among feasible actions.

**Proof.**
1. For $\alpha_{\text{spec}} \neq \alpha_0$, purposeful action requires $\text{outcome}(\alpha_{\text{spec}}) \succ e_0$. If $\neg(e_{\text{spec}} \succ e_0)$, the requirement fails, proving $\neg \mathsf{P}(i, t, h, \alpha_{\text{spec}})$.
2. For $`\alpha_{\text{alt}}`$, the hypotheses provide feasibility, execution, relief of unease ( $`e_{\text{alt}} \succ e_0`$ ), and undominatedness against all $`\beta \in \mathcal{A}_{\text{feas}}`$. These satisfy all conditions of Definition 3.8, establishing $`\mathsf{P}(i, t, h, \alpha_{\text{alt}})`$. $\blacksquare$

### Theorem 4.31 (Attainability Inclusion Rules Out Strict Dominance)
Suppose a bundle $b_{stranded}$ and a comparison bundle $b_{zero}$ satisfy this explicit condition: every finite set of ends jointly attainable under $b_{stranded}$ is also jointly attainable under $b_{zero}$. Then:

$$
\neg \triangleright_{\mathrm{T}}(\rho, b_{\text{stranded}}, b_{\text{zero}})
$$

One sufficient economic case is complement starvation: all ends using a particular capital good also require a complementary good, the stranded bundle falls below the required complement quantity, and the comparison bundle matches the stranded bundle in all other goods while removing the unusable capital. Those premises make the stated attainability inclusion transparent. Complement shortfall alone, without the comparison of other stocks and the requirements of all relevant ends, is not enough to establish the inclusion. This conclusion concerns the attainability order; it does not rank every physical use of the stock.

**Proof.** The premise is exactly the inclusion hypothesis of Theorem 4.25. Therefore strict attainability-based dominance is impossible. $\blacksquare$

### Theorem 4.32 (Present-Endowment Choice Invariance)
In any action frame, suppose an agent at decision moment $t$ across two histories $`h_1`$ and $`h_2`$ possesses identical present physical inventories ( $`\forall m, \omega(i, t, h_1, m) = \omega(i, t, h_2, m)`$ ), faces identical contemplated action menus ( $`\mathcal{A}_{\text{cont}}(i, t, h_1) = \mathcal{A}_{\text{cont}}(i, t, h_2)`$ ), and evaluates prospective ends with identical preference relations. Then:
1. Feasible action menus coincide: $`\mathcal{A}_{\text{feas}}(i, t, h_1) = \mathcal{A}_{\text{feas}}(i, t, h_2)`$.
2. An action is undominated on $h_1$ if and only if it is undominated on $h_2$.

This coincidence holds regardless of differing physical factor quantities expended at earlier historical transitions $t_{\text{past}} \prec t$. Purposeful choice depends on current physical stocks and expected prospective ends, not on sunk historical outlays.

**Proof.** The feasibility coupling condition gives $`\alpha \in \mathcal{A}_{\text{feas}} \iff \alpha \in \mathcal{A}_{\text{cont}} \wedge \forall m, u(\alpha, m) \le \omega(i, t, h, m)`$. Because contemplated menus and present inventories match coordinate-wise, feasible menus are identical. Because prospective ends and preferences are identical, the undominated choice conditions coincide. $\blacksquare$

## Conclusion

We have examined how requirements, stocks, and preference order can determine which ends are attainable, how successive units support ranked ends, and how productive means relate to the ends they help achieve. These comparisons remain conditional on the stated technologies and feasible alternatives. We now add uncertainty about which history will occur, so that we can distinguish present appraisal from later regret.
