# Chapter 12: State and Fiscal Political Economy

This chapter formalizes the political economy of the state, fiscal extraction, and judicial monopoly. Economic means (voluntary exchange) and political means (coercive extraction) are grounded directly in physical inventory transitions and counterfactual choice branches.

## The Praxeological Foundations of Hegemonic Interaction and State Monopoly

In a multi-agent setting, the Action Axiom partitions bilateral interactions into two mutually exclusive and exhaustive categories:
1. **Economic Means (Voluntary Exchange):** Neither participant initiates an invasive action contracting the other's clean-title physical endowment, and both strictly gain relative to their autonomous inaction baselines.
2. **Political Means (Coercive Extraction):** The aggressor's action physically contracts the victim's clean-title endowment on the passive counterfactual branch, forcibly stripping previously feasible purposeful actions from the victim's choice menu without consent.

A **Territorial Monopoly of Violence** arises when an institutional actor establishes two structural asymmetries:
1. **Monopoly on Aggression and Prohibition of Defense:** The ruler claims an exclusive license on physical invasion against subjects while designating subjects' defensive counter-actions and resistance as punishable infractions.
2. **Monopoly on Final Adjudication:** In any dispute between a subject and the state, the state (or its appointed tribunal) acts as the ultimate arbiter, making the ruler judge in its own cause.

## Economic and Political Means

To distinguish voluntary exchange from coercive extraction, we ground the interaction directly in physical stock transitions across counterfactual histories. Both subject $i$ and state $j$ possess physical endowments $\omega(i, t, h, m)$ at decision node $\langle t, h \rangle$. When $i$ enacts $\alpha_i$ and $j$ enacts $\alpha_j$, the realized joint counterfactual history branch is:

$$
\text{jointBranch}(i, j, t, h, \alpha_i, \alpha_j) = \sigma(j, t, \alpha_j, \sigma(i, t, \alpha_i, h))
$$

with post-action stock at subsequent transition moment $t'$ given by $\omega(i, t', \text{jointBranch}(i, j, t, h, \alpha_i, \alpha_j), m)$.

Physical invasion by the state, $`\text{Invasive}_{\mathrm{state}}(i, j, t, t', h, \alpha_{\text{tax}})`$, is an action that strictly contracts the subject's baseline physical stock when the subject is passive ($\alpha_0$):

$$
\exists m \in \mathcal{M}, \quad \omega(i, t', \text{jointBranch}(i, j, t, h, \alpha_0, \alpha_{\text{tax}}), m) < \omega(i, t, h, m)
$$

which by Chapter 8 is mathematically equivalent to stripping previously feasible purposeful actions from the subject's choice menu.

1. **Economic means (voluntary exchange):** An interaction $(\alpha_i, \alpha_j)$ is an economic means if and only if it is a voluntary exchange: neither party initiates an invasive action contracting the other's physical stock, and both strictly prefer the joint outcome to their autonomous status-quo baseline:
   
$$
\neg I_{i \to j}(\alpha_i) \wedge \neg I_{j \to i}(\alpha_j) \wedge O_i(\alpha_i, \alpha_j) \succ_i O_i(\alpha_0, \alpha_0) \wedge O_j(\alpha_i, \alpha_j) \succ_j O_j(\alpha_0, \alpha_0)
$$

2. **Political means (coercive extortion):** An interaction $(\alpha_i, \alpha_{\text{state}})$ is a political means if and only if it is coercive extortion: the state's action is physically invasive against the subject's physical stock ( $I_{\text{state} \to i}(\alpha_{\text{state}})$ ), the subject strictly prefers compliance to the threatened outcome, the subject strictly prefers the unmolested autonomous baseline to compliance, and the state strictly prefers the extraction outcome to the joint baseline:

$$
\begin{aligned}
&I_{\text{state} \to i}(\alpha_{\text{state}}) \\
\wedge\;&O_i(\alpha_{\text{comply}}, \alpha_{\text{state}}) \succ_i O_i(\alpha_0, \alpha_{\text{state}})\\
\wedge\;&O_i(\alpha_0, \alpha_0) \succ_i O_i(\alpha_{\text{comply}}, \alpha_{\text{state}})\\
\wedge\;&O_j(\alpha_{\text{comply}}, \alpha_{\text{state}}) \succ_j O_j(\alpha_0, \alpha_0)
\end{aligned}
$$

The comparison with the threatened outcome matters. Choosing compliance over punishment is a purposeful response to the threat, but it remains entirely distinct from voluntary gain relative to the unmolested baseline.

### Theorem 12.1 (The Coercive Invariance of Public Services Theorem)

Suppose a strictly positive quantity of public-service output accompanies compliance ( $0 < \text{publicGood}(\alpha_{\text{comply}}, \alpha_{\text{tax}})$ ). If the tax action is physically invasive against the subject's physical stock ( $I_{j \to i}(\alpha_{\text{tax}})$ ), the subject strictly prefers compliance to the threatened outcome, the subject strictly prefers the unmolested joint baseline to compliance, and the state strictly prefers the extraction outcome to the joint baseline, then:
1. the interaction is a political means (coercive extortion);
2. the interaction is not an economic means (voluntary exchange);
3. the subject's compliance is a purposeful response to the threat; and
4. public service provision remains strictly positive ( $0 < \text{publicGood}(\alpha_{\text{comply}}, \alpha_{\text{tax}})$ ).

**Proof.** The four preference and physical invasion premises satisfy all clauses in the definition of coercive extortion, classifying the interaction as a political means. Voluntary exchange requires that the state's action be non-invasive ( $\neg I_{j \to i}(\alpha_{\text{tax}})$ ), which directly contradicts the invasion premise. Positivity of the externally specified output quantity is preserved as an independent physical metric; it leaves the underlying stock contraction and preference comparisons intact. Compliance is purposeful because $O_i(\alpha_{\text{comply}}, \alpha_{\text{tax}}) \succ_i O_i(\alpha_0, \alpha_{\text{tax}})$. $\square$

This theorem is proven universally for all action frames. It establishes the exact conditions under which fiscal extraction constitutes coercive extortion: physical stock invasion paired with the victim's ordinal preference for unmolested property over extraction. Providing a public good represents an independent physical output, leaving the structural property invasion intact.

### Proposition 12.2 (Majoritarian Coalition Extraction is Political Means)

Let a subject $i$ face a tax policy enacted by a majoritarian coalition $j$. If the policy is physically invasive of $i$'s physical endowment ( $I_{j \to i}(\alpha_{\text{tax}})$ ), compliance under threat beats punishment, $i$ strictly prefers the non-tax baseline to compliance, and the coalition strictly prefers extraction to the baseline, then:
1. the interaction is a political means; and
2. the interaction is not an economic means.

$$
I_{j \to i}(\alpha_{\text{tax}}) \wedge O_i(\alpha_c, \alpha_t) \succ_i O_i(\alpha_0, \alpha_t) \wedge O_i(\alpha_0, \alpha_0) \succ_i O_i(\alpha_c, \alpha_t) \wedge O_j(\alpha_c, \alpha_t) \succ_j O_j(\alpha_0, \alpha_0) \implies \text{PoliticalMeans} \wedge \neg \text{EconomicMeans}
$$

**Proof.** The four hypotheses immediately satisfy the conditions of coercive extortion, establishing political means. Voluntary exchange requires non-invasion ( $\neg I_{j \to i}(\alpha_{\text{tax}})$ ), which directly contradicts the invasion premise. $\square$

The praxeological status of an act is determined strictly by physical invasion and revealed ordinal preference: majoritarian voting procedures preserve the formal structure of coercive extortion, as coalition size leaves the victim's property violation and preference ranking unchanged.

## Fiscal Incidence in an Action Frame: The Calhoun Class Partition

We now ground the fiscal transfer system directly in physical inventory transitions. Let $\text{Cohort} \subseteq \mathcal{I}$ be a finite set of agents.

### Definition 12.3 (Fiscal Transfer System)
A **Fiscal Transfer System** $\mathcal{F}$ consists of:
1. A finite cohort of agents $\text{Cohort} \subseteq \mathcal{I}$;
2. Initial physical endowments $\omega_{\text{pre}} : \mathcal{I} \to \mathbb{N}$;
3. Post-transfer physical endowments $\omega_{\text{post}} : \mathcal{I} \to \mathbb{N}$;
4. A deadweight loss $L \ge 0$ representing resources consumed in collection, administration, and rent-seeking dissipation;
5. The physical conservation law:

$$
\left(\sum_{a \in \text{Cohort}} \omega_{\text{post}}(a)\right) + L = \sum_{a \in \text{Cohort}} \omega_{\text{pre}}(a)
$$

### Definition 12.4 (Calhoun Fiscal Classes: Taxpayers and Tax-Consumers)
Under a fiscal transfer system $\mathcal{F}$, the cohort is partitioned into John C. Calhoun's two fundamental fiscal classes:
1. **Net Tax-Consumer:** An agent $s \in \text{Cohort}$ whose post-transfer endowment strictly exceeds their initial endowment: $\omega_{\text{pre}}(s) < \omega_{\text{post}}(s)$.
2. **Net Taxpayer:** An agent $b \in \text{Cohort}$ whose post-transfer endowment is strictly smaller than their initial endowment: $\omega_{\text{post}}(b) < \omega_{\text{pre}}(b)$.

### Theorem 12.5 (The Calhoun Fiscal Class Partition Theorem)
In any fiscal transfer system, if there exists at least one net tax-consumer, there strictly exists at least one net taxpayer:

$$
(\exists s \in \text{Cohort}, \ \omega_{\text{pre}}(s) < \omega_{\text{post}}(s)) \implies (\exists b \in \text{Cohort}, \ \omega_{\text{post}}(b) < \omega_{\text{pre}}(b))
$$

Furthermore, there is no universal fiscal dividend: it is impossible for every cohort member to weakly gain while at least one strictly gains, and impossible for all members of a nonempty cohort to strictly gain.

**Proof.** Suppose by contradiction that no cohort member is a net taxpayer. Then for every $a \in \text{Cohort}$, $\omega_{\text{pre}}(a) \le \omega_{\text{post}}(a)$. Because $s$ is a net tax-consumer, $\omega_{\text{pre}}(s) < \omega_{\text{post}}(s)$. Summing these inequalities over the finite cohort yields a strict inequality:

$$
\sum_{a \in \text{Cohort}} \omega_{\text{pre}}(a) < \sum_{a \in \text{Cohort}} \omega_{\text{post}}(a)
$$

However, by the conservation law of [Definition 12.3](#definition-123-fiscal-transfer-system) and nonnegativity of deadweight loss $L \ge 0$:

$$
\sum_{a \in \text{Cohort}} \omega_{\text{post}}(a) \le \left(\sum_{a \in \text{Cohort}} \omega_{\text{post}}(a)\right) + L = \sum_{a \in \text{Cohort}} \omega_{\text{pre}}(a)
$$

This contradicts the strict inequality, proving that at least one net taxpayer $b \in \text{Cohort}$ must exist. $\blacksquare$

### Theorem 12.6 (The Tullock Rent-Seeking Dissipation Theorem)
Let $\mathcal{F}$ be a fiscal transfer system over cohort $\text{Cohort}$. If the resources consumed in administrative friction, compliance, enforcement, or rent-seeking contest are strictly positive ($L > 0$), then the aggregate post-transfer physical endowment of the cohort is strictly less than the initial pre-transfer endowment:

$$
L > 0 \implies \sum_{a \in \text{Cohort}} \omega_{\text{post}}(a) < \sum_{a \in \text{Cohort}} \omega_{\text{pre}}(a)
$$

**Proof.** Immediate from the conservation equation $\sum \omega_{\text{post}} + L = \sum \omega_{\text{pre}}$ and $L > 0$. $\blacksquare$

[Theorem 12.6](#theorem-126-the-tullock-rent-seeking-dissipation-theorem) demonstrates that rent-seeking contests and coercive redistribution are physically negative-sum over the cohort. In the presence of dissipation, gains to net tax-consumers are strictly outweighed by the physical depletion imposed on taxpayers.

### Theorem 12.7 (The Calhoun Taxpayer Menu Stripping Theorem)
When the fiscal transfer system is induced by the physical inventory transition at $t \to t'$ on history $h$ with nontrade actions and zero physical yield in means $m$, the extraction of physical stock from a net taxpayer $b \in \text{Cohort}$ strictly strips previously feasible purposeful actions from $b$'s choice menu:

$$
\exists b \in \text{Cohort}, \forall \alpha \in \mathcal{A}, \quad
\left(\alpha \in \mathcal{A}_{\text{feas}}(b, t, h) \wedge \alpha \in \mathcal{A}_{\text{cont}}(b, t', h) \wedge \text{use}(\alpha, m) = \omega(b, t, h, m)\right) \implies \alpha \notin \mathcal{A}_{\text{feas}}(b, t', h)
$$

**Proof.** By [Theorem 12.5](#theorem-125-the-calhoun-fiscal-class-partition-theorem), the presence of a tax-consumer forces the existence of a net taxpayer $b$ whose stock contracts: $\omega(b, t', h, m) < \omega(b, t, h, m)$. Any action $\alpha$ requiring $b$'s full initial stock has $\text{use}(\alpha, m) = \omega(b, t, h, m) > \omega(b, t', h, m)$. By the feasibility coupling condition, $\alpha$ is infeasible at $t'$, proving that the state's fiscal extraction forcibly strips $\alpha$ from the taxpayer's choice menu. $\blacksquare$

### Definition 12.8 (Title-Anchored Fiscal System)
A **Title-Anchored Fiscal System** tracks legitimate property titles alongside physical transfers:
1. Initial physical endowments conform to clean title: $`\forall a \in \text{Cohort}, \ \text{title}_{\mathrm{pre}}(a) \le \omega_{\mathrm{pre}}(a)`$;
2. For every net taxpayer $b \in \text{Cohort}$, fiscal extraction reduces physical stock below clean title:

$$
\omega_{\mathrm{post}}(b) < \text{title}_{\mathrm{pre}}(b)
$$

### Theorem 12.9 (The Calhoun Fiscal Title Invasion and Bundle Dominance Theorem)
Under a title-anchored fiscal system:
1. Fiscal extraction from a net taxpayer $b$ constitutes a directed physical invasion of clean title ($I_{\mathrm{state} \to b}$);
2. If taxpayer $b$ evaluates outcomes by goal attainment (teleological bundle dominance), and $b$'s pre-tax stock achieves a valued goal $e$ requiring means $m$ ( $req(e, m) \le \omega_{\mathrm{pre}}(b, m)$ ) while the post-tax stock fails to achieve $e$ ( $\omega_{\mathrm{post}}(b, m) < req(e, m)$ ), then the pre-tax goods strictly teleologically dominate the post-tax goods:

$$
b_{\mathrm{pre}} \succ_{\mathrm{teleo}} b_{\mathrm{post}}
$$

Consequently, the taxpayer's welfare loss is deduced from objective physical requirements and goal achievement, rather than an arbitrary utility scalar.

**Proof.** Statement 1 follows directly from [Definition 12.8](#definition-128-title-anchored-fiscal-system): because $`\omega_{\mathrm{post}}(b) < \text{title}_{\mathrm{pre}}(b)`$ and $\omega_{\mathrm{post}}(b) < \omega_{\mathrm{pre}}(b)$, extraction reduces physical goods below legitimate title, meeting the definition of directed title invasion. Statement 2 follows because the pre-tax bundle contains enough means to attain goal $e$, while the post-tax bundle falls short. Because the pre-tax goods achieve $e$ and the post-tax goods fail to do so, the pre-tax bundle strictly teleologically dominates the post-tax bundle ($b_{\mathrm{pre}} \succ_{\mathrm{teleo}} b_{\mathrm{post}}$). $\blacksquare$

[Theorem 12.5](#theorem-125-the-calhoun-fiscal-class-partition-theorem) supplies a conservation result for one measured physical account: a net beneficiary entails a net payer. Identifying who paid requires individual-level or equivalent allocation data; classifying the transfer as coercive requires the relevant invasion and preference comparisons; and comparing welfare between persons requires a separate evaluative basis.

The same accounting conclusion applies to multi-moment inventory runs when every member's run has zero total yield in the means being tracked. Inventory balance then gives

$$
\sum_{a\in C}\omega_a(u)+\sum_{a\in C}\text{use}_a
=\sum_{a\in C}\omega_a(t),
$$

where $t$ and $u$ are the initial and terminal moments. Thus an increase in that means for one cohort member requires a decrease for at least one member, provided the cohort is finite and the stated zero-yield condition holds. Uses account for any additional reduction in the cohort's total stock.

### Proposition 12.10 (A Beneficiary Requires a Loss in a Zero-Yield Cohort)
Let $C$ be a finite cohort, and suppose each member's inventory run has zero total yield in means $m$. If an operator belongs to $C$ and its stock of $m$ strictly increases from $t$ to $u$, then some member of $C$ has a strictly smaller stock at $u$ than at $t$.

**Proof.** Summing the inventory balance over the finite cohort, zero total yield gives

$$
\sum_{a\in C}\omega(a,u,h,m)+\sum_{a\in C}\text{use}_a(m)
=\sum_{a\in C}\omega(a,t,h,m).
$$

Since uses are nonnegative, total terminal stock is no greater than total initial stock. If no member lost stock, every terminal stock would be at least its initial stock; the operator's strict increase would make the total terminal stock strictly greater. This contradicts the inequality. $\square$

## Production and a Fiscal Claim

Let gross output be $Y$, a fiscal claim be $T$, and a leisure benchmark be $V$. Assume the action menu contains production and inaction, both are feasible, and the model's binary appraisal rule ranks the production end above the leisure end exactly when the net comparison is $Y > V+T$. Under this rule, producing is purposeful only when it is enacted and $V+T < Y$. When $Y\le V+T$, the production action is not purposeful; since these are the only feasible actions, any purposeful action in the menu must be inaction.

This result is a binary-choice module: given the stated appraisal rule, menu, and feasibility conditions, its integer comparison classifies production versus inaction. Applying it to other tax settings supplies the corresponding output, claim, benchmark, preference, and menu inputs.

### Proposition 12.11 (Downsian Voter Non-Pivotality Blocks Purposeful Voting)

Let an agent $i$ face a binary choice between active voting ($\alpha_{\text{vote}} \neq \alpha_0$) and abstaining ($\alpha_0$). If voting yields an outcome no better than abstaining ($a \le b$, for example because a single vote has zero chance of changing the election outcome), then voting cannot be purposeful:

$$
a \le b \implies \neg \mathsf{P}(i, t, h, \alpha_{\text{vote}})
$$

More generally, if an active choice $\alpha \neq \alpha_0$ yields the exact same end as baseline inaction ( $\text{outcome}(i, \alpha, t, h) = \text{outcome}(i, \alpha_0, t, h)$ ), $\alpha$ cannot be purposeful:

$$
\alpha \neq \alpha_0 \wedge \text{outcome}(i, \alpha, t, h) = \text{outcome}(i, \alpha_0, t, h) \implies \neg \mathsf{P}(i, t, h, \alpha)
$$

**Proof.** Purposeful active choice requires strictly preferring the active outcome to inaction ($b < a$); when $a \le b$, this fails. More generally, purposeful active choice requires $\text{outcome}(\alpha) \succ_{i,t,h} \text{outcome}(\alpha_0)$; if the two outcomes are identical, this would require preferring an outcome strictly to itself, which contradicts the irreflexivity of preference. $\square$

This proposition clarifies why people vote from a praxeological perspective. When casting a ballot takes time and effort without changing the electoral outcome, voting to achieve a political result is not purposeful. When people do choose to vote, they do so for the direct satisfaction of participating (expressive voting), not as an effective instrument to change policy.

## A Conditional Comparison of Fiscal Horizons

The model can encode two agents with different numerical rates and fiscal decisions. Let $g$ be a future tax base, $q_s$ and $q_c$ two positive rates, and $G>0$ a gain parameter. The relevant comparisons are

$$
Gq_s < g < Gq_c.
$$

The first inequality makes restraint preferable to extraction for the stationary ruler; the second makes extraction preferable to restraint for the caretaker. These are fiscal choices about taking a current gain while preserving a future tax base, not production-versus-inaction decisions. They imply $q_s < q_c$, since $Gq_s < Gq_c$ and $G>0$. A weak comparison $g\le Gq_c$ also appears in the model's hypotheses, but the strict inequality is needed for purposeful extraction.

More completely, the model's evidence also specifies a viable moderate claim and a prohibitive higher claim:

$$
V+T_m < Y,
\qquad
Y\le V+T_h.
$$

### Proposition 12.12 (Purposeful Fiscal Choice under the Stated Bounds)

Assume the two fiscal decisions each have only extraction and fiscal restraint as alternatives, and assume the modeled enactments: the stationary ruler enacts restraint and the caretaker enacts extraction. If $Gq_s < g < Gq_c$, then $q_s < q_c$, restraint is purposeful for the stationary ruler, and extraction is purposeful for the caretaker. The corresponding opposite choices are not purposeful.

**Proof.** Since $G>0$, the inequalities imply $q_s < q_c$. The stationary ruler's comparison places the future tax base above the current extraction gain, so restraint is preferred and purposeful when enacted. The caretaker's comparison reverses this ranking, so extraction is preferred and purposeful when enacted. In each binary menu, the opposite choice is strictly dominated. $\square$

The terms “stationary” and “caretaker” label the two roles in this scenario. Applying them to historical actors composes the result with evidence for the corresponding roles, rates, appraisals, and enactments.

## Adjudication by the Interested Ruler

### Proposition 12.13 (A Preferred Expansion Excludes the Limiting Decision)

Suppose a ruler's tribunal is the final arbiter in a dispute between the ruler and a subject. If an expansion action is feasible for the ruler and the ruler strictly prefers its outcome to the outcome of enforcing a limitation, then the limitation is not a purposeful action of that tribunal in the specified decision context.

**Proof.** The tribunal's action is identified with the ruler's action by the adjudication condition. The feasible expansion then strictly dominates the proposed limitation, contradicting the undominatedness condition for purposeful action. $\square$

[Proposition 12.13](#proposition-1213-a-preferred-expansion-excludes-the-limiting-decision) composes the adjudication rule, which identifies the tribunal's action with the ruler's, with two decision inputs: the ruler's stated preference and the expansion's feasibility. Those inputs establish when the limiting decision fails the purposefulness condition.

## Protected Entry and Calculation Uncertainty

Let $U_s$ be the modeled uncertainty of using spot-market comparisons and $U_f$ the modeled uncertainty of internal calculation. For factor-price spread $W$, grid step $g$, transaction volume $z$, and internal blur components $b_1,b_2,b_3$, define

$$
U_s=(W+g)z,\qquad U_f=(b_1+b_2+b_3)z.
$$

The following result uses a binary appraisal scenario: the operator compares continuing activity with an outside benchmark that includes an entry penalty; the entrant compares entry with its corresponding penalized benchmark. Execution and the two-action menus are explicit parts of the scenario.

### Proposition 12.14 (Entry Penalty and Purposeful Continuation)
Suppose $z>0$ and

$$
U_s < U_f < U_s+\Pi,
$$

where $\Pi$ is the entry penalty. The operator's binary appraisal compares the outside spot-market uncertainty plus the penalty, $U_s+\Pi$, with internal calculation uncertainty, $U_f$. The entrant faces the reverse comparison. If the operator executes its active action, it is purposeful; the entrant's entry action is not purposeful. The first inequality says internal calculation uncertainty exceeds spot uncertainty, while the second says the statutory penalty makes outside entry costlier than the incumbent's internal calculation uncertainty.

**Proof.** In the operator's binary appraisal, $U_s+\Pi > U_f$, so the executed active choice is preferred to its baseline and is purposeful. The entrant would need $U_f > U_s+\Pi$ for entry to be purposeful, contrary to the assumed inequality. $\square$

[Proposition 12.14](#proposition-1214-entry-penalty-and-purposeful-continuation) supplies a binary entry-and-continuation comparison under its stated appraisal and execution premises. An application to a particular firm supplies evidence for those premises; when its inventory run also has zero total yield in a tracked means and the protected operator's stock rises, [Proposition 12.10](#proposition-1210-a-beneficiary-requires-a-loss-in-a-zero-yield-cohort) composes with it to establish a cohort loss.

## The State Monopoly Master Synthesis

The chapter's derivations unite into an integrated master synthesis grounded directly in the Action Axiom:

### Theorem 12.15 (The State Monopoly Political Economy Master Synthesis)

Suppose an Action Frame combines:
1. an endogenous property interaction between a subject and the state involving taxation with public goods; and
2. a territorial judicial monopoly where the ruler adjudicates disputes with subjects.

Then:
1. Fiscal extraction is political, not economic: The fiscal interaction is a political means (coercive extortion) and cannot be an economic means (voluntary exchange).
2. The monopoly arbiter cannot purposefully limit the ruler: The monopoly arbiter cannot purposefully enact a limiting decision against the ruler.

**Proof.** By [Theorem 12.1](#theorem-121-the-coercive-invariance-of-public-services-theorem), the endogenously invasive tax satisfies coercive extortion and contradicts voluntary exchange. By [Proposition 12.13](#proposition-1213-a-preferred-expansion-excludes-the-limiting-decision), since the arbiter's action is identified with the ruler's and the expansion action is feasible and strictly preferred over the limitation, the limitation is strictly dominated and cannot be a purposeful act of the arbiter. $\square$

## Conclusion

We have analyzed the political economy of the state, fiscal extraction, and judicial monopoly from the foundations of purposeful action, physical inventory transitions, and choice menu stripping. In this framework, the structural characteristics of state power—clean-title invasion, fiscal extraction, and the impossibility of judicial self-restraint—follow deductively from the formal conditions of purposeful choice under physical scarcity. We now examine how monetary credit expansion interacts with capital structure and intertemporal production.
