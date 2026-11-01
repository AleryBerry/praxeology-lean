# Chapter 11: Organization, Firms, and Intervention

We compare market coordination with organized production and intervention. Each organizational or policy conclusion is stated for the particular information, price, and action conditions assumed.

> **Prerequisites and scope:** Chapters 1–10. We use bounded price knowledge and purposeful choice to analyze organizational boundaries, tender rules, intervention, and conditional credit-distortion results.

Prices communicate comparisons among heterogeneous inputs, but entrepreneurs may know only bounded or coarsened prices. The chapter develops those bounds before asking how production integration changes signals and where the firm boundary lies.

## Price Boxes and Robust Cost Comparison

Entrepreneurs often know a range of possible input prices rather than one exact vector. A price box gives bounds on costs; robust separation identifies plans whose ranking is unchanged throughout the box, while an indeterminacy cone records pairs for which rankings may reverse.

### Definition 11.1 (Input Plans and Catallactic Cost)
For $d$ distinct input categories, an **input plan** is a vector

$$
x : \text{Fin}(d) \to \mathbb{N}.
$$

Given a discrete price vector $P : \text{Fin}(d) \to \mathbb{N}$, the **catallactic cost** of plan $x$ is

$$
\text{Cost}_d(P,x)=\sum_{r\in\text{Fin}(d)} P(r)x(r).
$$

This is a monetary total in the unit of account. Its use depends on market prices supplying a common unit for the different inputs.

An observed price need not be a single exact number. Chapter 9's discrete marginal-pair bounds give a natural way to represent what is known about each price.

### Definition 11.2 (Price Box and Interval Width)
A **price box** $\mathcal{B}$ has lower and upper vectors $P_{\text{low}}$ and $P_{\text{high}}$, with $P_{\text{low}}(r)\le P_{\text{high}}(r)$ for every input $r$. Its admissible prices are

$$
\mathcal{B}(P_{\text{low}},P_{\text{high}})
=\{P\mid \forall r,\ P_{\text{low}}(r)\le P(r)\le P_{\text{high}}(r)\}.
$$

The interval width $W_r$ for input $r$ is the unique natural-number remainder satisfying

$$
P_{\text{low}}(r)+W_r=P_{\text{high}}(r).
$$

The interval records bounded price knowledge. It does not by itself specify a probability distribution or an entrepreneur's beliefs about which admissible price will occur.

### Lemma 11.3 (Cost Bounds from a Price Box)
If $P\in\mathcal{B}(P_{\text{low}},P_{\text{high}})$, then every input plan has a lower and upper cost bound:

$$
\sum_r P_{\text{low}}(r)x(r)
\le \text{Cost}_d(P,x)
\le \sum_r P_{\text{high}}(r)x(r).
$$

**Proof.** Each input quantity is nonnegative. Multiplying the componentwise price bounds by $x(r)$ preserves their direction, and summing over the finitely many inputs gives both inequalities. $\blacksquare$

The bounds let us distinguish a ranking that holds at every admissible price from one that depends on the exact realization.

### Theorem 11.4 (Robust Cost Separation)
Suppose the worst-case cost of plan $x$ is below the best-case cost of plan $y$:

$$
\sum_r x(r)P_{\text{high}}(r)
<\sum_r y(r)P_{\text{low}}(r).
$$

Then $x$ is strictly cheaper than $y$ under every price vector in the box:

$$
\forall P\in\mathcal{B}(P_{\text{low}},P_{\text{high}}),\quad
\text{Cost}_d(P,x)<\text{Cost}_d(P,y).
$$

**Proof.** By Lemma 11.3, the realized cost of $x$ is no greater than its upper bound, and the lower bound for $y$ is no greater than its realized cost. The strict separation of those bounds therefore implies the strict realized-cost comparison for every admissible $P$. $\blacksquare$

This is an epistemic compression result: when the bounds separate the methods, the public price box suffices to establish the ranking. The conclusion is independent of any additional private state used to select a realized price, provided that price remains in the box. When the bounds overlap, this theorem gives no ranking.

### Definition 11.5 (Price-Box Indeterminacy Cone)
Two input plans $x$ and $y$ lie in the **indeterminacy cone** of a price box if admissible prices can rank them in opposite directions:

$$
\begin{aligned}
\text{Indeterminate}_{\mathcal{B}}(x,y)\iff\;&
\exists P_1,P_2\in\mathcal{B}(P_{\text{low}},P_{\text{high}}),\\
&\text{Cost}_d(P_1,x)<\text{Cost}_d(P_1,y),\\
&\text{Cost}_d(P_2,y)<\text{Cost}_d(P_2,x).
\end{aligned}
$$

The definition requires two witnesses inside the same box. A mere difference in cost levels is not indeterminacy; the ordering must reverse.

### Proposition 11.6 (Componentwise Dominance Excludes Indeterminacy)
If $x$ uses no more of any input than $y$,

$$
\forall r,\quad x(r)\le y(r),
$$

then $x$ and $y$ cannot lie in the indeterminacy cone of any price box.

**Proof.** At every admissible price, all prices and quantities are nonnegative. Thus $P(r)x(r)\le P(r)y(r)$ for every input, so summing gives $`\text{Cost}_d(P,x)\le\text{Cost}_d(P,y)`$. The reverse strict inequality required by the cone is impossible. $\blacksquare$

Indeterminacy therefore concerns input plans that trade off physical factors. For example, with two inputs and prices ranging independently from $1$ to $3$, let $x=(2,0)$ and $y=(0,2)$. At $P_1=(1,3)$, their costs are $2$ and $6$; at $P_2=(3,1)$, their costs are $6$ and $2$. Neither plan componentwise dominates the other, and the price box admits both rankings.

### Theorem 11.7 (Kirznerian Arbitrage Contracts the Indeterminacy Cone)
Suppose new information or arbitrage tightens the bounds, so that

$$
P_{\text{low}}(r)\le P'_{\text{low}}(r)
\quad\text{and}\quad
P'_{\text{high}}(r)\le P_{\text{high}}(r)
$$

for every input $r$. Every pair that remains indeterminate in the narrower box was already indeterminate in the original box. Thus tightening cannot add pairs to the cone.

**Proof.** If a pair is indeterminate in the narrower box, two admissible price vectors in that box give opposite cost rankings. The narrowed box is contained in the original box, so both witnesses are admissible there as well. The same strict cost inequalities therefore make the pair indeterminate in the original box. Hence the narrower cone is a subset of the original cone. $\square$

The inclusion can be strict. For $x=(3,0)$ and $y=(0,5)$, the outer box $[1,4]\times[1,4]$ admits opposite rankings: at $(1,4)$, the costs are $3<20$, and at $(4,1)$, they are $5<12$ in the other direction. In the narrower box $[2,3]\times[2,3]$, however, $x$ costs at most $9$ while $y$ costs at least $10$. Arbitrage can therefore turn this previously indeterminate comparison into a robust one. It need not eliminate uncertainty for every pair.

## Delivered Unit Prices and Price Envelopes

Fix a general action structure, an observer, a good, and a payment good. An observed unit-price record comes from a settled exchange in which the observer's represented principal is a party, one unit of the good is exchanged, and the payment quantity determines the recorded price. A record can be delivered to another agent only through actions on the same history.

### Definition 11.8 (Purposeful Delivery of an Observed Unit Price)

A delivered quote specifies:

1. a registered source record of a unit exchange observed by the sender;
2. a recipient distinct from the sender;
3. a sending moment after the source transaction and a decision moment after receipt, all on one history;
4. receipt at the immediate successor of the sending moment; and
5. enacted and purposeful sending and receiving actions.

The communication actions are non-trade actions with zero physical input and yield for every means. The delivered price is exactly the payment quantity in the source transaction. Thus the message transmits an observed price; it does not create another transaction or substitute an unobserved number.

### Definition 11.9 (A Recipient's Price Envelope)

Let $p_0$ be a seed price from an observed source record, and let $p_1,\ldots,p_n$ be the prices of records actually delivered to one recipient. Define

$$
L_n=\min\{p_0,p_1,\ldots,p_n\},
\qquad
U_n=\max\{p_0,p_1,\ldots,p_n\}.
$$

Only messages delivered to that recipient enter the envelope. Source records that were not sent and received do not alter it.

An interval formed from two observed unit-price records uses the same additive accounting. The lower and upper prices must come from records by the same observer, for the same good and payment good, on the same history before the decision. Its spread is a natural number $s$ certified by

$$
p_{\mathrm{low}}+s=p_{\mathrm{high}}.
$$

The certificate establishes the order of the endpoints without relying on truncated subtraction. An unavailable quote remains unavailable; it is not treated as a zero price.

### Proposition 11.10 (Envelope Widening)

When one further price $p$ is delivered, the new endpoints are

$$
L_{n+1}=\min(p,L_n),\qquad U_{n+1}=\max(p,U_n).
$$

Consequently $L_{n+1}\le L_n$ and $U_n\le U_{n+1}$. If $U_n < p$, then $U_n < U_{n+1}$.

**Proof.** The new lower endpoint is the minimum of the old lower endpoint and the added price; the new upper endpoint is their maximum. The two weak inequalities follow from the defining properties of minimum and maximum. If $U_n < p$, then $U_{n+1}=p$, so the upper endpoint rises strictly. $\square$

This proposition concerns the recorded range of delivered observations. It does not claim that the recipient's beliefs or actions must change after receiving the message. Such a behavioral conclusion would require an additional preference or decision rule.

These definitions and results apply to any action structure that supplies the source transaction, communication actions, temporal order, enactment, and purposeful choice. A finite example may witness that the conditions are jointly satisfied, but it is not part of the definition of price delivery.

## Coarsened Signals along Production Stages

When prices are reported at coarser resolution, the set of admissible prices widens. The theorem records how this loss of precision affects indeterminacy across production stages.

### Definition 11.11 (Ordinal Price Box and Coarsening)
An **ordinal price box** $B$ consists of lower and upper price vectors $B_{\text{low}}$ and $B_{\text{high}}$ satisfying $B_{\text{low}}(r)\le B_{\text{high}}(r)$. A box $B_2$ **coarsens** $B_1$ when it contains all the prices of $B_1$:

$$
\begin{aligned}
\forall r,\quad
B_{2,\text{low}}(r)&\le B_{1,\text{low}}(r),\\
B_{1,\text{high}}(r)&\le B_{2,\text{high}}(r).
\end{aligned}
$$

Coarsening is an inclusion relation on information intervals. It says that the bounds widen; it does not say why they widened.

### Theorem 11.12 (Coarsening Weakly Expands Indeterminacy)
If $B_2$ coarsens $B_1$, every pair indeterminate in $B_1$ remains indeterminate in $B_2$. The same two price witnesses still belong to the larger box, so the cost reversals remain available.

**Proof.** Coarsening makes the original box a subset of the new box. The two admissible price vectors witnessing opposite cost rankings in $B_1$ therefore remain admissible in $B_2$. Thus every indeterminate pair in $B_1$ is indeterminate in $B_2$. The count over a finite menu is a sum of indicator values for these pairs, so it cannot decrease; it increases strictly if at least one new pair enters the cone. $\square$

For a finite menu $\mathcal{X}$ of input plans, count the ordered pairs in $\mathcal{X}\times\mathcal{X}$ whose costs can reverse within the box. This count is weakly increasing under coarsening and increases strictly when coarsening makes at least one previously determinate pair indeterminate. It is a count of reversible cost comparisons, not the maximum size of an antichain in a partial order.

### Definition 11.13 (Multi-Stage Production Chain)
A **multi-stage price chain** of length $L$ is a sequence of ordinal price boxes $B_0,\ldots,B_{L-1}$ such that later, more upstream stages have coarser boxes:

$$
\forall k_1,k_2\in\text{Fin}(L),\quad
k_1\le k_2\implies B_{k_2}\text{ coarsens }B_{k_1}.
$$

Under this premise, every method pair indeterminate at a downstream stage remains indeterminate at a more upstream stage. This is the order-theoretic form of signal attenuation: wider price bounds preserve ambiguity and may add new ambiguous comparisons. The widening premise is part of the model, not a theorem that every real production chain must satisfy it.

### Definition 11.14 (Factor Price Box and Precautionary Demand)
For $d$ factors, a factor-price box consists of lower and upper prices $`\underline{P}_r \le \overline{P}_r`$ for each $r < d$. Given an intended input vector $x\in\mathbb{N}^d$, define the precautionary cash requirement by

$$
C^+(x)=\sum_{r < d}\overline{P}_r x_r.
$$

This is the amount sufficient to purchase $x$ at every factor-price vector in the box. It is a worst-case expenditure bound, not an expected expenditure.

### Proposition 11.15 (Widening Price Uncertainty Increases Precautionary Demand)
If every upper price weakly increases, then $C^+(x)$ weakly increases. If an upper price strictly increases for a factor used in positive quantity, the increase in $C^+(x)$ is strict.

**Proof.** Multiplication by each nonnegative $x_r$ preserves the weak upper-price inequality. Summing gives the weak result. At a coordinate with $x_r > 0$, a strict upper-price increase makes that summand strictly larger; the remaining summands do not decrease. $\blacksquare$

For a finite cohort $C$, fixed money balances $\omega(i,m_{\text{money}})$, plans $x(i)$, and price box $\mathcal{B}$, define the **cash-backed cohort** by

$$
\mathcal{C}(\mathcal{B})
=\{i\in C:C^+_{\mathcal{B}}(x(i))\le\omega(i,m_{\text{money}})\}.
$$

Membership means that the agent's balance covers the plan's upper-bound expenditure throughout the box.

### Proposition 11.16 (Narrower Price Bounds and Cash Solvency)
*Suppose the factor-price bounds under monetary coordination are no wider than under barter:*

$$
\forall r,\quad P_{\text{high}}^{\text{money}}(r) \le P_{\text{high}}^{\text{barter}}(r).
$$

For any cohort of agents with the same cash balances $\omega(i,m_{\text{money}})$ and intended factor-acquisition plans $x(i)$ in both comparisons:
1. *Precautionary cash demand is weakly lower under monetary coordination than under barter for every agent:*

$$
\forall i,\quad C^+_{\text{money}}(x(i)) \le C^+_{\text{barter}}(x(i)).
$$

2. *The set of agents able to cover worst-case factor expenditure weakly expands:*

$$
\mathcal{C}(\mathcal{B}_{\text{barter}})
\subseteq
\mathcal{C}(\mathcal{B}_{\text{money}}).
$$

**Proof.** For each nonnegative input quantity, the no-wider upper bound under monetary coordination makes its upper-bound cost weakly lower. Summing gives the first inequality. If an agent's cash covers the barter requirement, it also covers the weakly smaller monetary requirement, proving the cohort inclusion. A strict upper-price decrease on an input used in positive quantity strictly lowers that input's summand; all other summands weakly fall, so total demand falls strictly. $\square$

If the price bounds narrow strictly for an input used in positive quantity, the corresponding cash requirement falls strictly. The proposition is conditional on the bounds being narrower; it does not infer price convergence from monetary coordination alone.

A monetary disturbance can also change which agents can pay the prevailing price. In the modeled Cantillon network grounded in the Action Frame (`CantillonNetwork`), a downstream agent's physical cash balance $\omega(i, t_{\text{post}}, h, m_{\text{money}}) = \omega(i, t_{\text{pre}}, h, m_{\text{money}}) = M$ remains unchanged while the price moves from $P_0$ to $P_1$, with $0 < P_0 \le M < P_1$. By Proposition 9.24 (`cantillon_network_purchasing_power_dilution`), the division-free affordability conclusions are

$$
1\cdot P_0\le M,\qquad
\forall q>0,\ \neg(q\cdot P_1\le M),\qquad
M\cdot P_0 < M\cdot P_1.
$$

One unit is affordable before the price rise, while no positive integer quantity is affordable afterward; the balance-price cross-product also rises strictly. The price movement and exclusion conditions are grounded natively in the agent's physical cash balance $\omega$. The conclusion is the resulting loss of purchasing capacity for the uninjected holder. It makes the distribution of balances and the timing of price changes explicit in the social analysis of money.

A further monetary choice arises when a purchaser can settle the same payment with either of two media. The relevant opportunity cost is the medium surrendered. If compulsory par acceptance makes either tender sufficient for the purchase, while the actor prefers to retain one medium, the undominatedness condition of purposeful choice, defined in Chapter 3, determines which tender is excluded.

### Theorem 11.17 (Gresham Tender Exclusion)
*Suppose an agent can feasibly tender bad money for a purchase, and the resulting end is strictly preferred to the end obtained by tendering good money. Then tendering good money cannot be purposeful.*

**Proof.** If tendering good money were purposeful, no feasible alternative could yield a strictly preferred end. The feasible bad-money tender is such an alternative, contradicting undominatedness. $\blacksquare$

Under compulsory acceptance at par, the purchased good can be the same whichever medium is tendered. If retaining the good money is strictly preferred to retaining the bad money, an appropriate bundle-preference bridge gives the strict comparison required by the theorem. For a cohort in which every purposeful purchaser tenders one of the two media and can tender bad money, good-money tender is excluded throughout the cohort. The bad medium is then tendered by every member. The feasibility and preference conditions explain why the conclusion concerns a particular tender regime.

For a cohort $C$, let $\theta(i)$ denote the medium agent $i$ actually tenders in a spot exchange. The circulating tender of medium $m$ is the set

$$
\mathcal{T}_C(m)=\{i\in C:\theta(i)=m\}.
$$

### Theorem 11.18 (Gresham Circulation Collapse)
For each agent $i$ in a finite cohort $C$, let $\alpha(i,m)$ be the action of tendering medium $m$. Suppose $\theta(i)$ is either $m_{\text{good}}$ or $m_{\text{bad}}$, the enacted tender action $\alpha(i,\theta(i))$ is purposeful, and $\alpha(i,m_{\text{bad}})$ is feasible. Suppose the bad-medium action yields an end strictly preferred at the decision situation to the end yielded by the good-medium action. Then:
1. *Circulating tender of good money collapses completely:*

$$
\mathcal{T}_C(m_{\text{good}})=\emptyset.
$$

2. *Debased money completely captures the circulating volume:*

$$
\mathcal{T}_C(m_{\text{bad}})=C.
$$

**Proof.** If any agent tendered $m_{\text{good}}$, its purposeful action would face the feasible bad-medium tender with a strictly preferred end. That contradicts the undominatedness clause of purposeful choice. Therefore no member of $C$ tenders good money. Since every member tenders one of the two specified media, every member tenders bad money. $\square$

---

## Hayek: Price Signals and Quantization across Stages

A production chain transmits price information through discrete interfaces. The signal model measures the loss at each interface and derives a threshold at which the accumulated signal disappears or can be restored by integration.

### Definition 11.19 (Stage Width and Total Quantization Noise)
For a production chain of $L$ stages with a discrete price grid step $g$, let $w_k$ be the price-signal width at stage $k$. Assume every stage width is at least one grid step, $g\le w_k$. Define the total quantization noise by

$$
N_{\text{market}}(L,g)=L g.
$$

### Theorem 11.20 (Linear Lower Bound on Multi-Stage Noise)
Under the stage-width premise of Definition 11.19,

$$
L g\le\sum_{k=0}^{L-1}w_k.
$$

**Proof.** Definition 11.19 gives $g\le w_k$ for each of the $L$ stages. Summing these $L$ inequalities yields $Lg\le\sum_{k=0}^{L-1}w_k$. $\square$

If each stage's reported price interval has width at least $g$, the accumulated width is at least $L g$. The inequality applies to records generated by that per-stage reporting condition; in an economic application, the interval bounds and minimum width come from the relevant price or reporting records.

### Definition 11.21 (Coalesced Interfaces and Noise)
If a firm coalesces $K$ contiguous production stages within a chain of length $L$, the model counts the remaining external price interfaces as

$$
I_{\text{firm}}(L,K)=L-K+1,
$$

and assigns them noise

$$
N_{\text{firm}}(L,K,g)=(L-K+1)g.
$$

The count includes the chain's boundary interface. The distinct count $L-K$ below measures the remaining inter-stage market relationships relevant to the calculation boundary.

### Theorem 11.22 (Coalescence Reduces External Quantization Noise)
If $2\le K\le L$ and $g>0$, then

$$
N_{\text{firm}}(L,K,g) < N_{\text{market}}(L,g).
$$

**Proof.** Since $K\ge2$, we have $L-K+1 < L$. Multiplication by the positive grid step $g$ preserves the strict inequality, giving $(L-K+1)g < Lg$. These are the two noise quantities in Definition 11.21 and Definition 11.19. $\square$

Integration removes at least one intermediate price interface from this noise count. The conclusion concerns quantization noise only; it says nothing yet about the cost of internal administration.

The next model makes the role of an intermediate interface explicit. A signal is attenuated both by a discrete discount divisor and by a deadband representing price spread and quantization.

### Definition 11.23 (Discrete Price-Signal Transmission)
For downstream price difference $\Delta P$, discount divisor $R$, and nonnegative deadband $d$, define one-stage transmission by

$$
S(\Delta P,R,d)=\Delta P \div R-d.
$$

Here division and subtraction are in $\mathbb{N}$; subtraction is truncated at zero. Thus the transmitted signal is zero whenever the discounted difference does not exceed the deadband. In the model, $R$ represents the discrete divisor associated with intertemporal discounting (the natural-rate version corresponds to $1+\iota$ ).

Across two separate market interfaces, with intermediate deadband $d_{\text{int}}$ and upstream deadband $d_{\text{u}}$, set

$$
S_{\text{split}}
=S\bigl(S(\Delta P_{\text{out}},R_1,d_{\text{int}}),R_2,d_{\text{u}}\bigr).
$$

When the intermediate stage is internalized, the model removes that intermediate deadband and compounds the discount divisors:

$$
S_{\text{merge}}
=S(\Delta P_{\text{out}},R_1R_2,d_{\text{u}}).
$$

### Theorem 11.24 (Critical Attenuation and Signal Restoration)
Assume $R_1,R_2\ge1$ and the downstream price difference lies in the interval

$$
(d_{\text{u}}+1)(R_1R_2)
\le \Delta P_{\text{out}}
\le R_1d_{\text{int}}+R_1R_2d_{\text{u}}.
$$

Then the split-market signal is extinguished while the merged signal remains positive:

$$
S_{\text{split}}=0
\qquad\text{and}\qquad
S_{\text{merge}}>0.
$$

**Proof.** The lower bound gives $\Delta P_{\text{out}}/(R_1R_2)\ge d_{\text{u}}+1$, so subtracting $d_{\text{u}}$ leaves a positive merged signal. For the split path, the upper bound gives
$\Delta P_{\text{out}}/R_1\le d_{\text{int}}+R_2d_{\text{u}}$.
After subtracting $d_{\text{int}}$ and truncating at zero, the intermediate signal is at most $R_2d_{\text{u}}$. Dividing by $R_2\ge1$ gives at most $d_{\text{u}}$; subtracting the upstream deadband therefore yields zero. $\square$

The reporting rule divides a price difference by the stage's discrete attenuation factor and subtracts the stage's deadband, truncating at zero. A split path applies that rule at each external interface; the merged path bypasses the intermediate report and applies the compounded divisor at the remaining interface. Under the displayed lower and upper bounds, the merged report is positive while the sequential split reports reach zero. This result applies when the modeled observations are generated by those reporting operations and the compared production tasks use the corresponding signals.

## Coase and Mises: The Boundary of the Firm

Integration removes some external price comparisons but introduces internal calculation uncertainty. The boundary results compare those two quantities and derive a parameter window in which partial integration is viable.

### Definition 11.25 (External and Internal Calculation Uncertainty)
Let $W_{\text{int}}$ be the intermediate spot-market price spread, $g$ the grid step, and $\Delta z$ the absolute physical volume being evaluated. Define external spot-market uncertainty as

$$
U_{\text{spot}}=(W_{\text{int}}+g)\Delta z.
$$

Let $b_{\text{up}}$ denote upstream price blur, $b_{\text{joint}}$ joint-cost allocation blur, and $b_{\text{opp}}$ the lost external-opportunity comparison. Define internal firm uncertainty as

$$
U_{\text{firm}}=(b_{\text{up}}+b_{\text{joint}}+b_{\text{opp}})\Delta z.
$$

### Theorem 11.26 (Master Coalescence Inequality)
For $\Delta z>0$, internal coordination has strictly less modeled calculation uncertainty than the spot market exactly when

$$
U_{\text{firm}} < U_{\text{spot}}
\quad\iff\quad
b_{\text{up}}+b_{\text{joint}}+b_{\text{opp}}
<W_{\text{int}}+g.
$$

**Proof.** Substitute the definitions of $U_{\text{firm}}$ and $U_{\text{spot}}$. Both sides have the common positive factor $\Delta z$, which can be canceled without changing the strict inequality. The remaining comparison is exactly the displayed sum-of-blurs inequality. $\square$

Because the physical volume factor is positive, the uncertainty-index comparison holds exactly when the internal blur sum is below the external spread plus grid step. Greater internal blur reverses the comparison, and equality gives no strict advantage. The indices compare the specified costs of market quoting and internal reporting in the same discrete units.

The other side of the boundary comes from Chapter 9's economic-calculation result. Market prices order monetary costs in $\mathbb{N}$, even when physical input plans are incomparable. An additive sum of numerical labels for ends can reverse under a ranking-preserving change of those labels. For example, keep the same strict ordering of four ends and compare the two bundles $`A=\{e_0,e_3\}`$ and $`B=\{e_1,e_2\}`$. The ranking-preserving assignments $(10,4,3,1)$ and $(10,9,8,1)$ give:

$$
\begin{aligned}
10+1&>4+3,\\
10+1&<9+8.
\end{aligned}
$$

Thus the additive comparison can reverse under order-preserving reassignments. This witness shows that the proposed summation rule does not preserve the stated ordering of ends.

### Theorem 11.27 (A Viable Coalescence Window)
Let $K_{\min}$ be a lower bound on the integration depth under consideration. If

$$
2\le K_{\min}\le K < L,
$$

the grid step satisfies $g>0$, and the merged signal is positive, then integration at depth $K$ can both reduce the modeled quantization noise and preserve at least one inter-stage market relationship:

$$
N_{\text{firm}}(L,K,g) < N_{\text{market}}(L,g),
\qquad 0 < S_{\text{merge}},
\qquad 1\le L-K.
$$

**Proof.** The depth bounds imply $K\ge2$ and $K < L$. Since $g>0$, Theorem 11.22 gives the strict reduction in noise. Positivity of the merged signal is assumed. Since $K < L$ are natural numbers, $1\le L-K$, so at least one inter-stage market relationship remains. $\square$

Under the critical attenuation inequalities from Theorem 11.24, the same window combines split-signal extinction, merged-signal restoration, noise reduction, and a remaining external market relationship. At $K=L$, the model instead has $L-K=0$: all inter-stage market relationships have been absorbed. If the compared production plans are physically incomparable and no external market prices remain to compare them, Chapter 9's incommensurability result applies. The formulas therefore identify a region where integration can address an intermediate signal problem without eliminating every external comparison.

These inequalities identify admissible integration scales for the specified chain and reporting mechanism. Selecting one scale from that range requires comparing available production methods, administrative resource use, external exchange terms, and the entrepreneur's valued outcomes.

### Proposition 11.28 (Information, Rather Than Stage Count, Determines the Policy Result)
Consider the finite policy model with four states, each combining a demand condition and a factor condition. When the observation reports both conditions, or when the missing factor condition is restored, there is a policy that selects the required production decision in every state. When either condition is hidden so that two states with different required decisions produce the same observation, no policy based on that observation can be correct in every state:

$$
\exists\pi_{\mathrm{full}},\pi_{\mathrm{restored}}\ \forall s,\quad
\pi_{\mathrm{full}}(s)=D(s)\ \wedge\ \pi_{\mathrm{restored}}(s)=D(s)
$$

and, for each observation map that hides one condition,

$$
\neg\exists\pi\ \forall s,\quad \pi(O_{\mathrm{hidden}}(s))=D(s).
$$

**Proof.** When both relevant conditions are observed, choose the stipulated state-specific required decision. If one condition is hidden, take two states that agree on the observed coordinate and differ on the hidden coordinate. By construction they require opposite decisions, but any policy receives the same observation in both states and must return the same decision. It therefore fails in at least one of them. The conclusion is about this finite information model; stage count alone does not determine whether the necessary information is available.

## Purposeful Choice of Organizational Form

The cost and signal results constrain what organizational forms are feasible in the model. The final choice theorem additionally assumes a feasible menu, preference ordering, and enacted action; these premises connect the calculation model to the purposeful-choice condition.

### Definition 11.29 (End-Based Appraisal of Organizational Outcomes)
An **end-based appraisal** specifies the actor's valued ends, their physical requirements, and the projected stock bundles associated with split-market production, partial integration, full socialization, and inaction. Write $`\mathcal{E}_{i,t,h}`$ for the ends valued by agent $i$ at the appraisal context, $\rho(e,m)$ for the means required by end $e$, and

$$
\text{Attains}(b,S)\iff
\forall m,\quad\sum_{e\in S}\rho(e,m)\le b(m)
$$

for each finite set $S$ of valued ends. We say $b_1\succ_{\mathrm{end},i,t,h}b_2$ when

$$
\begin{aligned}
b_1\succ_{\mathrm{end},i,t,h}b_2\iff\;&
\Bigl(\forall S\subseteq_{\mathrm{fin}}\mathcal{E}_{i,t,h},\
\text{Attains}(b_2,S)\to\text{Attains}(b_1,S)\Bigr)\\
&\wedge\Bigl(\exists S\subseteq_{\mathrm{fin}}\mathcal{E}_{i,t,h},\
\text{Attains}(b_1,S)\wedge\neg\text{Attains}(b_2,S)\Bigr).
\end{aligned}
$$

At each minimally plausible history, the partially integrated bundle satisfies this relation over each comparison bundle:

$$
\begin{aligned}
b_{\text{merge}}(h')&\succ_{\mathrm{end},i,t,h}b_{\text{split}}(h'),\\
b_{\text{merge}}(h')&\succ_{\mathrm{end},i,t,h}b_{\text{soc}}(h'),\\
b_{\text{merge}}(h')&\succ_{\mathrm{end},i,t,h}b_{\text{retain}}(h')
\qquad(h'\in\min_{\pi}(i,t)).
\end{aligned}
$$

The relation compares attainability of valued ends, not raw physical quantities. In the `ActionFrame`, action outcomes are grounded in their projected commodity bundles, and teleological bundle dominance natively induces strict preference between the realized ends (`teleological_bundle_dominance_induces_preference`). Partial integration is therefore strictly preferred to the other three action outcomes on each plausible history. A model with one valued end can establish the needed bundle relation from a recorded receipt once the end's requirement and the receipt comparison have been specified.

### Definition 11.30 (Entrepreneurial Firm-Boundary Decision)
At a node $\langle t,h\rangle$, an **entrepreneurial firm-boundary decision** specifies:

1. a split-market action $\alpha_{\text{split}}$;
2. a partial-integration action $\alpha_{\text{merge}}$;
3. a full-socialization action $\alpha_{\text{socialize}}$; and
4. the ends of these actions and of the passive baseline $\alpha_0$.

The decision also specifies the parameter inequalities for the viable coalescence window, feasibility of the three organizational actions, enactment of partial integration, preference over passive retention, and the preference comparisons generated by the signal and noise differences. Every other feasible action must have one of the listed four ends. These premises account for every feasible rival in the purposeful-choice condition.

### Theorem 11.31 (Purposeful Coalescence within the Viable Window)
Under Definition 11.30 and the critical attenuation conditions, the partially integrated action is purposeful, while the split-market and full-socialization actions are not purposeful:

$$
\neg\mathsf{P}(\alpha_{\text{split}})
\quad\wedge\quad
\mathsf{P}(\alpha_{\text{merge}})
\quad\wedge\quad
\neg\mathsf{P}(\alpha_{\text{socialize}}).
$$

**Proof.** By Definition 11.30, the merged action is feasible and enacted, and its end is strictly preferred to the passive end. The complete-menu premise and the stated preference comparisons rule out every feasible rival as strictly preferred to the merged end. Thus the merged action is purposeful. The merged end strictly dominates the split and socialization ends in preference, so each of those alternatives fails the undominatedness clause. The critical attenuation result supplies signal extinction under separation and a positive signal after integration; Theorem 11.27 supplies lower noise and a remaining market relation. $\square$

### Information-Grounded Derivation of the Preference Premises

The finite policy result is stated over information channels, not firm types. Each state combines a demand condition with a factor condition. A demand-hidden channel maps states with opposite demand to the same observation; a factor-hidden channel does the same for opposite factor conditions. A policy must choose the same task for states that have the same observation, so each channel faces a concrete state-conflict. Observing both coordinates, or restoring the missing coordinate, removes that conflict. An economic interpretation applies when actual reports, orders, and records induce these same observation equivalences and the required tasks correspond to real production choices.

When two arrangements have the same receipt and unsold-output profile, the scenario also establishes equality of their recorded physical inventories on those branches. If administration consumes additional resources or market coordination takes time, those costs must appear in the inventory record and can change the comparison. A valued monetary end, together with the traced stock comparison and the model's appraisal rule, supplies the entrepreneur's preferences. Feasibility, enactment, improvement over inaction, and undominatedness then establish purposeful choice. The numerical attenuation window is an additional signal condition; the choice conclusion depends on the listed causal and behavioral premises.

### Organizational Semantics from Accepted Direction and Exchange

To discuss organization, specify what the relevant actions do: who assigns a task, who accepts it, what work is authorized, and which transfers occur. These descriptions interpret actions within the general account of choice and exchange.

An accepted delegation records four purposeful actions on one history across three strictly ordered moments. At the decision moment, the principal proposes an assignment and the operator accepts a scope of permitted tasks. At a later instruction moment, the principal purposefully selects a specific task within that scope. At a still later work moment, the operator purposefully executes that task. The instruction is what connects an open-ended scope of authority to the particular work performed.

The internal transfer also has explicit physical preconditions. The operator's task must be non-trade production that uses positive quantities of raw material and operator capacity; these inputs are distinct from one another and from the delivered good, and the task uses no units of the delivered good. The task has enough output of the delivered good to cover the positive transfer, and the operator has no opening stock of that good. The two inputs must be available when the task is performed, while the positive compensation and delivered quantities must match the authorized exchange terms. These conditions establish that the internal delivery comes from the specified production rather than an unexplained initial stock.

An internal transfer authorized in advance differs from an exchange across independent governance. Both may use matched offers and acceptances and obey the same physical transfer laws. A fixed-price or continuing external contract remains a market interface when its parties act under independent authority. Fresh bargaining is a narrower case: it additionally requires that the terms be set through new bargaining rather than inherited from an earlier agreement.

An organizational network records delegated direction and market exchange along stage edges. All required relations must occur on the same history, and the external exchange must follow the delegated task. In a three-stage example, a principal directs production by an operator and an outside exchange occurs with a party under distinct governance. The evidence includes valid representation, independent governance, common history, and temporal order. Fixed-price and continuing contracts can therefore be external market interfaces; whether bargaining is fresh is a separate question about how their terms were set.

The finite policy obstruction can be stated using indistinguishable states: states with the same organizational observation must receive the same policy choice. When those states require different tasks, no policy using only that observation can meet both requirements. A bilateral trade example supplies an external market edge, but without an accepted internal delegation it does not constitute an example of a complete firm network.

One finite trace combines the information-grounded organizational choice with purposeful assignment and scope acceptance at the root, a later instruction, operator production at work, compensated internal transfer, and an outside bilateral sale. Its moments run root $\prec$ instruction $\prec$ work $\prec$ transfer $\prec$ sale. There is no separate finishing-production stage between transfer and sale. The operator begins without the intermediate good; the work action produces it, and the internal exchange delivers it to the principal before the sale. The trace depends on its stated input stocks, output quantities, sale proceeds, valued ends, and complete feasible menu.

### Proposition 11.32 (Ordinal Firm-Boundary Comparison)
There is also a purely ordinal formulation. Suppose passive retention, a firm action, market transacting, and universal integration comprise the feasible menu, and all three active organizational actions are feasible. If the firm action is distinct from market transacting, its end is strictly preferred to each of the other three ends, and the firm action is executed, then:

1. the firm action is purposeful;
2. the firm action demonstrates preference over market transacting; and
3. market transacting, universal integration, and passive retention are each excluded as purposeful choices on that menu.

**Proof.** The firm action is feasible and enacted, improves on passive retention, and no other menu action has a strictly preferred end. It is therefore purposeful. By definition, its purposeful enactment against the feasible market action demonstrates the stated action comparison. Each rival active action is strictly dominated by the firm action, while passive retention is not enacted and also has a lower-ranked end. Hence none is purposeful. $\square$

The conclusion follows from the stated preference comparisons and restricted menu. Those premises are not derived from the input-cost bounds, so the result isolates the choice consequence rather than deriving the rankings themselves.

## Price Controls and Conditional Shortage Cascades

A ceiling can remove the seller’s modeled gain from an exchange. When the affected input is required by later stages, withheld supply can propagate to downstream infeasibility. The cascade is conditional on the specified sectors, requirements, and action responses.

### Proposition 11.33 (A Ceiling That Removes the Seller's Gain Blocks Active Sale)
Let $\alpha_{\text{sale}}$ be a non-inertial sale action. If its controlled-price end $e_{\text{controlled}}$ is not strictly preferred to the retention end $e_{\text{retain}}$, then the sale cannot be active purposeful action:

$$
\alpha_{\text{sale}}\ne\alpha_0\quad\wedge\quad
\neg(e_{\text{controlled}}\succ_{i,t,h}e_{\text{retain}})
\quad\Longrightarrow\quad
\neg\mathsf{P}_{\mathrm{act}}(i,t,h,\alpha_{\text{sale}}).
$$

**Proof.** For a nonpassive action, active purposefulness requires its controlled-price end to be strictly preferred to the retention end. The premise denies that comparison, so the action fails the active improvement clause. $\square$

For a distinct sale action, the same premise also excludes purposeful sale, because purposeful intervention must improve on inaction. The argument does not say that every regulated price is below a seller's reservation price; that comparison is an explicit premise.

### Definition 11.34 (Regulatory Stages and Shortage Severity)
The staged model distinguishes an unhampered stage, a first control of a consumer sector, and a second control extending to an input sector. Their modeled shortage severities are respectively $0$, $1$, and $2$. The planner's strict preference in this model ranks a stage with fewer shortages above one with more shortages.

This ordering applies to the three modeled stages under the stated planner preference.

### Theorem 11.35 (Shortages in the Coupled Three-Sector Model)
Suppose sellers purposefully supply in the unhampered stage, the first ceiling removes the consumer-sector seller's gain relative to retention, and the second-stage assumptions remove the gain in both the consumer and input sectors. Define a sector shortage as the absence of active purposeful supply. Then:

1. there is no modeled shortage in the unhampered stage;
2. the consumer sector has a shortage under the first control; and
3. both the consumer and input sectors have shortages under the second control.

**Proof.** In the unhampered stage, the premise supplies purposeful active supply, so there is no shortage by definition. Under the first control, the consumer seller's controlled-price outcome fails the improvement condition by Proposition 11.33, so active purposeful supply is absent there. Under the second control, the same argument applies to both the consumer and input sellers. The stated stage assumptions therefore give the three shortage conclusions. The severity ranking records their order as zero, one, and two shortages. $\square$

Theorem 11.35 composes the seller-choice condition from Proposition 11.33 with the modeled controls and the severity ranking in Definition 11.34. To use a price ceiling as an explanation of withheld supply, an application supplies evidence that the controlled-price outcome fails the seller's stated improvement comparison against retention.

To show how withdrawal can make downstream production physically impossible, connect it to an input endowment and the transition law.

### Theorem 11.36 (From Withheld Supply to Downstream Infeasibility)
Suppose a seller begins with zero units of an input, executes inaction, and inaction neither consumes nor yields that input. If a downstream production action requires one unit, then at the next moment the seller still has zero units and that production action is infeasible.

**Proof.** The causal transition law gives

$$
\omega(i,t',h,m)+u(\alpha_0,m)
=\omega(i,t,h,m)+y(\alpha_0,m).
$$

Substituting the zero initial stock, zero use, and zero yield gives $\omega(i,t',h,m)=0$. The downstream action requires $1$, so its requirement exceeds the endowment. By the feasibility definition from Chapter 1, it is infeasible. $\blacksquare$

Theorem 11.36 is a one-step stock-transition module: zero initial stock, no use or yield under inaction, and a downstream action requiring one unit imply infeasibility at the next moment. Its conclusion iterates along a finite supply chain when each upstream producer retains the input, each downstream stage begins without the required factor, and the corresponding transition and production premises are supplied at every stage.

## Credit Expansion and the Firm Boundary

The firm-boundary comparison above weighs uncertainty in market coordination against uncertainty inside the firm. We can now place that comparison beside an intertemporal return threshold. This next step matters because a low credit-rate threshold can make a project appear acceptable even when the same increment does not pass the natural-rate threshold; the formal result then combines that divergence with the separate uncertainty comparison.

### Proposition 11.37 (Credit and Natural Rates Can Classify the Same Return Differently)

Let $\Delta P$ be an increment to expected return, $R_c$ a positive credit rate, $R_n$ a positive natural rate, and $d$ a deadband. If

$$
R_c d < \Delta P \le R_n d,
$$

then the increment is above the credit-rate threshold and at or below the natural-rate threshold.

**Proof.** The two conclusions are the two inequalities in the hypothesis, read as the corresponding return-threshold conditions. $\square$

The deadband fixes the integer scale for Proposition 11.37's return-threshold comparison. The proposition takes the rates and return increment as inputs; connecting them to a monetary-policy rule or to an enacted investment requires the corresponding rate-generation and choice premises.

### Proposition 11.38 (A Credit-Rate Boom Can Coexist with a Different Firm-Cost Ranking)

Let $z$ be production volume, $W$ the natural spread, $g$ the price-grid step, $b_u,b_j,b_e$ the upstream, joint-cost, and external-opportunity blurs, and let $R_c,R_n>0$ be the credit and natural rates. Define

$$
U_s=(W+g)z,
\qquad
U_f=(b_u+b_j+b_e)z.
$$

Suppose $z>0$, $W+g < b_u+b_j+b_e$, and a boom increment satisfies

$$
R_c(V+d_c)<\Delta P_b\le R_n(V+d_c),
$$

where $V$ is a safe-return benchmark and $d_c$ is a compensation term. Then the boom increment passes the credit-rate comparison but not the natural-rate comparison, and $U_s < U_f$.

**Proof.** The first two conclusions follow directly from the displayed return bounds. Since $z>0$, multiplying $W+g < b_u+b_j+b_e$ by $z$ gives $U_s < U_f$. $\square$

Proposition 11.38 composes two conditional comparisons: the boom increment passes the credit-rate threshold but not the natural-rate threshold, while the specified cost formulas rank spot uncertainty below firm uncertainty. To infer that credit expansion causes conglomeration, an application connects the rate threshold to a policy-to-rate mapping and then to organizational choice. To conclude that the entrepreneur selects a firm boundary, it composes the cost comparison with the preference, menu, and execution premises developed earlier in this chapter.

### Proposition 11.39 (Network Adoption Can Improve Price-Box Cash Coverage)

Suppose the money-adoption process of Chapter 9 starts with at least one adopter, the trading network is connected through the stated demand relations, and each acceptance profile is assigned a factor-price box. Assume that a larger acceptance profile is assigned a no-wider box. If the adoption process reaches a profile in which the designated medium is universally accepted, then at that profile the upper-bound cash demand for each fixed input plan is no greater than at the initial profile. Consequently, every agent whose cash covered its plan under the initial box still covers that plan under the final box.

**Proof.** The network-adoption result supplies a finite iterate at which the designated medium is universally accepted. The assumed monotonicity of the price-box schedule makes the final box no wider than the initial one. For each nonnegative input quantity, its upper-bound price contribution therefore weakly falls; summing gives weakly lower precautionary demand. Any initial cash balance covering the earlier demand also covers the lower final demand. $\square$

Proposition 11.39 composes network adoption with a price-box schedule that assigns no-wider bounds to larger acceptance profiles. Given that schedule, universal acceptance supplies weakly lower upper-bound cash demand and preserves initial coverage. The schedule is an explicit input to this connection between monetary adoption and cash coverage.

## Conclusion

We have used bounded price information to compare production plans, followed signals through stages of production, connected monetary adoption to cash coverage under an explicit price-box schedule, and stated conditions under which integration, credit-rate comparisons, or intervention alter modeled conclusions. We also separated organizational meanings from the physical transfers that can occur both inside and outside a firm. These examples concern defined institutions and conditional premises. We now turn to the political authority and fiscal relations that can alter the same patterns of production and exchange.
