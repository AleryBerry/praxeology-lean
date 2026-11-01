# Praxeological Critique of Central Bank Money Supply Measures ($M_1, M_2, M_3, M_4$) and the True Money Supply (TMS)

## Executive Summary

Monetary debates center on how to measure the "supply of money." Central banks publish liquidity-tiered aggregates ($M_1, M_2, M_3, M_4$), while Austrian economists propose the Rothbard-Salerno True Money Supply (TMS) to isolate the general medium of exchange. However, from our formalization in Chapter 9 (Definition 9.14a–c, Proposition 9.14d, Theorem 9.14e), Chapter 10 (Propositions 10.10a–10.12a, Definitions 10.19–10.22, Propositions 10.19a, 10.21a, Theorems 10.23–10.24), and Chapter 11 (Theorems 11.17–11.18), any scalar aggregation of money commits fundamental category errors.

This critique evaluates existing metrics against the physical conservation laws, spot-purchase feasibility, and ledger structures of praxeology:
1. **Federal Reserve Measures** ($M_1 \to M_4$) **Violate Physical Conservation:** $M_2, M_3$, and $M_4$ double-count pure credit contracts (time deposits, repurchase agreements, commercial paper), counting both the borrower's spendable cash and the lender's deferred claim, fabricating phantom purchasing power refuted by the contraction of the lender's action menu (Proposition 10.10b). They also treat non-medium equity shares (money market mutual funds) as spendable cash (violating Proposition 10.10a) while arbitrarily excluding sovereign operating balances at the central bank.
2. **Rothbard-Salerno TMS Corrects Credit Double-Counting but Fails as a Scalar:** While TMS correctly excludes pure credit transfers and includes Treasury cash balances, it aggregates heterogeneous commodities into a single scalar sum (violating cross-medium feasibility, Proposition 10.10a), assumes 1:1 par redeemability of unbacked fractional-reserve bank deposits (refuted by Proposition 10.12a and Proposition 10.21), and assumes par co-circulation violating Gresham's Law (Theorems 11.17–11.18).
3. **Praxeological Vector Accounting Provides Exact Measurement:** The primary praxeological state is the $|\mathcal{I}| \times |\mathcal{M}|$ Endowment Matrix $\boldsymbol{\Omega}(t, h)$ with bank-specific fiduciary media $m_{\mathrm{fid}, b}$. Its coarse-grained Sectoral Projection Vector $\mathbf{M}(t, h) = \langle M_{\mathrm{cash}}^{\mathrm{pub}}, M_{\mathrm{fid}}, R_{\mathrm{issuer}}, M_{\mathrm{treas}}, C_{\mathrm{pure}} \rangle$ (Definition 10.19) partitions total base money exactly into non-bank public currency, bank reserves, and Treasury cash without double-counting, isolating the unbacked fiduciary overhang $\Delta_{\mathrm{overhang}}$ and autonomous reserve coverage ratio $\rho$ (Definitions 10.19–10.20, Propositions 10.19a, 10.21, 10.21a).

---

## The Three Competing Measurement Paradigms

### 1. The Federal Reserve Aggregate Hierarchy ($M_1, M_2, M_3, M_4$, MZM)

Central banks group financial assets along administrative liquidity tiers:
- **$M_1$**: Physical currency in circulation plus demand and other liquid checkable deposits.
- **$M_2$**: $M_1$ plus small time deposits (certificates of deposit under 100,000 USD) and retail money market mutual funds (MMMFs).
- **$M_3 / M_4$**: $M_2$ plus large institutional time deposits, institutional MMMFs, repurchase agreements (repos), commercial paper, and short-term Treasury bills.

**Praxeological Defects:**
- *Credit Double-Counting (Proposition 10.10b):* When a saver funds a time deposit or repo, spendable cash is transferred to the borrower, strictly conserving total media ( $\sum \omega(t') = \sum \omega(t)$ ) while stripping tight money-using actions from the lender's feasible menu. Adding time deposits and debt securities to $M_1$ counts both the borrower's spendable cash and the lender's deferred claim, fabricating phantom purchasing power out of thin air.
- *Conflating Equity with Media (Proposition 10.10a):* Money market mutual fund shares are equity claims on investment trusts, not media of exchange. Spot purchases require the delivery of a concrete medium; mutual fund shares cannot execute spot transactions without a prior secondary liquidation into central bank reserves or commercial bank deposits.
- *Arbitrary Sovereign Exclusion:* Excludes the Treasury General Account ($M_{\mathrm{treas}}$), ignoring base reserves actively bidding on goods and services.

### 2. The Rothbard-Salerno True Money Supply (TMS)

Formulated by Murray Rothbard and Joseph Salerno to isolate the general medium of exchange:
- **TMS**: Currency in circulation outside banks, demand deposits, other checkable deposits, savings deposits (MMDAs), and U.S. government demand deposits at the central bank.
- *Excluded:* Time deposits, repurchase agreements, commercial paper, and money market mutual fund shares.

**Theoretical Soundness and Internal Contradictions:**
- *What TMS Gets Right:* Adheres to Proposition 10.10b by purging pure credit contracts (time deposits) and includes sovereign cash ($M_{\mathrm{treas}}$), respecting physical conservation.
- *The Cross-Medium Summation Impossibility (Proposition 10.10a):* TMS sums heterogeneous media ($m_{\mathrm{cash}} + m_{\mathrm{dep}} + m_{\mathrm{sav}} + m_{\mathrm{treas}}$) into a single scalar number. By Proposition 10.10a, spot-purchase feasibility requires sufficient holdings of the *specific* tender medium required; cross-medium summation attributes false purchasing capacity to actors that cannot be realized in any purposeful action.
- *The Fiduciary Par Fallacy (Proposition 10.12a, 10.21):* TMS treats fractional-reserve bank deposits as 1:1 par-convertible "warehouse receipts." In reality, fiduciary origination expands circulating liabilities while leaving bank physical reserves unchanged ( $R_{\mathrm{issuer}}(t') = R_{\mathrm{issuer}}(t)$ ). Simultaneous par redemption is physically infeasible when $M_{\mathrm{fid}} > R_{\mathrm{issuer}}$ (Proposition 10.21).
- *Gresham Par Collapse (Theorems 11.17–11.18):* Pegging distinct media at 1:1 nominal parity induces purposeful actors to hoard sound base cash and tender vulnerable bank deposits, extinguishing base circulation ( $\mathcal{C}(m_{\mathrm{good}}) = \emptyset$ ).

### 3. Praxeological Disaggregated Vector Accounting

From our formalization in Chapter 10 (Definitions 10.19–10.22, Propositions 10.19a, 10.21, 10.21a, 10.24, Theorem 10.23):
- **Primary Endowment Matrix & Sectoral Projection (Definition 10.19, Proposition 10.19a):** The fundamental praxeological state is the agent-by-medium Endowment Matrix $\boldsymbol{\Omega}(t, h) = [\omega_a(t, h, m)]$, where deposits at distinct banks are distinct media ($m_{\mathrm{fid}, b_1} \neq m_{\mathrm{fid}, b_2}$). To audit aggregate conservation without committing the cross-agent fallacy for individual spot trades (Proposition 10.19a), praxeology projects $\boldsymbol{\Omega}(t, h)$ over the disjoint partition $`\mathcal{I} = \mathcal{I}_{\mathrm{pub}} \sqcup \mathcal{I}_{\mathrm{banks}} \sqcup \{\mathrm{treas}\}`$ into the **Sectoral Monetary Projection Vector**:

$$
\mathbf{M}(t, h) = \big\langle M_{\mathrm{cash}}^{\mathrm{pub}}(t, h), \; M_{\mathrm{fid}}(t, h), \; R_{\mathrm{issuer}}(t, h), \; M_{\mathrm{treas}}(t, h), \; C_{\mathrm{pure}}(t, h) \big\rangle,
$$

satisfying the exact three-sector base money identity: $M_{\mathrm{base}}^{\mathrm{total}} = M_{\mathrm{cash}}^{\mathrm{pub}} + R_{\mathrm{issuer}} + M_{\mathrm{treas}}$.
- **Autonomous Overhang & Two-Tier Fiat LOLR Dichotomy (Definitions 10.20, Propositions 10.21, 10.21a):**

$$
\Delta_{\mathrm{overhang}}(t, h) = M_{\mathrm{fid}}(t, h) - R_{\mathrm{issuer}}(t, h), \qquad \rho(t, h) = \frac{R_{\mathrm{issuer}}(t, h)}{M_{\mathrm{fid}}(t, h)}.
$$

In a modern two-tier fiat system, $\rho(t, h)$ defines commercial banks' autonomous liquidity boundary prior to central bank intervention. If runs exceed $R_{\mathrm{issuer}}$, commercial banks face an operational dichotomy (Proposition 10.21a): autonomous default/suspension versus an inflationary lender-of-last-resort (LOLR) bailout ($\Delta M > 0$) that saves banks only by diluting purchasing power across the Cantillon network (Proposition 9.24).
- **Sectoral Solvency Stress Testing (Definition 10.22, Theorem 10.23):** Couples the monetary coordinates to factor price uncertainty $\mathcal{B} = \langle P^{\inf}, P^{\sup} \rangle$, evaluating the cash-backed solvent cohort $\mathcal{S}(\omega, m, \mathcal{B}, x, \text{Cohort})$ under Cantillon price inflation.

---

## Master Comparison Table of Monetary Measures

The table below contrasts the theoretical foundations, catallactic rules, and calculated metrics across the five measurement frameworks:

| Measurement Dimension | Federal Reserve M1 | Federal Reserve M2 | Federal Reserve M3 / Broad | Rothbard-Salerno TMS | Praxeological Vector Accounting |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Mathematical Formulation** | $m_{\mathrm{cash}} + m_{\mathrm{dep}}$ | $M_1 + C_{\mathrm{time}} + E_{\mathrm{mmmf}}$ | $M_2 + C_{\mathrm{inst}}$ | $m_{\mathrm{cash}} + m_{\mathrm{dep}} + m_{\mathrm{treas}}$ | Vector: $\langle M_{\mathrm{cash}}^{\mathrm{pub}}, M_{\mathrm{fid}}, R_{\mathrm{issuer}}, M_{\mathrm{treas}}, C_{\mathrm{pure}} \rangle$ |
| **Theoretical Category** | Scalar Aggregate | Scalar Aggregate | Scalar Aggregate | Scalar Aggregate | Matrix $\boldsymbol{\Omega}$ with Sectoral Projection Vector $\mathbf{M}$ |
| **Pure Credit Conservation** | Neutral (Excludes credit) | **Violated** (Prop 10.10b): Counts credit twice | **Critically Violated**: Compounds debt double-counting | **Satisfied** (Prop 10.10b): Excludes pure credit | **Strictly Preserved** (Prop 10.10b): Credit isolated as $C_{\mathrm{pure}}$ |
| **Spot-Trade Feasibility** | **Violated** (Prop 10.10a): Cross-medium sum | **Violated** (Prop 10.10a): Adds non-medium equity | **Violated** (Prop 10.10a): Adds illiquid debt | **Violated** (Prop 10.10a): Cross-medium sum | **Strictly Preserved** (Prop 10.10a, 10.19a): Governed by $\boldsymbol{\Omega}$ |
| **Cross-Bank Non-Fungibility** | Ignored (Summed) | Ignored (Summed) | Ignored (Summed) | Ignored (Summed) | **Preserved** (Prop 10.19a): $m_{\mathrm{fid}, b}$ distinct per bank |
| **Fractional-Reserve Par Fallacy** | **Present**: Equates unbacked deposits to base cash | **Present**: Equates unbacked deposits to base cash | **Present**: Equates unbacked deposits to base cash | **Present**: Assumes 100% par convertibility | **Refuted as Infeasible** (Prop 10.12a, 10.21) |
| **Treasury Cash Inclusion** | **Excluded** ($M_{\mathrm{treas}}$ omitted) | **Excluded** ($M_{\mathrm{treas}}$ omitted) | **Excluded** ($M_{\mathrm{treas}}$ omitted) | **Correctly Included** | **Correctly Tracked** ($M_{\mathrm{treas}}$ coordinate) |
| **Three-Sector Base Partition** | Double-counts bank cash | Double-counts bank cash | Double-counts bank cash | Combines cash and deposits | **Exact Disjoint Partition** (Def 10.19): Public + Banks + Treasury |
| **Systemic Run Transparency** | Concealed in scalar sum | Concealed in scalar sum | Concealed in scalar sum | Concealed in scalar sum | **Directly Measured**: Autonomous $\Delta_{\mathrm{overhang}}$ and $\rho$ (Def 10.20) |
| **Two-Tier Fiat LOLR Boundary** | Ignored | Ignored | Ignored | Ignored | **Dichotomy Exposed** (Prop 10.21a): Default vs. Base Inflation |
| **Factor Price Squeeze Coupling** | None (Macro scalar) | None (Macro scalar) | None (Macro scalar) | None (Macro scalar) | **Directly Coupled**: $\mathcal{S}(\omega, m, \mathcal{B}, x, \text{Cohort})$ (Thm 10.23) |
| **Dec 2024 Illustrative Value** | 18,211.0 billion USD | 21,371.0 billion USD | ~26,601.0 billion USD | 18,963.0 billion USD | Vector: $\langle 2{,}351.0, 15{,}860.0, 3{,}390.0, 752.0, 3{,}160.0 \rangle$ |
| **Total Base Money** ($M_{\mathrm{base}}^{\mathrm{total}}$) | 2,351.0B (Public only) | 2,351.0B (Public only) | 2,351.0B (Public only) | Unspecified | 6,493.0 billion USD ($M_{\mathrm{cash}}^{\mathrm{pub}} + R_{\mathrm{issuer}} + M_{\mathrm{treas}}$) |
| **Credit Phantom Distortion** | 0.0 | +3,160.0 billion USD | ~+8,390.0 billion USD | 0.0 | 0.0 (Credit tracked as separate coordinate) |
| **Unbacked Overhang** ($\Delta_{\mathrm{overhang}}$) | Concealed | Concealed | Concealed | Concealed | 12,470.0 billion USD (Def 10.20) |
| **Physical Reserve Coverage** ($\rho$) | Assumed 100% | Assumed 100% | Assumed 100% | Assumed 100% | 21.37% autonomous coverage (Prop 10.21a) |
| **Praxeological Status** | **Defective**: Violates spot-purchase feasibility | **Invalid**: Contradicts physical conservation | **Invalid**: Complete monetary breakdown | **Incomplete**: Correct credit rule, flawed scalar aggregation | **Rigorously Sound**: Matrix + Sectoral Projection |

---

## Core Findings from Comparative Analysis

1. **The Credit Double-Counting Distortion in Central Bank Aggregates:**
   By aggregating small time deposits (1,365.0 billion USD) and money market mutual fund shares (1,795.0 billion USD) into $M_1$, Federal Reserve $M_2$ fabricates **3,160.0 billion USD of phantom purchasing power** in December 2024. Over 62.8% of the nominal growth of $M_2$ in 2024 was an artifact of rate-seeking reallocations into term savings contracts (Proposition 10.10b), which contracted lenders' action menus rather than expanding spendable media. Broader measures ($M_3 / M_4$) compound this error to over 8.39 trillion USD by adding institutional repurchase agreements and commercial paper.
2. **The 12.47 Trillion USD Fiduciary Overhang Concealed by TMS:**
   While Rothbard-Salerno TMS purges credit double-counting, its scalar aggregation treats commercial bank checkable liabilities (15,860.0 billion USD) as identical to physical currency in circulation (2,351.0 billion USD). Benchmarking checkable liabilities against physical bank reserves (3,390.0 billion USD) reveals an **Unbacked Fiduciary Overhang of 12,470.0 billion USD** ($\Delta_{\mathrm{overhang}}$, Definition 10.20). Commercial bank reserves cover barely **21.37%** of checkable deposits ($\rho$, Proposition 10.21). Over 78.6% of checkable deposits lack base money backing, demonstrating that universal simultaneous par redemption is mathematically and physically impossible without central bank intervention (Proposition 10.12a, 10.21a).
3. **The Base Money Three-Sector Partition:**
   Central bank aggregates and TMS obscure the location of base reserves. In December 2024, total physical and digital central bank base money was **6,493.0 billion USD**, partitioned strictly into public currency ($M_{\mathrm{cash}}^{\mathrm{pub}} = 2{,}351.0\text{B}$), commercial bank custodial reserves ($R_{\mathrm{issuer}} = 3{,}390.0\text{B}$), and sovereign Treasury cash ($M_{\mathrm{treas}} = 752.0\text{B}$) (Definition 10.19). Separating these coordinates prevents double-counting bank reserves inside public cash.
4. **Actionable Structural Intelligence via Vector Accounting:**
   Representing money as the coordinate vector $\mathbf{M}(t, h)$ (Definition 10.19) derived from the underlying Endowment Matrix $\boldsymbol{\Omega}(t, h)$ provides macroeconomists with exact, actionable structural intelligence:
   - Measures genuine spendable media without fabricating credit phantoms (Proposition 10.10a, 10.10b).
   - Quantifies autonomous bank-run vulnerability via $\Delta_{\mathrm{overhang}}$ and $\rho$ (Definition 10.20, Proposition 10.21), identifying the exact point where central bank lender-of-last-resort fiat issuance ($\Delta M > 0$) must trigger purchasing-power dilution (Proposition 10.21a).
   - Traces sovereign liquidity flows ($M_{\mathrm{treas}}$) without confounding state and private purchasing power.
   - Evaluates supply chain solvency under factor price inflation via the cash-backed acceptance profile (Definition 10.22, Theorem 10.23).
   - Respects the boundary between observable balance-sheet records and unidentifiable counterfactual valuations, treating statistical classifications (MMDAs, sweep MMMFs) as observational coarse-grainings rather than absolute theoretical categories (Proposition 10.24).
5. **Operational Realities: Bank Tiers, Liquidity Freezes, and Standing Facilities:**
   - *Bank-Tier Asymmetry (Proposition 10.19a):* Aggregating reserves across all commercial banks masks critical concentration risks. Federal Reserve H.8 balance sheets show that large domestic money-center institutions ( $`\mathrm{Tier}_1`$ ) hold a disproportionate share of total reserves relative to regional and community institutions ( $`\mathrm{Tier}_2`$ ). As proved in Proposition 10.19a, when reserve distribution is asymmetric, the regional tier's coverage ratio ( $`\rho_{\mathrm{Tier}_2}`$ ) falls strictly below the consolidated system aggregate ( $`\rho_{\mathrm{agg}}`$ ), exposing regional banks to localized run infeasibility ( $q > R_{b_2}$ ) even when system-wide reserves appear abundant ( $R_{\mathrm{issuer}} \ge q$ ).
   - *Automated Sweeps and Liquidity Freeze Breakdown (Proposition 10.24):* Sweep accounts (shifting checkable deposits into overnight repos or MMMFs) enable spot purchases only via a two-step sequential bilateral credit advance. Under a liquidity freeze where secondary markets seize, conversion fails to execute; the buyer is forced into baseline inaction $\alpha_0$, leaving cash balances unchanged and stripping the spot trade from the feasible action menu.
   - *Standing LOLR Facilities (Proposition 10.21a):* Central bank emergency facilities (discount window, Standing Repo Facility) restore commercial bank reserve coverage only by encumbering commercial bank collateral assets while expanding total base money in circulation ( $+\Delta M$ ), directly triggering Cantillon purchasing power dilution.

---

## Conclusion

The search for a single scalar "money supply" is an artifact of aggregate macroeconomics refuted by the action axioms. The Rothbard-Salerno True Money Supply made a vital theoretical advance by purging credit double-counting, but retained the scalar error of equating unbacked fractional liabilities with physical base money. Grounded in Chapter 10 of our treatise, praxeological vector accounting replaces ad-hoc scalar metrics with a rigorous, coordinate-based representation of monetary reality that preserves physical conservation, respects spot-trade feasibility, and exposes systemic fractional-reserve vulnerability.
