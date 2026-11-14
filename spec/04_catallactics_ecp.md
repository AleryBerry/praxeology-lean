# Specification 04: Exchange, money, prices, credit, and calculation

This page documents results in [`Praxeology/Catallactics.lean`](../Praxeology/Catallactics.lean)
and [`Praxeology/Catallactics/Credit.lean`](../Praxeology/Catallactics/Credit.lean).
The conclusions are conditional on each theorem's model and evidence; the
formal results should not be read as universal claims about actual markets.

## 1. Bilateral exchange

[`BilateralExchange`](../Praxeology/Catallactics.lean#L1168) requires distinct
agents, distinct goods, and purposeful enactment of the matching offer and
accept actions. [`double_inequality_of_exchange`](../Praxeology/Catallactics.lean#L1240)
derives that each active party prefers the outcome of its own exchange action
to its passive baseline. It is a result about the modeled bilateral exchange
predicate, not an empirical claim that every observed transfer is voluntary.

[`highwayman_is_purposeful_but_not_catallactic`](../Praxeology/Catallactics.lean#L153)
classifies one stipulated extortion scenario under the module's definitions.
Its scope depends on the model's baseline and end assignments; it does not
classify coercive cases in general.

## 2. Monetary-adoption processes

The profile operator [`Phi`](../Praxeology/Catallactics.lean#L1658) adds agents
meeting a specified marketability and indirect-feasibility predicate to
acceptance profiles. [`phi_inflationary`](../Praxeology/Catallactics.lean#L1664)
proves that profiles only grow under this operator. The concrete
[`concrete_phi_non_monotone_witness`](../Praxeology/Catallactics.lean#L1701) shows
that profile inclusion need not be preserved by the particular
maximum-marketability update.

[`universal_money_emergence`](../Praxeology/Catallactics.lean#L1829) is conditional:
given a fixed point, a selected medium that is maximally marketable there, and
feasibility for every agent, it proves that all agents accept that medium. It
does not derive such a fixed point or a unique currency from arbitrary initial
barter conditions. The separate
[`network_universal_money_emergence`](../Praxeology/Catallactics.lean#L2196)
derives a finite fixed point and universal acceptance under its assumptions of
a finite set of means, finite agents, a seed already accepting the candidate
medium, and connected unmet demand. It is relative to the defined finite
network adoption operator and the supplied network/wants relation.

The theorem
[`network_money_emergence_narrows_price_box_and_expands_solvency`](../Praxeology/Catallactics.lean#L3680)
adds a `NetworkPriceBoxSchedule` whose monotonicity links adoption-profile
growth to price-box narrowing. The resulting cash-demand and solvent-profile
conclusions are derived from that supplied schedule and its definitions; the
price-box response itself is not derived from the adoption process.

[`greshams_law_circulation_collapse`](../Praxeology/Catallactics.lean#L3860)
assumes a finite group of tenders, a two-medium tender choice, purposeful
tendering, and a preference for the modeled bad-medium outcome over the
good-medium outcome. Under those premises it proves the group does not tender
the good medium. The theorem does not derive the preference from legal tender
rules or show that every historical version of Gresham's law follows.

## 3. Prices and market clearing

[`marginal_pairs_equilibrium`](../Praxeology/Catallactics.lean#L2636) is an
arithmetic theorem: if an integer price satisfies the specified adjacent
buyer and seller reservation bounds, it is acceptable to the marginal buyer
and seller and deters the next buyer and seller. The bounds use integer
prices and unit steps; they are not a continuous price model.

[`purposeful_marginal_pairs_deterrence`](../Praxeology/Catallactics.lean#L2674)
connects those inequalities to a conditional ActionFrame conclusion, given
teleological bundle-dominance evidence for the extra-marginal buyer and seller.
[`MultilateralCohortMarket`](../Praxeology/Catallactics.lean#L2734) stores buyer and
seller reservation values. Its pairwise conservation theorem assumes the
matched pair's aggregate balance and invariance of all other agents; it does
not itself construct a clearing allocation or derive bilateral trades from
those reservation values.

The `CantillonNetwork` result assumes a higher post-change price and an
unchanged downstream money balance. It derives that one unit was affordable
at the earlier price while no positive quantity is affordable at the later
price. It does not derive the price increase, the monetary injection path, or
an economy-wide distributional effect from a network execution.

## 4. Credit contracts and monetary accounting

[`PawnLoanTerms`](../Praxeology/Catallactics/Credit.lean#L30) stores a positive
natural-number principal and the promised repayment amount directly. Its gross
repayment factor and net nominal rate are derived as rational numbers, and its
nominal premium is a signed integer amount. The contract representation
therefore admits positive, zero, and negative nominal rates; a theorem gives
simple amount-level examples of all three cases. This is representational
capacity, not a claim that any particular loan market will quote a negative
rate. Originary interest remains a separate intertemporal preference result.

The credit module records advances, fiduciary issuance, repayment, and unpaid
maturity as separate lifecycle evidence. Its accounting theorems derive
inventory changes from matched ActionFrame transfers and state when
redemption offers are infeasible for insufficient balances. The result
[`fiduciary_origination_and_cash_shortfall_contract_comparison`](../Praxeology/Catallactics/Credit.lean#L1812)
has additional strong premises: two terms share borrower, principal, and
money; a purposeful fiduciary issuance, origination, advance, and repayment
are represented; and the borrower's cash immediately before repayment falls
below the natural-repayment amount. Under those conditions it derives a
lower contractual repayment and gross factor for the credit contract, an
increase in total media from the fiduciary origination, and infeasibility of
the natural-repayment offer. It does not derive those contract terms or the
cash shortfall from a loan market, project technology, or monetary expansion.

## 5. Economic-calculation examples

[`socialist_calculation_incommensurability`](../Praxeology/Catallactics.lean#L3940)
constructs two strictly order-preserving rank assignments under which the
sum of two selected ranks reverses. It is a counterexample to using that
particular sum of ordinal ranks as an invariant comparison; it does not prove
that all calculation procedures in nonmarket institutions are impossible.

[`action_frame_socialist_calculation_impossibility`](../Praxeology/Catallactics.lean#L4077)
is a conditional two-economy planner result. It assumes physically
incomparable methods, matching observations and ends across two records, and
opposite stipulated local preference flags. It then proves that any
deterministic planner using the shared observation selects an option that
violates the defined Mengerian economizing condition in at least one record.
The theorem does not derive the model records or their opposite preferences
from a specified institution. Its interpretation as a general economic
calculation theorem needs additional modeling and witness work.

The textbook's former existential phrasing has been corrected: the Lean
declaration [`action_frame_socialist_calculation_impossibility`](../Praxeology/Catallactics.lean#L4077)
takes both economies and their disagreement as hypotheses. Its
physical-antichain hypothesis is copied into the conclusion and does no work
in the planner-rule case split, while the root module no longer labels a
forwarding theorem as a ground witness.

To close that witness gap within an explicitly delimited interface,
[`Praxeology/EconomicCalculation.lean`](../Praxeology/EconomicCalculation.lean),
[`Praxeology/EconomicCalculation/Institutions.lean`](../Praxeology/EconomicCalculation/Institutions.lean),
and [`Praxeology/EconomicCalculation/Incentives.lean`](../Praxeology/EconomicCalculation/Incentives.lean)
provide the generic common-decision criterion, full-information control,
strategic reporting rules including payoff-insensitive babbling lemmas
([`babbling_equilibrium_of_payoff_insensitive`](../Praxeology/EconomicCalculation.lean#L206)),
stock-synchronized certificate redemption
([`WorkLedger.redeem`](../Praxeology/EconomicCalculation.lean#L472)),
and concrete physical finite-economy witnesses:

- [`ground_action_frame_calculation_witness`](../Praxeology/EconomicCalculation/Institutions.lean#L1367)
  and the branching program proofs
  [`wantsC1_downstream_purposeful`](../Praxeology/EconomicCalculation/Institutions.lean#L1025)
  and [`wantsC2_downstream_purposeful`](../Praxeology/EconomicCalculation/Institutions.lean#L1142)
  derive physical conservation, factor scarcity, and purposeful downstream
  continuations over a shared branching `ActionFrame` without placing opposite
  current appraisals at a single decision node.
- [`voucher_accounting_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1461),
  [`io_accounting_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1524),
  [`transcript_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1553),
  and [`precommitment_zero_queue_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1585)
  prove impossibility for explicitly specified pre-commitment labor-voucher,
  input-output, multi-round transcript, and zero-queue administered-price
  interfaces where downstream end-valuation reports arrive only after the
  irreversible method commitment, alongside the explicit `InIndeterminacyCone`
  witness [`methods_in_indeterminacy_cone`](../Praxeology/EconomicCalculation/Institutions.lean#L1599).
- Six positive controls (`control_physical_dominance`,
  `control_reverse_dominance_and_tie`, `control_single_factor`,
  `control_successful_antichain`, `control_distinguishing_report`,
  `control_full_information`) and the exact equivalence theorems
  [`antichain_iff_param_conflict`](../Praxeology/EconomicCalculation/Institutions.lean#L1751)
  and [`param_unsolvable_iff_antichain_of_blind_obs`](../Praxeology/EconomicCalculation/Institutions.lean#L1781)
  characterize precisely when `PhysicalAntichain` creates an obstruction under
  world-blind observation. As noted in Mises, *Human Action* (Chapter XXVI, §1,
  "The Problem"), once ultimate valuations and complete data are supplied in
  advance (as in [`control_distinguishing_report`](../Praxeology/EconomicCalculation/Institutions.lean#L1735)),
  a deterministic planning rule can succeed; these theorems establish an
  impossibility relative to the specified restricted records rather than all
  conceivable planning algorithms or general strategic Lange equilibrium.
- Separately, [`Incentives.lean`](../Praxeology/EconomicCalculation/Incentives.lean)
  proves that equal clock-hour voucher compensation for easy vs. hard tasks
  induces every purposeful worker to select the easy task and starve
  downstream intermediate production
  ([`worker_every_purposeful_selects_easy`](../Praxeology/EconomicCalculation/Incentives.lean#L537),
  [`purposeful_easy_starves_downstream`](../Praxeology/EconomicCalculation/Incentives.lean#L577)),
  paired with an equal-effort control
  ([`equal_effort_hard_purposeful_and_downstream_feasible`](../Praxeology/EconomicCalculation/Incentives.lean#L723)).
