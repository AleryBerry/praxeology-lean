# State Monopoly and Fiscal Extraction

Implementation: [`Praxeology/StateMonopoly.lean`](../Praxeology/StateMonopoly.lean), exported by `Praxeology`.

The module extends property-anchored bilateral interaction and firm uncertainty comparisons with explicit institutional and behavioral assumptions. It introduces no custom axioms.

## Institutional structure

`TerritorialMonopoly` uses the agents and actions of an `ActionFrame`. It records a ruler, a finite subject cohort, physical invasion, claimed licensing, rival defense, resistance, punishment, and an arbitration function. Invasive actions against subjects are licensed exclusively to the ruler. Rival defense and resistance attract punishment, backed by invasive force. Disputes involving a subject and the ruler are arbitrated by the ruler. These assumptions describe an institution; they do not establish its legitimacy.

`IsMarketCompetition` in `Catallactics` now requires both participants to be non-invasive and the competitor to prefer its competitive action to conditional inaction. The existing trichotomy witness supplies all three branches.

## Theorem 11.1: Taxation with public goods

`taxation_with_public_goods_is_extortion_not_catallactic` assumes a positive physical service quantity, invasion by the taxing party, purposeful compliance compared with punishment, dissent relative to the autonomous baseline, and a gain for the taxing party. It proves anchored extortion, failure of voluntary exchange, and `PurposefulResponseI`, while retaining positivity of the service quantity. Physical services alone do not imply consent or subjective benefit relative to autonomy.

`majoritarian_coalition_tax_is_political_means` proves that majoritarian coalition voting does not transmute coercive tax extraction into economic means: even when extraction is enacted by a winning coalition $`j`$, if it is endogenously invasive against taxpayer $`i`$'s clean-title endowment, it is classified strictly as political means (`IsPoliticalMeans`) and strictly fails to be voluntary exchange (`¬ IsEconomicMeans`).

## Theorem 11.2: Fiscal conservation and Calhoun class partition

`FiscalTransferSystem` records natural-number endowments and nonnegative deadweight loss, with total post-transfer holdings plus loss equal to initial holdings. `calhoun_fiscal_class_partition` proves that any strict net beneficiary requires a strict net payer. `no_universal_net_subsidy` rules out universal strict gain on a **nonempty** cohort. Empty cohorts and all-zero transfers are permitted by the accounting structure. The arithmetic does not itself prove coercion or aggregate utility loss.

`rent_seeking_dissipation_depletes_cohort` proves that when positive resources are consumed in rent-seeking contests or collection friction (`deadweight_loss > 0`), the aggregate post-transfer physical endowment of the cohort is strictly less than the pre-transfer initial endowment.

`calhoun_action_frame_run_class_partition` extends Calhoun's law to dynamic physical execution runs (`ActionFrameInventoryRun`): across any closed multi-moment execution history under zero-yield fiscal extraction, if an institutional extractor strictly expands its physical stock of factor $`m`$, physical conservation (*Laws in Re*) guarantees that at least one subject in the taxpayer cohort experiences strict physical stock depletion.

## Theorem 11.3: Production and ruler horizons

`BinaryFiscalDecision` specializes an existing `ActionFrame` to a feasible menu consisting of an active alternative and inertia. Its two local preference equivalences represent the actor's comparison of the specified returns. They are explicit modeling assumptions, not universal cardinal utility.

`purposeful_production_iff` proves that production is purposeful exactly when it is executed and retained output strictly exceeds the leisure threshold. `production_shutdown_boundary` excludes production at or above the extraction boundary and shows that any purposeful choice on this menu must be inertia. It does not infer execution from preference.

`voter_non_pivotality_blocks_purposefulness` demonstrates that if a voting action does not strictly improve the voter's return over the abstention baseline (`a ≤ b`), the voting act cannot be purposeful under the action frame. Furthermore, `action_non_pivotality_not_purposeful` shows that any active choice yielding an identical end to inaction is praxeologically non-purposeful by strict irreflexivity of preference.

`ruler_time_preference_extraction_bounds` supplies natural-number discount and retention bounds. `hoppe_ruler_time_preference_extraction` additionally connects strict discounted comparisons to the two rulers' `PurposefulAct` predicates, conditional on execution, and derives the caretaker's larger discount divisor from the two strict return bounds. The stationary ruler's baseline preserves the tax base; the caretaker's active alternative confiscates it. A strict caretaker gain is essential: the weak numerical bound permits ties, which do not establish active purposefulness. Natural-number division rounds down, and subtraction truncates at zero.

`hoppean_monarchical_vs_democratic_capital_exhaustion` deduces that the democratic caretaker ruler's shortened planning horizon drives purposeful rapid capital depletion of the productive tax base, while the hereditary dynastic owner purposefully conserves capital value across long horizons.

## Theorem 11.4: Judicial monopoly

`judicial_monopoly_self_exoneration` rules out purposeful self-limitation when expansion is feasible and strictly preferred. `territorial_judicial_monopoly_self_exoneration` uses the institution's arbitration identity to apply that result to the judge in a subject–ruler dispute. Neither theorem derives self-interested preferences from monopoly, nor proves inevitable constitutional drift across future histories.

`statutory_judicial_monopoly_self_exoneration` proves that when a sovereign magistrate holds monopoly arbitration jurisdiction over its own disputes, purposeful self-limitation against statutory expansion is praxeologically excluded.

## Theorem 11.5: Protected calculation blindness and master synthesis

`statutory_monopoly_calculation_bounds` proves that internal uncertainty can exceed spot-market uncertainty while a statutory penalty reverses the cost comparison facing entry. `statutory_monopoly_immunizes_calculation_blindness` connects those bounds to local operator and entrant decisions: the enacted protected operation is purposeful, while entry is not. The local return representations and execution are explicit hypotheses. Persistence requires these conditions to continue to hold; a single decision does not establish perpetual misallocation.

`statutory_monopoly_run_blindness_and_fiscal_incidence` unites Coasean-Misesian calculation blindness with multi-moment inventory run execution (`ActionFrameInventoryRun`): when a protected enterprise expands its physical endowment under calculation blindness and zero yield, Calhoun's physical conservation law guarantees that a net taxpayer is strictly depleted.

Finally, `state_monopoly_political_economy_master_synthesis` provides a unified master theorem combining:
1. Public-goods taxation as non-catallactic extortion;
2. Statutory calculation blindness under coercive entry penalties;
3. Calhoun physical taxpayer depletion across execution runs;
4. Judicial monopoly self-exoneration.

## Verification

Build with `lake build`. Concrete witnesses cover fiscal redistribution, discounting, positive services with extortion, territorial punishment, and a tied return that cannot justify active purposefulness even when the action is executed. Arithmetic boundary examples cover exact-threshold and above-output taxation. The root module re-exports the state-monopoly declarations.
