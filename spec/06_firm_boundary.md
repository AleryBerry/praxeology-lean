# Specification 06: Price Intervals, Signal Attenuation, and Conditional Firm Choice

Formal mathematical specification for [`Praxeology/FirmBoundary.lean`](../Praxeology/FirmBoundary.lean).

## Scope of the results

This module combines arithmetic results for price intervals and attenuation with a mechanism-level organizational choice theorem. The economic chain runs from observation maps to feasible production and exchange traces, from their stock-flow balances to individual appraisal through valued ends, and from those preferences to `PurposefulAct` and an organization network. Each premise has an interpretable role: observation channels describe received information; recipes describe input and output requirements; matched exchanges describe transfers; valued ends describe the entrepreneur’s monetary goal; feasible menus include the relevant rivals and passive retention.

The finite policy theorem [`firm_information_boundary_policy_witness`](../Praxeology/FirmBoundary.lean#L900) is an information result: when observationally equivalent states require different production decisions, no policy based on that observation can choose correctly in every state. Restoring the missing observation removes that conflict. The policy theorem alone says nothing about production yields or organizational advantage; the ActionFrame connection supplies those through [`ProjectedInventoryTrace`](../Praxeology/Production.lean#L391) and `FirmTraceSaleRecipe`.

`FirmTraceSaleRecipe` records initial cash and product stocks. Its cash equation is opening cash plus cash received in matched exchanges equals cash used plus terminal cash; production contributes no cash. Its product equation is opening product plus physical production equals product used in exchanges plus unsold terminal inventory; unmatched offers transfer nothing. `ActionFrameInventoryRun.inventory_balance` derives terminal inventory from the frame’s transition laws. An external `ServiceAccounting` structure can supply per-action service yields, which `InventoryRun.totalService` sums along the trace. Every other means coordinate remains computed from the trace. The operational scenario places the internal matched delivery, finishing production, and independent customer sale in the entrepreneur’s merge trace. It records resource availability for production and sale. If two organizational policies have identical tracked profiles, equality of their full trace inventories is required before their ends are identified; resource costs of administration and coordination therefore enter through the same stock-flow account.

The operator’s intermediate delivery has a further causal check in `DelegationCompensationEvidence`: the task is enacted, is nontrade production, and is the transition immediately preceding settlement. The operator starts with zero units of the delivered intermediate and does not use it as an input. `law_in_re_transition` therefore makes the post-task quantity equal the recipe yield, from which the delivered quantity is bounded. This prevents an existing or transferred good from being attributed to the operator’s production.

[`purposeful_firm_coalescence_from_information`](../Praxeology/FirmBoundary.lean#L1471) derives preferences from those traced outcomes, a valued end requiring monetary receipts, projected feasibility, and ActionFrame’s appraisal bridge. It then derives purposeful coalescence from actual execution and full feasible-menu coverage. The displayed signal-attenuation inequalities characterize the numeric parameter window used by this scenario; they do not substitute for the causal traces or the individual appraisal. The network theorem constructs its organizational evidence only after purposeful principal assignment, operator acceptance, and later purposeful task performance are established.

The generic result is applicable to any concrete organization whose observations, production recipes, matched transfers, valued ends, and feasible alternatives satisfy these conditions. A closed finite workshop instance with three agents and the full delegation-to-customer-sale trace is still needed to demonstrate all of these interfaces together in one model; the current finite trade frame establishes the external exchange component, while the generic trace theorems establish stock accounting for any ActionFrame, with service totals supplied externally when needed.

## Accepted direction and the market boundary

[`DelegationVocabulary`](../Praxeology/Organization.lean#L26) interprets action content: it identifies assignment/acceptance pairs, tasks covered by an assignment, and exchange terms authorized in advance. An [`AcceptedDelegation`](../Praxeology/Organization.lean#L70) requires the principal's purposeful assignment and instruction, the operator's purposeful acceptance, temporal precedence, and the operator's later purposeful execution of the assigned task on the same history. Passive refusal cannot count as acceptance, and an out-of-scope task cannot satisfy the execution record. The definition models voluntary delegated direction; it adds no legal-ownership premise.

An [`IndependentMarketInterface`](../Praxeology/Organization.lean#L332) combines a [`BilateralExchange`](../Praxeology/Catallactics.lean#L902) with evidence that seller and buyer act under independent governance principals. Each side has a `GovernanceRole` tying its actual Offer or Accept to direct principal authority or an accepted task scope. Fixed-price and continuing contracts qualify when authority is independent; the separate `FreshlyBargainedInterface` describes the narrower case of new bargaining at the interface. [`DelegatedInternalTransfer`](../Praxeology/Organization.lean#L235) identifies an authorized internal transfer through its accepted terms.

[`GovernanceRole`](../Praxeology/Organization.lean#L321) identifies an actor, principal, decision capacity, and authority for the transaction’s specific Offer or Accept action. Direct principal action uses the principal’s own authority; a delegate must have an `AcceptedDelegation` whose task scope contains that action. [`OrganizationNetwork`](../Praxeology/Organization.lean#L636) locates these relationships on stage edges and aligns the relevant actors and tasks. Its external edge is backed by purposeful exchange between independent governance principals; it need not be newly bargained. `HasFirmStructure` requires a connected three-stage path, and `connected_chain_coherence` retains the common history and temporal order. The `threeStageFirmNetwork` constructor allows the seller to represent the producing principal, so an authorized entrepreneur or salesperson can sell the firm’s output. It derives its internal and market edges from action-level evidence. The `subjectiveTradeBoundaryNetwork` witnesses an external market edge in the finite trade frame; its scope is the exchange interface, not the complete productive workshop.

The finite signal policies are linked to [`KnowledgeRelation`](../Praxeology/EpistemicAbility.lean#L24): states are indistinguishable exactly when the modeled organization supplies the same observation. In `InformationGroundedFirmDecision`, each channel supplies a history-indexed observation record, and a proof ties that record to the channel’s information map. The actual instruction is selected from the received record. The general lemma [`no_knowledge_respecting_policy_across_conflict`](../Praxeology/Organization.lean#L894) yields an obstruction when observationally equivalent states require different tasks; it does not imply that an agent cannot purposefully act under uncertainty.

Finally, [`OperationalFirmBoundaryDecision`](../Praxeology/FirmBoundary.lean#L1723) links a proposed contract and later task to purposeful principal assignment and instruction, purposeful operator acceptance and productive execution, finishing production, and an external purposeful exchange. `DelegationCompensationEvidence` requires positive raw-material and capacity use, their availability at the work node, positive delivery and compensation quantities, and delivery bounded by the task’s physical yield. The immediate production transition and zero opening stock now derive availability of the delivered intermediate at settlement. A matched internal exchange settles the contract after production. The principal then purposefully uses the delivered intermediate and capacity to make the tracked final good; the trace records that production before the external sale, and the sale goods and payment must be available at the transaction node. The network is constructed from these behavioral and catallactic certificates. A closed finite three-agent `ActionFrame` deriving the entrepreneur’s, operator’s, and customer’s choices from their valued ends and alternatives remains necessary for an end-to-end witness.

## 1. Price boxes and relative cost indeterminacy

For a finite set of factors, a price box is a coordinatewise interval

```math
\\mathcal{B}_t := \\prod_{k=1}^d \\left[ \\underline{P}_t(m_k), \\overline{P}_t(m_k) \\right] \\subseteq \\mathbb{Q}^d.
```

[`InPriceBox`](../Praxeology/FirmBoundary.lean#L48) formalizes membership in such a box. [`InIndeterminacyCone`](../Praxeology/FirmBoundary.lean#L51) says that the cost ranking of two input vectors reverses at two prices in the box. For application to a production decision, the box is read as the range of market quotes or defensible price bounds available to the entrepreneur; the theorem identifies when that range permits opposite cost rankings.

If one input vector uses no more of each factor than another, its cost cannot exceed the other's at a nonnegative price vector, so that pair cannot reverse its cost ranking in the box ([`robust_dominance_excludes_indeterminacy`](../Praxeology/FirmBoundary.lean#L69)). When every price interval is a singleton, there is only one price vector, so the reversal predicate is empty ([`degenerate_box_eliminates_indeterminacy`](../Praxeology/FirmBoundary.lean#L127)).

## 2. Uniform cost comparison under price bounds

[`hayekian_epistemic_compression`](../Praxeology/FirmBoundary.lean#L85) assumes each state-indexed realized price vector lies in a supplied box. If the worst-case cost of input vector $\mathbf{x}$ is below the best-case cost of $\mathbf{y}$, then $\mathbf{x}$ is cheaper at every realized price vector. This gives a usable decision rule when an entrepreneur has reliable bounds on relevant factor prices across the states under consideration.

## 3. Arithmetic comparison of uncertainty indices

The definitions `InternalFirmUncertainty` and `SpotMarketUncertainty` assign numerical values to blur, spread, grid-step, and scale parameters. [`master_coalescence_inequality`](../Praxeology/FirmBoundary.lean#L521) shows that the internal index is lower exactly when the accumulated internal blur is below the price-spread-plus-grid-step expression. In an applied model, these inputs correspond to reporting precision, delay, rounding, and observed quote dispersion; the theorem gives the parameter condition under which the defined comparison changes sign.

## 4. Cost comparability, rank reversal, and stage counts

[`positive_prices_and_ordinal_rank_sum_reversal`](../Praxeology/FirmBoundary.lean#L555) combines two mathematical facts: strictly positive prices give positive costs for the specified positive input plans, and order-preserving relabelings can reverse a sum of ordinal ranks. The latter establishes that such sums are not invariant ordinal comparisons. It does not formalize market extinction or an economic-calculation impossibility; those conclusions require separate premises linking governance, actual price records, and the entrepreneur’s available comparisons.

The stage-count lemmas state that integrating \(K\) of \(L\) stages leaves \(L-K\) stages outside that chain. [`viable_coalescence_window`](../Praxeology/FirmBoundary.lean#L580) proves the arithmetic implication. In an organization model, the residual stages count as external only when actual exchange interfaces connect them to independent counterparties.

### Refutation of the Arithmetic Stage-Count Fallacy

Verbal expositions often claim that integrating all stages of a vertical production chain (\(K = L\)) automatically destroys economic calculation. Theorem [`vertical_integration_stage_count_fallacy_refuted`](../Praxeology/FirmBoundary.lean#L916) formally refutes this arithmetic stage-count claim:
1. Complete vertical integration of all \(K = L\) stages with intact external benchmark quotes (`org = .bothSignals` or `org = .factorRestored`) achieves 100% policy correctness across all demand-by-factor states (`PolicyCorrect org s`).
2. Conversely, partial integration (or spot fragmentation) where external market quotes are concealed (`org = .factorHidden` or `org = .demandHidden`) strictly generates an unresolvable epistemic observation-class conflict:

```math
\neg \exists \pi : \text{Bool} \times \text{Bool} \to \text{FirmProductionDecision},\quad
\forall s,\quad \pi(\text{informationObservation}(\text{org}, s)) = \text{firmRequiredDecision}(s).
```

Therefore, calculation blindness is not an arithmetic function of vertical integration stage depth (\(K = L\)), but an epistemic observation-class conflict where the disappearance of external prices leaves states with disjoint required decisions observationally indistinguishable. Certified with strictly zero transitive axioms (`[] (0 axioms)`).

## 5. Conditional purposeful coalescence and credit regret

The theorem [`purposeful_operational_firm_boundary`](../Praxeology/FirmBoundary.lean#L1868) applies the action axiom to supplied feasibility, execution, preference, and complete-menu conditions. Its choice conclusion is conditional on those preference comparisons. The trace-grounded result instead derives the entrepreneur’s comparisons from initial inventories, production and matched-transfer flows, unsold output, a valued monetary end, and the ActionFrame appraisal rules. It derives purposeful choice when the chosen alternative is feasible and executed and no action in the specified complete menu dominates it. The signal inequalities characterize the modeled reporting path; they do not replace the physical and choice premises.

The arithmetic result [`artificial_conglomeration_firm_boundary_distortion`](../Praxeology/FirmBoundary.lean#L1999) derives return-threshold and uncertainty inequalities from numeric assumptions. It does not model a loan lifecycle, a bust branch, or regret. [`credit_expansion_expands_hop_horizon`](../Praxeology/FirmBoundary.lean#L1989) is another conditional inequality result; neither theorem establishes that actual credit expansion causes purposeful conglomeration.

## 6. Interval coarsening and indeterminate-pair counts

`IndeterminacyAntichainWidth` currently denotes the cardinality of **ordered plan pairs** in a finite menu whose cost rankings can reverse inside a price box. It is not defined as the width of a partial order or as a Dilworth invariant. The established name is retained for compatibility, while this specification states its actual mathematical meaning.

Box widening weakly increases this count, and a concrete finite example exhibits strict increase ([`stage_coarsening_expands_antichain_width`](../Praxeology/FirmBoundary.lean#L2203), [`order_theoretic_firm_boundary_non_vacuous`](../Praxeology/FirmBoundary.lean#L2218)). The count can compare decision environments when their observed price bounds and feasible methods are represented by the corresponding boxes and menus. A preference conclusion still follows from actors’ appraisals of the resulting production and exchange outcomes, as in the trace-grounded theorem above.
