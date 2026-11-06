# Mathematical specifications

The files in this directory describe selected Lean declarations and their
formal scope. The Lean code is authoritative when prose and a declaration
differ. A proved theorem establishes its proposition from its hypotheses; it
does not establish that those premises are universally true or that the
formalization is a complete account of an economic theory. See the
[claim and assumption register](claims_and_assumptions.md).

## Specifications

| Page | Main Lean modules | Scope |
|---|---|---|
| [01 Ontology and frames](01_ontology_and_frames.md) | [`Frame`](../Praxeology/Frame.lean), [`Frame/Core`](../Praxeology/Frame/Core.lean), [`Frame/Witnesses`](../Praxeology/Frame/Witnesses.lean) | Agents, time, histories, action menus, and frame instances |
| [02 Action and preference](02_action_and_preference.md) | [`Action`](../Praxeology/Action.lean) | Purposeful action, demonstrated preference, and modeled feasible menus |
| [03 Intertemporal marginal](03_intertemporal_marginal.md) | [`Marginal`](../Praxeology/Marginal.lean), [`Marginal/AllocationChoice`](../Praxeology/Marginal/AllocationChoice.lean), [`Marginal/AllocationActionFrame`](../Praxeology/Marginal/AllocationActionFrame.lean), [`Marginal/ComplementarityWitness`](../Praxeology/Marginal/ComplementarityWitness.lean) | Legacy allocation assumptions, derived ranked-prefix results and witnesses, complementary attainment, time preference, and interest conditions |
| [04 Catallactics and ECP](04_catallactics_ecp.md) | [`Catallactics`](../Praxeology/Catallactics.lean), [`Catallactics/Credit`](../Praxeology/Catallactics/Credit.lean) | Exchange, monetary processes, prices, calculation, and credit contracts |
| [05 Counterfactuals and regret](05_counterfactuals_regret.md) | [`Action`](../Praxeology/Action.lean), [`Entrepreneurship`](../Praxeology/Entrepreneurship.lean) | Context-matched regret and conditional entrepreneurial-cycle synthesis |
| [06 Firm boundary](06_firm_boundary.md) | [`Organization`](../Praxeology/Organization.lean), [`FirmBoundary`](../Praxeology/FirmBoundary.lean), [`FirmWitness`](../Praxeology/FirmWitness.lean) | Delegation, firm boundaries, information, and a finite workshop witness |
| [07 Business cycle](07_business_cycle.md) | [`Entrepreneurship`](../Praxeology/Entrepreneurship.lean), [`BusinessCycle`](../Praxeology/BusinessCycle.lean) and its submodules | Conditional cycle, cohort, information, and lifecycle results; a physical multi-borrower schedule exists, while its purposeful-choice/default/regret integration remains outstanding |
| [08 Econometric limits](08_econometric_limits.md) | [`EconometricLimits`](../Praxeology/EconometricLimits.lean) | Non-identifiability within specified interpretation classes and observations |
| [09 Behavioral poset](09_behavioral_poset.md) | [`BehavioralPoset`](../Praxeology/BehavioralPoset.lean) | Asymmetric preferences, conditional transitivity, menu examples, and a Condorcet witness |
| [10 State monopoly](10_state_monopoly.md) | [`StateMonopoly`](../Praxeology/StateMonopoly.lean) | Conditional institutional classifications and finite accounting results |
| [Comparison with Komendarczyk et al.](komendarczyk_contrast.md) | External companion and this repository | Formal scope, DMU assumptions, witness types, and library dependencies |

## Reading the specifications

Three distinctions are important throughout:

1. **A theorem versus an instantiated witness.** A theorem quantified over
   every `ActionFrame` is conditional on a supplied frame. A separate concrete
   instance is needed to witness the relevant economic scenario.
2. **A premise versus a derived result.** If a structure stores an optimality,
   preference, funding, or regret condition, a theorem using that structure
   does not derive the stored condition unless a separate result constructs it.
3. **Kernel validity versus economic fidelity.** Lean checks completed proofs
   against their formal premises. Interpreting those premises as a faithful
   economic theory remains a separate task.

## Library and foundational assumptions

This project uses Mathlib. Its use does not add axioms automatically, and
avoiding Mathlib would not by itself remove `Classical.choice` or other
dependencies. The accepted standard axiom dependencies and the declaration
audit are documented in the [root README](../README.md) and
[`claims_and_assumptions.md`](claims_and_assumptions.md). Project-specific
axioms and unfinished proofs are not accepted.

`natural_language/` remains a reader-facing draft. Chapters 2, 10, and 13 now
include targeted updates for the evaluation-horizon adapter, physical versus
purposeful credit evidence, and branch-sensitive cycle execution. A full
chapter-by-chapter fidelity review remains outstanding; the Lean declarations
remain authoritative where prose and source differ.
