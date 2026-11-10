# Formalized Austrian Praxeology in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.35.0-blue)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-blue)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **“Human action is an attempt to ease discomfort by making things better. It reflects subjective values under uncertainty: an available option is chosen when its intended result is preferred to doing nothing and no available alternative seems better, while inaction follows when no option seems better. When the options remain available in every situation the actor considers possible, preferring one requires a better result in at least one, while an option that does no worse in any and better in one must be preferred. Even then, the intended result may not be achieved.”**

A machine-checked mathematical development of formal models motivated by Austrian praxeology. It covers purposeful choice, subjective valuation, intertemporal choice, exchange, monetary coordination, entrepreneurial error, and institutional constraints. Individual results are conditional on the definitions, model structures, and hypotheses stated in Lean.

The project develops a formal framework connecting modeled purposeful choice to physical feasibility, exchange, information, and institutional organization. The exact scope and assumptions of headline results are recorded in [`spec/claims_and_assumptions.md`](spec/claims_and_assumptions.md). Formal validity and fidelity to Mises, Menger, Rothbard, or other economic writing are separate questions.

> [!NOTE]
> **Notice & Disclaimer:** This project is an independent, AI-assisted formalization based on the broader literature cited in [References](#references). After initial development was underway, the project was informally refined against the paper *"A Formalization of Austrian Economics"* (Komendarczyk, Rafał, Block, Walter E., Levendis, John, & Tipler, Frank) and their repository [`rafkom72/praxeology-lean`](https://github.com/rafkom72/praxeology-lean).
>
> It is not officially affiliated with or endorsed by the authors. For their authoritative academic formalization, see their paper ([arXiv:2606.18292](https://arxiv.org/abs/2606.18292)) and repository. See [`spec/komendarczyk_contrast.md`](spec/komendarczyk_contrast.md) for a technical comparison with their base system.

## Contents

- [Mathematical architecture](#mathematical-architecture)
  - [Epistemological foundation: the Action Axiom and ActionFrame](#epistemological-foundation-the-action-axiom-and-actionframe)
  - [Core structural components](#core-structural-components)
  - [Uncertainty, plausible circumstances, and deliberation](#uncertainty-plausible-circumstances-and-deliberation)
  - [Representation conventions in Lean](#representation-conventions-in-lean)
- [Module architecture and dependency flow](#module-architecture-and-dependency-flow)
- [Formal coverage](#formal-coverage)
- [Methodological scope, feasibility, and model witnesses](#methodological-scope-feasibility-and-model-witnesses)
- [Documentation and repository organization](#documentation-and-repository-organization)
- [Building and verification](#building-and-verification)
- [References](#references)

## Mathematical architecture

### Epistemological foundation: the Action Axiom and ActionFrame

In simple terms, [`ActionFrame`](Praxeology/Frame/Core.lean#L276) is the foundational formal model in which the Action Axiom is defined. It establishes the universe of discourse—agents, moments, branching histories, means, and ends—that allows purposeful human choice to be stated with mathematical precision.

Rather than relying on neoclassical aggregate equilibrium functions or ad-hoc premise structures, this single unified ontology provides the machine-checked deductive foundation for the major theoretical pillars of the **Austrian School of Economics (ASE)**:
* **Subjective Value & Marginal Utility:** Mengerian ranked-use choice, diminishing marginal utility derived without cardinal utility metrics, and factor complementarity ([`Marginal.lean`](Praxeology/Marginal.lean)).
* **Time Preference & Capital Structure:** Böhm-Bawerkian multi-stage capital gestation, roundabout production processes, and intertemporal opportunity cost ([`Production.lean`](Praxeology/Production.lean)).
* **Catallactics & Economic Calculation:** Bilateral voluntary exchange, Ricardian comparative advantage (Mises' *Law of Association*), and the epistemic necessity of market prices for rational capital allocation ([`Catallactics.lean`](Praxeology/Catallactics.lean)).
* **Entrepreneurship & Firm Boundaries:** Kirznerian arbitrage, Coasean-Austrian firm boundaries, internal delegation, and the limits of central economic planning ([`Organization.lean`](Praxeology/Organization.lean), [`FirmBoundary.lean`](Praxeology/FirmBoundary.lean)).
* **The Austrian Business Cycle Theory (ABCT):** The full Mises-Hayek monetary transmission mechanism—from unbacked fiduciary credit expansion to artificially depressed interest rates, factor market squeezes, capital malinvestment, completion bottlenecks, and cluster defaults ([`BusinessCycle.lean`](Praxeology/BusinessCycle.lean), [`BusinessCycle.MasterResults`](Praxeology/BusinessCycle/MasterResults.lean)).
* **Interventionism & State Monopoly:** The formal boundary between voluntary contract and coercive menu-stripping, statutory calculation deadbands, and territorial extraction ([`StateMonopoly.lean`](Praxeology/StateMonopoly.lean)).

A common misconception in formal economics is to treat the Action Axiom (*"Man acts"*) as an empty syntactic token, and to view the spatiotemporal, physical, and counterfactual structure of `ActionFrame` as an external overlay. In Austrian praxeology (Mises, Rothbard, Hoppe), this is a category error:

1. **The Essential Categories of Action:** Action is inconceivable in a vacuum. To say that human action occurs already implies:
   - **Time and the Open Future:** Action is directed toward altering future states; it requires an irreversible temporal flow, a fixed past, and a branching future of open possibilities.
   - **Physical Scarcity and Causality:** An actor must allocate scarce physical means subject to conservation laws to achieve desired ends. Without scarcity and causality, economizing and choice cannot exist.
   - **Counterfactuals and Opportunity Cost:** Choosing path $\alpha$ means forgoing path $\beta$. If alternative courses were never feasible, no genuine choice occurred.

   Therefore, [`ActionFrame`](Praxeology/Frame/Core.lean#L276) does not replace or dilute the Action Axiom. It is the **rigorous mathematical articulation of the essential ontological categories presupposed by the Action Axiom itself**.

2. **Methodological Individualism:**
   Markets, prices, money, credit contracts, firms, and state interventions do not exist as autonomous aggregate entities. They are configurations of acting human beings. In this formalization, every institution—from bilateral exchange and loan markets to firm delegation and state taxation—is modeled strictly through individual agents executing purposeful choices ([`PurposefulAct`](Praxeology/Action.lean#L232)) within their feasible menus.

3. **Branching Possibilities vs. Deterministic Forcing:**
   The formalization does not hardcode crises or force institutional outcomes. Because `ActionFrame` models branching time, it defines an open space of realizable history paths where the universal analytical laws of praxeology govern all possible regimes:
   - At every decision situation, acting agents face menus of feasible alternatives—whether to consume or save, trade voluntarily or coerce, coordinate through market prices or impose central edicts, maintain sound money or expand unbacked fiduciary credit.
   - Across all branches, the core praxeological and physical laws (conservation of means, ordinal evaluation, opportunity cost, and capital gestation) hold universally. What is contingent is which historical trajectory is realized through the actions chosen:
     - In **catallactics and exchange**, voluntary bilateral exchange yields mutual gains from trade, whereas coercive intervention contracts feasible choice menus and impairs economic calculation.
     - In **capital and credit (ABCT)**, the genuine saving branch channels real factors into sustainable roundabout production, whereas the fiduciary credit expansion branch induces entrepreneurial entry under false interest rate signals, inevitably driving the trajectory toward factor market squeezes, cluster errors, and contractual defaults.
   - Hence, the comprehensive theoretical framework of Austrian economics always applies to human action; what an economy experiences in history depends on which specific branch of choices is enacted.

### Core structural components

[The common formal framework](Praxeology/Frame/Core.lean#L276) supplies an ontology of agents, moments, histories, actions, means, and ends. Its structural conditions connect five components:

1. **Branching time and agency.** Histories are maximal temporal chains. History extensionality identifies histories with the same incident moments; no choice between undivided histories constrains enacted actions on histories sharing a strict future moment. Feasible actions have realizable choice cells, including a passive baseline.
2. **Physical feasibility and transitions.** Finite menus distinguish contemplated actions from feasible actions. Endowments, input requirements, production yields, and bilateral transfers constrain resource use. Multi-step inventory accounting and optional service yields are handled in [`Production.lean`](Praxeology/Production.lean).
3. **Ordinal evaluation.** A shared requirement schedule applies to ends, while subjective valuation identifies which ends matter to an agent at a decision situation. The core account needs no separate domains for wants or services. Asymmetric preference supports strict comparison without cardinal utility; results needing transitivity or stronger order properties state those assumptions separately.
4. **Deliberation and counterfactuals.** Minimal plausibility, projected decision moments, branch selection, and expected maturation make the evaluated alternative explicit. The [action module](Praxeology/Action.lean) and [`Entrepreneurship`](Praxeology/Entrepreneurship.lean) distinguish ordinary branch comparisons from regret grounded in shared causal contexts.
5. **Explicit bridges.** Physical stocks and numerical inequalities do not imply a choice by themselves. Applications state the preference, feasible-menu, and execution conditions that connect an accounting result to an action conclusion.

With the agent, moment, and history fixed, the formal predicate [`PurposefulAct`](Praxeology/Action.lean#L232) in [`Action.lean`](Praxeology/Action.lean) is:

```math
\begin{aligned}
\text{PurposefulAct}(\alpha^{\ast})\iff{}&
\alpha^{\ast}\in A_{\mathrm{feas}}\ \wedge\ \text{Exec}(\alpha^{\ast})\\
&\wedge\bigl(\alpha^{\ast}=\alpha_0\ \vee\ \text{EndOf}(\alpha^{\ast})\succ\text{EndOf}(\alpha_0)\bigr)\\
&\wedge\forall\beta\in A_{\mathrm{feas}},\ \neg\bigl(\text{EndOf}(\beta)\succ\text{EndOf}(\alpha^{\ast})\bigr).
\end{aligned}
```

The definition specifies four core conditions for purposeful choice:
* **Feasibility and Execution:** The chosen action $\alpha^{\ast}$ belongs to the feasible menu $A_{\mathrm{feas}}$ and is physically executed at the decision moment on history $h$.
* **Baseline Inaction** ($\alpha_0$): Inaction is always admissible. An active action must strictly improve upon doing nothing: $\text{EndOf}(\alpha^{\ast})\succ\text{EndOf}(\alpha_0)$.
* **Undominatedness:** No feasible alternative $\beta \in A_{\mathrm{feas}}$ yields an end strictly preferred to $\alpha^{\ast}$.
* **Incomplete Preferences:** Preferences are not required to be total or complete; ties and mutually incomparable ends are allowed. Purposeful action requires that the chosen alternative is not strictly dominated, not that the actor consciously computes a global optimum.

### Uncertainty, Plausible Circumstances, and Deliberation

The choice is judged by the actor’s own preference at that moment, connecting subjective evaluation to the outcomes regarded as plausible:

* **Existential Support:** When both courses are feasible in considered circumstances, preferring one end over another is supported by a favorable outcome in at least one plausible circumstance.
* **Universal Weak Dominance:** Conversely, if one course's outcome is at least as good in every plausible circumstance and strictly better in at least one, that supports preferring its end.
* **Consistency of Active Choice:** When available courses remain open across considered circumstances, an active purposeful choice has support over inaction in at least one circumstance, and no rival is strictly better in all of them.

> [!NOTE]
> These properties are **conditional implications** derived from the formal account of uncertainty, rather than extra ad-hoc clauses added to the definition of purposeful choice. Economic applications then combine purposeful choice with domain-specific technological, informational, or institutional conditions.

### Representation Conventions in Lean

The formalization distinguishes unordered collections from ordered sequences:
* [`Finset`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html) is used for unordered collections (menus of actions, commodity bundles, sets of ends).
* [`List`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Basic.html) is used where sequential order and computational determinism matter (chronological histories, loan auction priority queues, deterministic searches).

## Module architecture and dependency flow

The diagram below illustrates the conceptual architecture and dependency flow of the library across its primary subsystems, concrete models, and empirical witnesses:

```mermaid
flowchart TB
    %% Categorized Subgraphs

    subgraph Foundations ["Foundations & Epistemic Deliberation"]
        direction TB
        ExactNat["ExactNat"]
        Frame["Frame"]
        Action["Action"]
        Production["Production"]
        Subjective["Subjective"]
        Veridical["Veridical"]
        Marginal["Marginal"]
        EpistemicAbility["EpistemicAbility"]
    end

    subgraph Institutions ["Catallactics, Capital & Institutions"]
        direction TB
        Catallactics["Catallactics"]
        CatallacticsCredit["Catallactics.Credit"]
        Organization["Organization"]
        FirmBoundary["FirmBoundary"]
        StateMonopoly["StateMonopoly"]
        Entrepreneurship["Entrepreneurship"]
    end

    subgraph Execution ["Physical Execution & Market Clearing"]
        direction TB
        FiniteEconomy["FiniteEconomy"]
        ProgActionFrame["FiniteEconomy.ProgramActionFrame"]
        Auctions["BusinessCycle.Auctions"]
        Regimes["BusinessCycle.Regimes"]
        FactorExec["BusinessCycle.FactorExecution"]
        ProfileProg["BusinessCycle.ProfileProgram"]
        Outcome["BusinessCycle.Outcome"]
    end

    subgraph CycleSynthesis ["Business Cycle Analysis & Synthesis"]
        direction TB
        CycleInfo["BusinessCycle.Information"]
        CycleClusters["BusinessCycle.Clusters"]
        CycleFirms["BusinessCycle.Firms"]
        BehavProg["BusinessCycle.BehavioralProgram"]
        BehavChoices["BusinessCycle.BehavioralChoices"]
        IntegResults["BusinessCycle.IntegratedResults"]
        MasterResults["BusinessCycle.MasterResults"]
        BusinessCycle["BusinessCycle"]
    end

    subgraph Witnesses ["Witnesses, Countermodels & Lifecycle Checks"]
        direction TB
        FrameWitnesses(["Frame.Witnesses"])
        AllocationActionFrame(["Marginal.AllocationActionFrame"])
        FirmWitness(["FirmWitness"])
        CreditLifecycle(["BusinessCycle.CreditLifecycleFrame"])
        CycleDefault(["BusinessCycle.DefaultWitness"])
        PhysicalSettlement(["BusinessCycle.PhysicalSettlementWitness"])
        CycleGrounded(["BusinessCycle.Grounded"])
    end

    subgraph Limits ["Methodological Scope & Identification"]
        direction TB
        EconometricLimits["EconometricLimits"]
    end

    %% Architectural & Definitional Dependencies (Solid Arrows)
    ExactNat --> Marginal
    Frame --> Action
    Action --> Production
    Action --> Subjective
    Subjective --> Veridical
    Action --> Marginal
    Production --> Marginal
    Action --> EpistemicAbility

    Marginal --> Catallactics
    Catallactics --> CatallacticsCredit
    CatallacticsCredit --> Entrepreneurship
    Catallactics --> Organization
    Organization --> FirmBoundary
    FirmBoundary --> StateMonopoly

    Catallactics --> FiniteEconomy
    FiniteEconomy --> ProgActionFrame
    ProgActionFrame --> ProfileProg

    Auctions --> Regimes
    Regimes --> FactorExec
    FactorExec --> ProfileProg
    ProfileProg --> Outcome

    EpistemicAbility --> CycleInfo
    Entrepreneurship --> CycleInfo
    CycleInfo --> CycleClusters
    FirmBoundary --> CycleFirms

    Outcome --> BehavProg
    BehavProg --> BehavChoices
    BehavChoices --> IntegResults
    IntegResults --> MasterResults
    MasterResults --> BusinessCycle

    CycleClusters --> BusinessCycle
    CycleFirms --> BusinessCycle

    Marginal --> EconometricLimits

    %% Witness, Countermodel & Lifecycle Checks (Dashed Arrows)
    Frame -. "model witness" .-> FrameWitnesses
    Marginal -. "discrete allocation" .-> AllocationActionFrame
    Organization -. "workshop witness" .-> FirmWitness
    CatallacticsCredit -. "lifecycle check" .-> CreditLifecycle
    CreditLifecycle -. "unpaid maturity" .-> CycleDefault
    FactorExec -. "settlement check" .-> PhysicalSettlement
    Entrepreneurship -. "2-agent witness" .-> CycleGrounded
    CycleDefault -. "lifecycle input" .-> BusinessCycle
    CycleGrounded -. "cohort input" .-> BusinessCycle
    PhysicalSettlement -. "settlement input" .-> BusinessCycle
```

Each module is linked in the [coverage table](#formal-coverage) below, and the root [`Praxeology.lean`](Praxeology.lean) module re-exports the public library modules.

### Axioms and assumptions

The project declares no custom Lean [`axiom`](https://lean-lang.org/doc/reference/latest/Axioms/) and has no unfinished [`sorry`](https://lean-lang.org/doc/reference/latest/Axioms/) proofs. Its transitive axiom audit reports standard Lean dependencies such as [`Classical.choice`](https://lean-lang.org/doc/reference/latest/Axioms/), [`Quot.sound`](https://lean-lang.org/doc/reference/latest/Axioms/), and [`propext`](https://lean-lang.org/doc/reference/latest/Axioms/). These dependencies are distinct from importing Mathlib; neither the use nor avoidance of Mathlib determines soundness. The accepted axiom set and economic premises are documented in the [claim and assumption register](spec/claims_and_assumptions.md).

## Formal coverage

The root module [`Praxeology.lean`](Praxeology.lean) imports the public library modules. The principal modules and their roles are:

| Module | Principal mathematical content |
|---|---|
| [Frame](Praxeology/Frame.lean) | Branching-time histories, action menus, endowments, preferences, ends, and physical transition laws |
| [Frame.Witnesses](Praxeology/Frame/Witnesses.lean) | Finite branching models and bilateral trade ActionFrame witnesses |
| [Action module](Praxeology/Action.lean) | Purposeful choice, preference, opportunity costs, plausible histories, and contextual regret |
| [Subjective](Praxeology/Subjective.lean) | Subjective scenario systems, independent carrier type, observation agreement, appraisal rules, and purposefulness certificates |
| [Veridical](Praxeology/Veridical.lean) | Veridical scenario embeddings, cross-forecast physical inventory invariance theorems, and domain veridical instances |
| [Production](Praxeology/Production.lean) | Inventory steps and runs, additive stock balances, and external service accounting |
| [ExactNat](Praxeology/ExactNat.lean) | Exact natural-number remainders and additive certificates |
| [Marginal](Praxeology/Marginal.lean) | Endogenous Mengerian factor complementarity, imputed marginal yield, teleological quantum capacity bounds, and intertemporal preference structures |
| [Marginal.AllocationChoice](Praxeology/Marginal/AllocationChoice.lean) | Stock-independent ranked-use technology, local ordinal laws, derived ranked-prefix choice, capacity tables, satiation, and countermodels for incomplete menus or missing replacement laws |
| [Marginal.AllocationActionFrame](Praxeology/Marginal/AllocationActionFrame.lean) | Complete finite allocation menus and purposeful ranked-prefix actions at distinct one-unit and two-unit stocks in one ActionFrame |
| [EpistemicAbility](Praxeology/EpistemicAbility.lean) | Choice-cell guarantees, causal ability, knowledge, and know-how |
| [Catallactics](Praxeology/Catallactics.lean) | Exchange, comparative advantage, monetary adoption, prices, and calculation |
| [Catallactics.Credit](Praxeology/Catallactics/Credit.lean) | Loan lifecycle and fiduciary issuance accounting; contractual repayment is stored directly and the derived rational nominal rate can be positive, zero, or negative |
| [Organization](Praxeology/Organization.lean) | Delegation, instructions, internal transfers, and independent market interfaces |
| [Entrepreneurship](Praxeology/Entrepreneurship.lean) | Credit, investment, capital formation, completion bottlenecks, and regret |
| [FirmBoundary](Praxeology/FirmBoundary.lean) | Price boxes, information, production traces, and organizational choice |
| [FirmWitness](Praxeology/FirmWitness.lean) | A finite workshop and its action, production, transfer, and sale sequence |
| [BusinessCycle](Praxeology/BusinessCycle.lean) | Public synthesis of conditional cycle, information, cohort, firm, one-project, unpaid-maturity, behavioral-choice, and contextual-regret results |
| [BusinessCycle.Information](Praxeology/BusinessCycle/Information.lean) | ActionFrame-indexed Catallactics signals, observation-based knowledge, and policy response |
| [BusinessCycle.Clusters](Praxeology/BusinessCycle/Clusters.lean) | Conditional ActionFrame cohort results for shared-input and price squeezes, with regret composition |
| [BusinessCycle.CreditLifecycleFrame](Praxeology/BusinessCycle/CreditLifecycleFrame.lean) | Multi-stage credit lifecycle events, advances, repayments, and finite tree branches |
| [BusinessCycle.DefaultWitness](Praxeology/BusinessCycle/DefaultWitness.lean) | Separate unpaid-maturity path through an unmatched repayment acceptance; aggregate collateral inventory includes an intervening matched advance, with legal title and foreclosure outside that frame |
| [BusinessCycle.Auctions](Praxeology/BusinessCycle/Auctions.lean) | Deterministic loan bids and factor-price clock; projected reservation preferences and price-affordability calculations |
| [BusinessCycle.Regimes](Praxeology/BusinessCycle/Regimes.lean) | Three five-project source-and-use scenarios, projected and forecast-price calculations, and sufficient-input boundary calculations; cash endowment and transfer remain explicit premises |
| [BusinessCycle.FactorExecution](Praxeology/BusinessCycle/FactorExecution.lean) | Physical note issuance, household deposit exchange, loan advances, early-input purchases, capital formation, factor purchases, completion, output sales, repayment, and contractual settlement |
| [BusinessCycle.ProfileProgram](Praxeology/BusinessCycle/ProfileProgram.lean) | Recursive ActionFrame adapter with a finite household plan menu and branch-state market clearing; records matched transactions and contractual outcomes but does not prove purposeful household or entrepreneur choices |
| [BusinessCycle.Outcome](Praxeology/BusinessCycle/Outcome.lean) | Projection that bundles interpreter-derived inventories and services with matched deposit, credit, default, and collateral records |
| [BusinessCycle.BehavioralProgram](Praxeology/BusinessCycle/BehavioralProgram.lean) | Project-two ActionFrame menu, local observation, four-factor forecast, and subjective purposeful acceptance proof |
| [BusinessCycle.BehavioralChoices](Praxeology/BusinessCycle/BehavioralChoices.lean) | Purposeful household saving under an explicit terminal preference and finite plan menu |
| [BusinessCycle.IntegratedResults](Praxeology/BusinessCycle/IntegratedResults.lean) | Project-three forecast-based purposeful acceptance plus project-two and project-three contextual-regret witnesses for their actual default branches |
| [BusinessCycle.MasterResults](Praxeology/BusinessCycle/MasterResults.lean) | Parameterized master theorem synthesizing the eight causal links of Austrian Business Cycle Theory from credit expansion to purposeful entry, factor squeeze, malinvestment, defaults, and ex-post regret |
| [BusinessCycle.PhysicalSettlementWitness](Praxeology/BusinessCycle/PhysicalSettlementWitness.lean) | Physical settlement witness verifying that matched repayments clear obligations and return collateral independently of behavioral certificates |
| [FiniteEconomy.ProfileSchedule](Praxeology/FiniteEconomy/ProfileSchedule.lean) | Generic compiler from well-formed proposed profiles plus explicitly listed alternatives to a branching physical program with pre-state affordability, idle actions, unilateral branches, and an executed-history witness |
| [BusinessCycle.Firms](Praxeology/BusinessCycle/Firms.lean) | Organized-firm specialization of the single-project entrepreneurial cycle |
| [BusinessCycle.Grounded](Praxeology/BusinessCycle/Grounded.lean) | Finite two-agent ActionFrame witness for one entrepreneur's investment and contextual regret |
| [FiniteEconomy](Praxeology/FiniteEconomy.lean) | Finite histories, physical states, execution, markets, and supply-chain examples |
| [StateMonopoly](Praxeology/StateMonopoly.lean) | Territorial institutions, fiscal accounting, and political choice |
| [EconometricLimits](Praxeology/EconometricLimits.lean) | Observational equivalence and limits of causal identification |

The modules combine general deductive results with constructive finite witnesses and impossibility countermodels. Each theorem's mathematical premises explicitly bound its domain of application.

## Methodological scope, feasibility, and model witnesses

The formal library develops the core theorems of Austrian economics by combining generic deductive proofs, constructive finite models, and machine-checked boundary theorems:

- **Tripartite Separation of Feasibility, Deliberation, and Know-How:** The mathematical framework strictly separates physical transition laws and stock-flow conservation ([`Production.lean`](Praxeology/Production.lean)), subjective deliberation and purposeful choice ([`Action.lean`](Praxeology/Action.lean), [`Subjective.lean`](Praxeology/Subjective.lean)), and epistemic perception and causal execution over choice cells ([`EpistemicAbility.lean`](Praxeology/EpistemicAbility.lean)).
- **Constructive Model Witnesses:** Finite models prove the constructive satisfiability and non-vacuity of the formal structures. Concrete models include the finite workshop ([`FirmWitness.lean`](Praxeology/FirmWitness.lean)), the discrete ranked-use allocation frame ([`AllocationActionFrame.lean`](Praxeology/Marginal/AllocationActionFrame.lean)), and the multi-stage business cycle transmission witnesses ([`CreditLifecycleFrame.lean`](Praxeology/BusinessCycle/CreditLifecycleFrame.lean), [`MasterResults.lean`](Praxeology/BusinessCycle/MasterResults.lean)).
- **Deductive Bounds & Impossibility Theorems:** The formalization machine-checks foundational praxeological boundaries:
  - *Calculation Impossibility:* Proving the impossibility of rational economic calculation for higher-order capital goods without market price signals ([`Catallactics.lean`](Praxeology/Catallactics.lean)).
  - *Factor Complementarity:* Proving that isolated complementary factors have zero imputed marginal yield when required complementary inputs are absent ([`Marginal.lean`](Praxeology/Marginal.lean)).
  - *Econometric Identification Limits:* Establishing that external empirical observation of historical action traces cannot uniquely identify private subjective preference orderings or causal knowledge programs ([`EconometricLimits.lean`](Praxeology/EconometricLimits.lean)).
- **Deductive Precision:** Lean 4 ensures that every economic conclusion is strictly bounded by its explicit mathematical premises. Theorems explicitly articulate where a conclusion holds for all purposeful human actions as such, versus where it requires specific institutional settings (such as bilateral property titles, monetary calculation, or unbacked credit expansion). Detailed premise mappings for all headline claims are maintained in [`spec/claims_and_assumptions.md`](spec/claims_and_assumptions.md).

## Documentation and repository organization

- [`natural_language/`](natural_language/README.md) contains fourteen expository chapters presenting the mathematical treatise on praxeology, synchronized with the Lean 4 formalization.
- [`spec/`](spec/README.md) organizes the mathematical specifications and their Lean correspondence by topic.
- [`spec/claims_and_assumptions.md`](spec/claims_and_assumptions.md) records the scope and assumptions of headline claims.
- [`Praxeology/`](Praxeology/) contains the formal library; [`Praxeology.lean`](Praxeology.lean) is its root module.
- [`critiques/`](critiques/) contains methodological essays and comparisons with alternative economic formulations.
- [`scripts/`](scripts/) contains documentation, link, and axiomatic-floor checks.

The Lean declarations are authoritative for exact formal hypotheses and conclusions. Prose specifications track the formal theorems; economic fidelity remains a separate interpretive question.

## Building and verification

The toolchain and Mathlib revision are pinned in [`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml), and [`lake-manifest.json`](lake-manifest.json). The build commands use [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/). With Lean's toolchain manager installed, run from the repository root:

```bash
lake exe cache get
lake build
python3 scripts/update_theorem_links.py --check
python3 scripts/update_natural_language_links.py --check
python3 scripts/fix_markdown_math.py --check
python3 scripts/check_markdown_math.py
python3 scripts/audit_adhoc_premises.py --check
python3 scripts/audit_axiomatic_floor.py
python3 scripts/audit_constructive_axioms.py --by-axiom --limit 20
```

The build checks formal declarations and configured linters. The declaration-link checker, Markdown math checks, and constructive axiom report are verification tools. The source-pattern premise and axiomatic-floor scripts are advisory only: a textual pattern cannot decide semantic validity or fidelity. The constructive audit's [`--by-axiom`](scripts/audit_constructive_axioms.py) option reports transitive dependencies; `--strict` is for projects that specifically require an axiom-free result, not the default validity criterion. No current finite business-cycle calibration should be read as a historical case study.

## References

1. **Cachanosky, Nicolás, & Padilla, Alexandre.** (2016). "A Mathematical Version of Garrison's Model". *The Quarterly Journal of Austrian Economics*, 19(3), 225–247.
2. **Coase, Ronald H.** (1937). "The Nature of the Firm". *Economica*, 4(16), 386–405.
3. **Hayek, Friedrich A.** (1945). "The Use of Knowledge in Society". *The American Economic Review*, 35(4), 519–530.
4. **Hülsmann, Jörg Guido.** (1998). "Toward a General Theory of Error Cycles". *The Quarterly Journal of Austrian Economics*, 1(4), 1–23.
5. **Hülsmann, Jörg Guido.** (2002). "A Theory of Interest". *The Quarterly Journal of Austrian Economics*, 5(4), 77–110.
6. **Hülsmann, Jörg Guido.** (2003). "Facts and Counterfactuals in Economic Law". *Journal of Libertarian Studies*, 17(1), 57–102.
7. **Komendarczyk, Rafał, Block, Walter E., Levendis, John, & Tipler, Frank J.** (2026). "A Formalization of Austrian Economics: Praxeological Foundations: The Base System and Its Derived Theorems". *arXiv:2606.18292v3 [econ.TH]*. Code repository: [rafkom72/praxeology-lean](https://github.com/rafkom72/praxeology-lean).
8. **Lawson, Gary S.** (2022). "The Epistemology of Second Best". *Texas Law Review*, 100(4), 747–785.
9. **Megger, Dawid.** (2024). "Demonstrated preference in the Austrian economic analysis". *Philosophical Problems in Science (Zagadnienia Filozoficzne w Nauce)*, 76, 391–423.
10. **Menger, Carl.** (1871). *Grundsätze der Volkswirtschaftslehre* (*Principles of Economics*). Wilhelm Braumüller.
11. **Menger, Carl.** (1892). "On the Origin of Money". *The Economic Journal*, 2(6), 239–255.
12. **Mises, Ludwig von.** (1920). "Economic Calculation in the Socialist Commonwealth" ("Die Wirtschaftsrechnung im sozialistischen Gemeinwesen"). *Archiv für Sozialwissenschaft und Sozialpolitik*, 47, 86–121.
13. **Mises, Ludwig von.** (1929). *Critique of Interventionism* (*Kritik des Interventionismus*). Gustav Fischer.
14. **Mises, Ludwig von.** (1949). *Human Action: A Treatise on Economics*. Yale University Press.
15. **Rothbard, Murray N.** (1956). "Toward a Reconstruction of Utility and Welfare Economics". In M. Sennholz (Ed.), *On Freedom and Free Enterprise: Essays in Honor of Ludwig von Mises* (pp. 224–262). D. Van Nostrand.
16. **Rothbard, Murray N.** (1962). *Man, Economy, and State: A Treatise on Economic Principles* (with *Power and Market*). D. Van Nostrand.
17. **van Berkel, Kees, & Lyon, Tim.** (2021). "The Varieties of Ought-implies-Can and Deontic STIT Logic". In *Deontic Logic and Normative Systems: 15th International Conference, DEON 2020/2021* (pp. 57–76). College Publications. Also available as *arXiv:2604.00967*.
18. **Vienneau, Robert.** (2026). "The Production of Commodities and the Structure of Production". *MPRA Paper No. 128751*, University Library of Munich.
