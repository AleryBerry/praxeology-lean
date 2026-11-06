# Comparison with Komendarczyk et al.'s Lean companion

This note compares the current repository with
[`rafkom72/praxeology-lean`](https://github.com/rafkom72/praxeology-lean),
the Lean 4 companion to Komendarczyk, Block, Levendis, and Tipler's
*An Axiomatization of Praxeology — Foundations*. It is a comparison of
formal scope and representation, not a claim that either codebase is more
faithful to Austrian economics. The external repository's description and
README were checked on 5 November 2026.

## 1. Formal design

The [Komendarczyk et al. companion](https://github.com/rafkom72/praxeology-lean)
presents the paper's praxeological signature as a Lean class and supplies
concrete Crusoe models for its stated axioms. Its README describes a finite
three-period Crusoe instance for the action core, an infinite-time witness for
the full base theory, a production hierarchy, and a diminishing-marginal-
utility enrichment with a water/fish witness. It says the single Lean file
imports no Mathlib and uses Lean 4 core only. These are claims made by that
repository's README; this note does not audit its proofs or axiom dependencies.

This repository instead develops a larger, modular `ActionFrame` interface
with explicit finite action menus, resource constraints, endowments, inventory
transitions, preferences, and enacted actions. Its modules add conditional
results about exchange, monetary coordination, credit events, firms, business
cycle mechanisms, institutional classifications, and econometric
non-identifiability. Concrete witnesses exist for selected submodels, including
a workshop, a single-entrepreneur cycle, and a five-project scheduled physical
program with an ActionFrame adapter. The latter carries market results through
its branches and still omits early production, behaviorally derived choices,
market recalculation after deviations, and integrated default adjudication.

These are different formal targets. A class that packages a paper's axioms and
a model satisfying that class is not the same representation as an
ActionFrame-based physical economy. A larger collection of modules does not by
itself mean a stronger proof of the base theory or greater economic fidelity.

## 2. DMU and its assumptions

The external companion describes DMU as a theorem under a specific
production-enriched order structure and corrected top-segment axiom, and
includes a two-good witness for its multi-good formulation. See its
[`Praxeology.lean`](https://github.com/rafkom72/praxeology-lean/blob/main/Praxeology.lean)
and README for the exact definitions and hypotheses.

The older DMU interface in this repository is explicitly marked legacy. Its
allocation menu included a premise saying the designated top prefix dominates
every feasible alternative, so the old choice-to-prefix result should not be
presented as deriving that optimality from purposeful action alone. The newer
[`AllocationChoice.lean`](../Praxeology/Marginal/AllocationChoice.lean)
separates homogeneous-use technology from local ordinal addition,
replacement, and transitivity laws. It derives that an undominated purposeful
choice selects the ranked prefix when the stocked context supplies exact
requirements and a complete feasible realization map. The context has a
concrete two-agent ActionFrame instantiation with the same three-use technology
and ranking at stocks one and two; the respective purposeful allocations are
`{0}` and `{0, 1}`. The module also proves the two-unit-quantum capacity table
for stocks zero through four and countermodels for an incomplete menu and a
missing replacement law. These results have specific local hypotheses and do
not establish equivalence with the companion's production-enriched order
structure or its corrected top-segment axiom.

The two DMU developments should be compared by their formal definitions,
axioms, theorem hypotheses, and instantiated models. The shared phrase
“diminishing marginal utility” is not sufficient to establish that the
formalized conclusions are equivalent.

## 3. Library imports and axioms

This project uses Mathlib for finite sets, arithmetic, order theory, and proof
tactics. Mathlib is a library dependency, not an additional axiom. The relevant
soundness question is whether Lean's kernel checks the proof and which axioms
the declaration depends on transitively. This repository accepts the standard
Lean dependencies `propext`, `Classical.choice`, and `Quot.sound` where they
occur; it rejects custom axioms and unfinished proofs.

The other repository's no-Mathlib design is a useful self-contained
engineering choice. It does not follow merely from that fact that all of its
proofs avoid choice or every other axiom; that requires an axiom-dependency
check of its declarations. Conversely, using Mathlib does not make a proof
unsound. Library choice and foundational axioms are separate questions.

## 4. Current comparison boundaries

| Topic | Komendarczyk et al. companion | This repository |
|---|---|---|
| Base formalization | Paper-oriented signature and axiom system, with Crusoe models | Modular ActionFrame laws and selected instances |
| DMU | Production-enriched order hierarchy, corrected top-segment condition, theorem deriving reduced marginal end, and a two-good water/fish witness, as described by its README | Legacy global-optimum interface is labeled; new local ordinal laws derive ranked-prefix choice, with an ActionFrame witness at stocks one and two, two-unit capacity tables, and boundary countermodels |
| Physical exchange and monetary institutions | README identifies these as future enrichments | Separate exchange, money, and credit modules with theorem-specific premises and witnesses |
| Business-cycle scope | Not listed in the external repository's stated coverage | Conditional cohort mechanisms and a scheduled five-project physical ActionFrame program; early production, behaviorally derived saving/investment, off-path market recalculation, and integrated default adjudication remain open |
| Dependencies | Lean 4 core only, per its README | Lean 4 plus Mathlib |

This table is intentionally limited to repository descriptions and checked
formal interfaces. It does not assess the correctness of the economic
interpretations or substitute for a theorem-by-theorem review.

## References

- [Komendarczyk et al., paper and repository citation](https://arxiv.org/abs/2606.18292).
- [Lean companion repository](https://github.com/rafkom72/praxeology-lean).
- [Current claim and assumption register](claims_and_assumptions.md).
