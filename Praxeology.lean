module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Counterfactuals
public import Praxeology.Marginal
public import Praxeology.Catallactics
public import Praxeology.FirmBoundary
public import Praxeology.BusinessCycle

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Praxeology — The 8 Grand Theorems of Formalized Austrian Praxeology

A fully verified, constructive Lean 4 formalization of human action,
subjective value, market exchange, socialist calculation, firm boundaries, and business cycle dynamics:

- **Theorem 0.1: Model-Theoretic Consistency & Non-Vacuity of the Praxeological Frame** (`Praxeology.Frame`)
  Spatiotemporal branching time, backward linearity, and Bourbaki-Witt marketability consistency (`ModelM0`).

- **Theorem 1: The Praxeological Action Axiom & Revealed Teleology** (`Praxeology.Action`)
  Purposeful action (`UnifiedPurposefulAct`), revealed preference, set-valued opportunity cost (`OCSet`),
  and performative self-consistency without neoclassical patches.
  *Theorems 1.1–1.7*.

- **Theorem 2: The Law of Ordinal Diminishing Marginal Utility & Mengerian Marginal Sacrifice** (`Praxeology.Marginal`)
  Purely ordinal diminishing marginal utility and least-urgent end economizing without cardinal utilities.
  *Theorems 2.1–2.2*.

- **Theorem 3: Universal Positive Time Preference & Originary Interest** (`Praxeology.Marginal`)
  Avenue B action horizon impossibility under negative time preference, demonstrated time preference,
  and strictly positive originary interest ι > 0.
  *Theorems 3.1–3.5*.

- **Theorem 4: Catallactic Bilateral Exchange & Bourbaki-Witt Money Emergence** (`Praxeology.Catallactics`)
  Double inequality of exchange, Megger's highwayman separation of coercion vs. exchange,
  fixed-point universal money emergence, discrete marginal pairs pricing bounds, and praxeological Gresham's law.
  *Theorems 4.1–4.5*.

- **Theorem 5: The Mises-Hayek Economic Calculation Problem (ECP)** (`Praxeology.Catallactics`)
  Automorphism non-invariance over physical antichains, semantic incommensurability barrier vs. algorithmic complexity.
  *Theorems 5.1–5.2*.

- **Theorem 6: Counterfactual Action, Speculative Regret, & Epistemic Second-Best** (`Praxeology.Counterfactuals`)
  Ex-ante/ex-post divergence, cross-branch regret, mandatory regret in heterodoxastic speculation,
  Lawson's epistemic second-best non-monotonicity, and dynamic interventionist regulatory cascades.
  *Theorems 6.1–6.6*.

- **Theorem 7: The Coasean-Misesian Boundary of the Firm & Signal Quantization Attenuation** (`Praxeology.FirmBoundary`)
  Catallactic price-box indeterminacy cones, multi-stage signal attenuation, master coalescence inequality,
  the Coasean-Misesian firm boundary tradeoff, and credit-induced artificial conglomeration (spontaneous cartelization).
  *Theorems 7.1–7.8*.

- **Theorem 8: The Austrian Business Cycle Theory (ABCT) & Synchronized Cluster of Errors** (`Praxeology.BusinessCycle`)
  Fiduciary signal opacity, artificial interest rate distortion, endogenous IC1 factor tug-of-war starvation,
  Hülsmann-Rothbard synchronized cluster of errors, midstream factor bailout impossibility, Cantillon bailout regret cascade,
  and kernel-checked non-vacuity witness.
  *Theorems 8.1–8.8*.
-/
