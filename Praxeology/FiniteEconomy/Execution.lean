/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Tree
public import Praxeology.FiniteEconomy.Policy
public import Praxeology.Production

/-!
# Finite execution traces

A generated finite scenario supplies one certified inventory step for each
agent and parent-child edge. This module assembles those local certificates
into the `InventoryRun` objects used by general ActionFrame theorems.
-/

@[expose] public section

namespace Praxeology

/-- Executable evidence that an action profile assigns trades to their
proposers or acceptors. The certificate is data so its cases can select an
inventory-step constructor without classical choice. -/
inductive ActionFrame.WellFormedAction (W : ActionFrame) [BilateralExchangeFrame W]
    (i : W.Agent) : W.Action → Type where
  | nontrade {α : W.Action} (h_nontrade : ¬ W.IsTradeAction α) :
      W.WellFormedAction i α
  | offer {α : W.Action} (j : W.Agent) (qA : ℕ) (mA : W.Means)
      (qB : ℕ) (mB : W.Means) (h_agents : i ≠ j)
      (h_action : α = W.Offer i j qA mA qB mB) : W.WellFormedAction i α
  | accept {α : W.Action} (j : W.Agent) (qA : ℕ) (mA : W.Means)
      (qB : ℕ) (mB : W.Means) (h_agents : i ≠ j)
      (h_action : α = W.Accept i j qA mA qB mB) : W.WellFormedAction i α

def ActionFrame.WellFormedEnactedAction (W : ActionFrame) [BilateralExchangeFrame W]
    (i : W.Agent) (t : W.Moment) (h : W.History) : Type :=
  W.WellFormedAction i (W.enacted i t h)

def InventoryStep.ofWellFormedAction
    {W : ActionFrame} [BilateralExchangeFrame W] {i : W.Agent}
    {h : W.History} {t t' : W.Moment} {α : W.Action}
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_exec : W.enacted i t h = α) (h_well : W.WellFormedAction i α) :
    InventoryStep W i h t t' := by
  cases h_well with
  | nontrade h_nontrade => exact .production α h_exec h_nontrade h_next
  | offer j qA mA qB mB h_agents h_action =>
      have h_offer := h_exec.trans h_action
      by_cases h_accept : W.enacted j t h = W.Accept j i qA mA qB mB
      · exact .matchedOffer j qA mA qB mB h_agents h_offer h_accept h_next
      · exact .unmatchedOffer j qA mA qB mB h_offer h_accept h_next
  | accept j qA mA qB mB h_agents h_action =>
      have h_accept := h_exec.trans h_action
      by_cases h_offer : W.enacted j t h = W.Offer j i qA mA qB mB
      · exact .matchedAccept j qA mA qB mB h_agents.symm h_accept h_offer h_next
      · exact .unmatchedAccept j qA mA qB mB h_accept h_offer h_next

/-- A well-formed enacted action determines its production, matched-trade, or
unmatched-trade inventory step. -/
theorem InventoryStep.exists_of_wellFormedAction
    {W : ActionFrame} [BilateralExchangeFrame W] {i : W.Agent}
    {h : W.History} {t t' : W.Moment} {α : W.Action}
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_exec : W.enacted i t h = α)
    (h_well : W.WellFormedAction i α) :
    Nonempty (InventoryStep W i h t t') :=
  ⟨InventoryStep.ofWellFormedAction h_next h_exec h_well⟩

/-- Classify a well-formed enacted action without enumerating the full action
type or invoking classical choice. -/
theorem InventoryStep.exists_of_wellFormedEnactedAction
    {W : ActionFrame} [BilateralExchangeFrame W] {i : W.Agent}
    {h : W.History} {t t' : W.Moment}
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_well : W.WellFormedEnactedAction i t h) :
    Nonempty (InventoryStep W i h t t') :=
  ⟨InventoryStep.ofWellFormedAction h_next rfl h_well⟩

def InventoryStep.ofWellFormedEnactedAction
    {W : ActionFrame} [BilateralExchangeFrame W] {i : W.Agent}
    {h : W.History} {t t' : W.Moment}
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_well : W.WellFormedEnactedAction i t h) : InventoryStep W i h t t' :=
  InventoryStep.ofWellFormedAction h_next rfl h_well

/-- A finite-tree execution certificate over an existing ActionFrame. The
frame remains the source of actions, endowments, ends, preferences, and
doxastic laws; this record supplies only the finite temporal presentation
and its enacted inventory steps. -/
structure FiniteInventoryProgram (W : ActionFrame) [BilateralExchangeFrame W]
    (T : FiniteTreeSpec) where
  presentation : FiniteTreeSpec.FiniteTreePresentation W T
  /-- A precomputed ancestry matrix reused by profile and history queries. -/
  treeIndex : FiniteTreeSpec.FiniteTreeIndex T
  history : T.History
  initialEndowment : W.Agent → W.Means → ℕ
  initialEndowment_matches : ∀ (i : W.Agent) (m : W.Means),
    W.omega i (presentation.moment 0) (presentation.history history) m =
      initialEndowment i m
  actionProfile : W.Agent → T.Node → T.History → W.Action
  actionProfile_matches : ∀ (i : W.Agent) (t : T.Node) (h : T.History),
    T.MemHist t h →
    W.enacted i (presentation.moment t) (presentation.history h) = actionProfile i t h
  actionProfile_wellFormed : ∀ (i : W.Agent) (t : T.Node) (h : T.History),
    T.MemHist t h → W.WellFormedAction i (actionProfile i t h)

namespace FiniteInventoryProgram

/-- Compile one parent-child edge from the ActionFrame's enacted profile.
The compiler derives temporal adjacency from the parent array and classifies
the event as production, matched exchange, or unmatched exchange. -/
def step {W : ActionFrame} [BilateralExchangeFrame W] {T : FiniteTreeSpec}
    (P : FiniteInventoryProgram W T) (i : W.Agent) {u v : T.Node}
    (huv : T.parent v = u) (hv : v ≠ 0) (hmem : T.MemHist v P.history) :
    InventoryStep W i (P.presentation.history P.history)
      (P.presentation.moment u) (P.presentation.moment v) := by
  have htree := (T.isNextMoment_iff_parent u v P.history).2 ⟨hmem, hv, huv⟩
  have hnext := P.presentation.map_next_moment htree
  have hpu : T.Ancestor u v := by
    rw [← huv]
    exact T.ancestor_of_parent hv (T.ancestor_refl _)
  have humem : T.MemHist u P.history := T.ancestor_trans hpu hmem
  exact InventoryStep.ofWellFormedAction hnext
    (P.actionProfile_matches i u P.history humem)
    (P.actionProfile_wellFormed i u P.history humem)

/-- Compile the certified edges from the root to any node on the selected
history into a physical inventory run. The recursion is on the node index,
which strictly decreases along parent pointers. -/
def runTo {W : ActionFrame} [BilateralExchangeFrame W] {T : FiniteTreeSpec}
    (P : FiniteInventoryProgram W T) (i : W.Agent) (t : T.Node)
    (ht : T.MemHist t P.history) :
    InventoryRun W i (P.presentation.history P.history)
      (P.presentation.moment 0) (P.presentation.moment t) := by
  by_cases ht0 : t = 0
  · subst t
    exact InventoryRun.done _
  · let p := T.parent t
    have hpu : T.Ancestor p t :=
      T.ancestor_of_parent ht0 (T.ancestor_refl p)
    have hpmem : T.MemHist p P.history := T.ancestor_trans hpu ht
    have edge := P.step i (u := p) (v := t) rfl ht0 ht
    have edgeRun : InventoryRun W i (P.presentation.history P.history)
        (P.presentation.moment p) (P.presentation.moment t) :=
      .step (by simpa [p] using edge) (.done _)
    exact (runTo P i p hpmem).append edgeRun
termination_by t.val
decreasing_by
  exact T.parent_decreases t ht0

end FiniteInventoryProgram

namespace FiniteInventoryProgram

/-- Read a selected history's incidence through the cached matrix carried by
the compiled program. -/
def cachedMemHist {W : ActionFrame} [BilateralExchangeFrame W] {T : FiniteTreeSpec}
    (P : FiniteInventoryProgram W T) (t : T.Node) : Prop :=
  P.treeIndex.MemHist t P.history

theorem cachedMemHist_iff {W : ActionFrame} [BilateralExchangeFrame W] {T : FiniteTreeSpec}
    (P : FiniteInventoryProgram W T) (t : T.Node) :
    P.cachedMemHist t ↔ T.MemHist t P.history :=
  P.treeIndex.memHist_iff t P.history

/-- Run to any node certified by the compiled history index. -/
def runToCached {W : ActionFrame} [BilateralExchangeFrame W] {T : FiniteTreeSpec}
    (P : FiniteInventoryProgram W T) (i : W.Agent) (t : T.Node)
    (ht : P.cachedMemHist t) :
    InventoryRun W i (P.presentation.history P.history)
      (P.presentation.moment 0) (P.presentation.moment t) :=
  P.runTo i t (P.cachedMemHist_iff t |>.1 ht)

end FiniteInventoryProgram

namespace InventoryRun

/-- Forward-simulate an endowment from a root ledger and the cumulative
effective inputs and outputs of a compiled inventory run. The natural-number
subtraction is safe because `inventory_balance` certifies that the run's total
uses are funded. -/
def simulateEndowment {W : ActionFrame} [BilateralExchangeFrame W]
    {i : W.Agent} {h : W.History} {t u : W.Moment}
    (run : InventoryRun W i h t u)
    (initial : W.Means → ℕ) : W.Means → ℕ :=
  fun m => initial m + run.totalYield m - run.totalUse m

/-- The forward-simulated stock equals the ActionFrame's observed stock when
the root ledger is read from that same frame. -/
theorem simulateEndowment_eq_omega {W : ActionFrame} [BilateralExchangeFrame W]
    {i : W.Agent} {h : W.History} {t u : W.Moment}
    (run : InventoryRun W i h t u) :
    run.simulateEndowment (fun m => W.omega i t h m) =
      fun m => W.omega i u h m := by
  funext m
  have hbalance := run.inventory_balance m
  simp only [simulateEndowment]
  omega

end InventoryRun

/-- Interpretation of compiler ends inside an existing ActionFrame. Its
bundle encoder agrees with the frame's primitive `BundleEnd`. -/
structure EconomyEndInterpretation (W : ActionFrame) (History PrimitiveEnd : Type) where
  encode : PrimitiveEnd → W.Ends
  bundlePrimitive : (W.Means → ℕ) → PrimitiveEnd
  encode_bundle : ∀ b, encode (bundlePrimitive b) = W.BundleEnd b

namespace EconomyEndInterpretation

/-- Convert a primitive end or plan into the frame's existing abstract end
type after selecting the relevant history. -/
def toActionFrameEnd {W : ActionFrame} {History PrimitiveEnd : Type}
    (E : EconomyEndInterpretation W History PrimitiveEnd) (h : History)
    (e : EconomyEnd History PrimitiveEnd) : W.Ends :=
  E.encode (e.evaluate h)

/-- A state-contingent bundle plan is encoded as a primitive bundle only after
the history has been selected. -/
def bundlePlan {W : ActionFrame} {History PrimitiveEnd : Type}
    (E : EconomyEndInterpretation W History PrimitiveEnd)
    (plan : History → W.Means → ℕ) : EconomyEnd History PrimitiveEnd :=
  .plan fun h => E.bundlePrimitive (plan h)

/-- Normalize a bundle plan to a primitive bundle only when it is constant on
the finite support of plausible histories. This is an encoding operation; the
ActionFrame continues to supply preference and doxastic laws. -/
def normalizedBundlePlan {W : ActionFrame} {PrimitiveEnd : Type}
    [DecidableEq W.History] [DecidableEq PrimitiveEnd]
    (E : EconomyEndInterpretation W W.History PrimitiveEnd)
    (support : Finset W.History) (representative : Option W.History)
    (plan : W.History → W.Means → ℕ) :
    EconomyEnd W.History PrimitiveEnd :=
  normalizePlan support representative (fun h => E.bundlePrimitive (plan h))

theorem toActionFrameEnd_bundlePlan {W : ActionFrame} {History PrimitiveEnd : Type}
    (E : EconomyEndInterpretation W History PrimitiveEnd)
    (plan : History → W.Means → ℕ) (h : History) :
    E.toActionFrameEnd h (E.bundlePlan plan) = W.BundleEnd (plan h) := by
  simp [toActionFrameEnd, bundlePlan, EconomyEnd.evaluate, E.encode_bundle]

/-- Evaluating a normalized contingent bundle plan at any supported history
recovers the same primitive ActionFrame bundle end. -/
theorem toActionFrameEnd_normalizedBundlePlan
    {W : ActionFrame} {PrimitiveEnd : Type}
    [DecidableEq W.History] [DecidableEq PrimitiveEnd]
    (E : EconomyEndInterpretation W W.History PrimitiveEnd)
    (support : Finset W.History) (representative : Option W.History)
    (plan : W.History → W.Means → ℕ)
    (h : W.History) (hh : h ∈ support) :
    E.toActionFrameEnd h (E.normalizedBundlePlan support representative plan) =
      W.BundleEnd (plan h) := by
  rw [toActionFrameEnd]
  change E.encode (EconomyEnd.evaluate h
    (normalizePlan support representative (fun h' => E.bundlePrimitive (plan h')))) = _
  rw [normalizePlan_evaluate support representative _ hh]
  exact E.encode_bundle (plan h)

/-- Preference between contingent bundle plans is still driven directly by
the ActionFrame's subjective teleological dominance and bundle-preference
field at the realized history. -/
theorem contingent_bundle_plan_preference
    {W : ActionFrame} {PrimitiveEnd : Type}
    (E : EconomyEndInterpretation W W.History PrimitiveEnd)
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (b₁ b₂ : W.History → W.Means → ℕ)
    (hdom : W.SubjectiveTeleologicalDominates i t h (b₁ h) (b₂ h)) :
    W.Preference i t h
      (E.toActionFrameEnd h (E.bundlePlan b₁))
      (E.toActionFrameEnd h (E.bundlePlan b₂)) := by
  rw [E.toActionFrameEnd_bundlePlan, E.toActionFrameEnd_bundlePlan]
  exact W.teleological_bundle_dominance_induces_preference i t h
    (b₁ h) (b₂ h) hdom

/-- Normalizing a contingent plan on plausible-history support preserves the
same ActionFrame preference derivation at every supported history. -/
theorem normalized_bundle_plan_preference
    {W : ActionFrame} {PrimitiveEnd : Type}
    [DecidableEq W.History] [DecidableEq PrimitiveEnd]
    (E : EconomyEndInterpretation W W.History PrimitiveEnd)
    (support : Finset W.History) (representative : Option W.History)
    (i : W.Agent) (t : W.Moment)
    (h : W.History) (hh : h ∈ support)
    (b₁ b₂ : W.History → W.Means → ℕ)
    (hdom : W.SubjectiveTeleologicalDominates i t h (b₁ h) (b₂ h)) :
    W.Preference i t h
      (E.toActionFrameEnd h (E.normalizedBundlePlan support representative b₁))
      (E.toActionFrameEnd h (E.normalizedBundlePlan support representative b₂)) := by
  rw [E.toActionFrameEnd_normalizedBundlePlan support representative b₁ h hh,
    E.toActionFrameEnd_normalizedBundlePlan support representative b₂ h hh]
  exact W.teleological_bundle_dominance_induces_preference i t h
    (b₁ h) (b₂ h) hdom

/-- Finite plan normalization preserves the ActionFrame's primitive
subjective-teleological preference driver for bundle comparisons. -/
theorem bundle_plan_preference {W : ActionFrame} {PrimitiveEnd : Type}
    (E : EconomyEndInterpretation W W.History PrimitiveEnd)
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (b₁ b₂ : W.Means → ℕ)
    (hdom : W.SubjectiveTeleologicalDominates i t h b₁ b₂) :
    W.Preference i t h
      (E.toActionFrameEnd h (E.bundlePlan (fun _ => b₁)))
      (E.toActionFrameEnd h (E.bundlePlan (fun _ => b₂))) := by
  exact E.contingent_bundle_plan_preference i t h (fun _ => b₁)
    (fun _ => b₂) hdom

end EconomyEndInterpretation

/-- Declarative finite scenario data attached to a frame. The frame remains
the source of endowments and teleological preference laws; this record
provides finite tables and proves that they agree with the frame's enacted
actions and valued ends. -/
structure FiniteEconomySpec (W : ActionFrame) [BilateralExchangeFrame W]
    (T : FiniteTreeSpec) where
  presentation : FiniteTreeSpec.FiniteTreePresentation W T
  initialEndowment : W.Agent → W.Means → ℕ
  initialEndowment_matches : ∀ (i : W.Agent) (m : W.Means) (h : T.History),
    W.omega i (presentation.moment 0) (presentation.history h) m = initialEndowment i m
  actionProfile : W.Agent → T.Node → T.History → W.Action
  actionProfile_matches : ∀ (i : W.Agent) (t : T.Node) (h : T.History),
    T.MemHist t h →
    W.enacted i (presentation.moment t) (presentation.history h) = actionProfile i t h
  actionProfile_wellFormed : ∀ (i : W.Agent) (t : T.Node) (h : T.History),
    T.MemHist t h → W.WellFormedAction i (actionProfile i t h)
  valuedEndProfile : W.Agent → T.Node → T.History → W.Ends → Prop
  valuedEndProfile_matches : ∀ (i : W.Agent) (t : T.Node) (h : T.History)
      (w : W.Ends), T.MemHist t h →
    (W.ValuedEnd i (presentation.moment t) (presentation.history h) w ↔
      valuedEndProfile i t h w)

namespace FiniteEconomySpec

/-- Select one finite history and expose its validated profile to the generic
inventory-run compiler. Preference and end semantics continue to come from
the underlying `ActionFrame`. -/
def inventoryProgram {W : ActionFrame} [BilateralExchangeFrame W]
    {T : FiniteTreeSpec} (S : FiniteEconomySpec W T) (h : T.History) :
    FiniteInventoryProgram W T :=
  { presentation := S.presentation
    treeIndex := T.compileIndex
    history := h
    initialEndowment := S.initialEndowment
    initialEndowment_matches := fun i m => S.initialEndowment_matches i m h
    actionProfile := S.actionProfile
    actionProfile_matches := S.actionProfile_matches
    actionProfile_wellFormed := S.actionProfile_wellFormed }

end FiniteEconomySpec

namespace FiniteInventoryProgram

/-- Compute the balance at a node from the selected history's root stock and
the compiled production/trade transitions along the parent path. -/
noncomputable def predictedEndowment {W : ActionFrame} [BilateralExchangeFrame W]
    {T : FiniteTreeSpec} (P : FiniteInventoryProgram W T) (i : W.Agent)
    (t : T.Node) (ht : T.MemHist t P.history) : W.Means → ℕ :=
  (P.runTo i t ht).simulateEndowment
    (P.initialEndowment i)

/-- The compiled forward simulation agrees with the frame's observed stock
at every node. -/
theorem predictedEndowment_eq_omega {W : ActionFrame} [BilateralExchangeFrame W]
    {T : FiniteTreeSpec} (P : FiniteInventoryProgram W T) (i : W.Agent)
    (t : T.Node) (ht : T.MemHist t P.history) :
    P.predictedEndowment i t ht =
      fun m => W.omega i (P.presentation.moment t)
        (P.presentation.history P.history) m := by
  funext m
  change P.initialEndowment i m + (P.runTo i t ht).totalYield m -
      (P.runTo i t ht).totalUse m = _
  rw [← P.initialEndowment_matches i m]
  exact congrFun (P.runTo i t ht).simulateEndowment_eq_omega m

end FiniteInventoryProgram

namespace FiniteEconomySpec

theorem initial_endowment_at_root {W : ActionFrame} [BilateralExchangeFrame W]
    {T : FiniteTreeSpec} (S : FiniteEconomySpec W T) (i : W.Agent) (m : W.Means)
    (h : T.History) :
    W.omega i (S.presentation.moment 0) (S.presentation.history h) m =
      S.initialEndowment i m :=
  S.initialEndowment_matches i m h

/-- The compiled transition trace reproduces stocks from the declared root
endowment and the frame's enacted production/trade transitions. -/
theorem predictedEndowment_eq_declared_profile
    {W : ActionFrame} [BilateralExchangeFrame W] {T : FiniteTreeSpec}
    (S : FiniteEconomySpec W T) (h : T.History) (i : W.Agent) (t : T.Node)
    (ht : T.MemHist t h) (m : W.Means) :
    (S.inventoryProgram h).predictedEndowment i t ht m =
      W.omega i (S.presentation.moment t) (S.presentation.history h) m := by
  simpa [inventoryProgram] using
    congrFun ((S.inventoryProgram h).predictedEndowment_eq_omega i t ht) m

theorem valued_ends_remain_frame_valued
    {W : ActionFrame} [BilateralExchangeFrame W] {T : FiniteTreeSpec}
    (S : FiniteEconomySpec W T) (i : W.Agent) (t : T.Node) (h : T.History)
    (w : W.Ends) (ht : T.MemHist t h) :
    W.ValuedEnd i (S.presentation.moment t) (S.presentation.history h) w ↔
      S.valuedEndProfile i t h w :=
  by
    exact (S.valuedEndProfile_matches i t h w) ht

end FiniteEconomySpec

end Praxeology

end
