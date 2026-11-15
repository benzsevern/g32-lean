import HodgeLean.Adapters.NormalConeB4aGysinEvaluation
import HodgeLean.Adapters.NormalConeB4aGysinClass
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Ambient normal cycles and their evaluations

Holomorphic charts with a marked support point specify actual relative
homology classes in the ambient pair. Their pairings with normalized classes
are the original cycle multiplicities.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular

/-- A holomorphic normal chart with a marked point on the cycle support.
Source: the chart data in `a3b4_IsCycleClass`. -/
structure A3b4aGysinNormalChart {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) (c : ℕ) where
  tangentDim : ℕ
  chart : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
    ((Fin tangentDim → ℂ) × (Fin c → ℂ))
  support_eq : ∀ y ∈ chart.source, y ∈ a3b4_cycleSupport q γ ↔ (chart y).2 = 0
  point : ComplexPoint (Over.mk q)
  mem_source : point ∈ chart.source
  mem_support : point ∈ a3b4_cycleSupport q γ
  holomorphic : a3b4_IsHolChart q chart

/-- The ambient homology class of the marked complex normal disk.
Source: `flattenedSupportNormalClass` and functoriality of relative homology. -/
def a3b4a_gysin_normalCycle
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    {γ : AlgebraicCycle Z ℚ} {c : ℕ} (C : A3b4aGysinNormalChart q γ c) :
    RelativeHomology ℚ (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c) :=
  relativeHomologyMap ℚ (2 * c)
    (a3b4_neighborhoodPairMap
      (flattenedSupportNeighborhood (Fin C.tangentDim → ℂ) c C.chart C.point C.mem_source)
      (a3b4_cycleSupport q γ))
    (flattenedSupportNormalClass (Fin C.tangentDim → ℂ) c C.chart C.point C.mem_source
      (a3b4_cycleSupport q γ) C.support_eq ((C.support_eq C.point C.mem_source).mp C.mem_support))

/-- A normalized class pairs with an ambient normal cycle by the cycle's multiplicity. -/
theorem a3b4a_gysin_normalCycle_pairing
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    {γ : AlgebraicCycle Z ℚ} {c : ℕ} (C : A3b4aGysinNormalChart q γ c)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) :
    relativeCohomologyEquivDualHomology ℚ _ (2 * c) β (a3b4a_gysin_normalCycle C) =
      a3b4_multiplicity q γ C.point := by
  rw [a3b4a_gysin_normalCycle, ← relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  exact a3b4a_gysin_normal_evaluation_of_cycleClass q γ c β hβ C.tangentDim C.chart
    C.support_eq C.point C.mem_source C.mem_support C.holomorphic

/-- Normal cycles span the ambient relative homology in the lowest support degree. -/
theorem a3b4a_gysin_normalCycles_span
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ) :
    Submodule.span ℚ (Set.range (a3b4a_gysin_normalCycle (q := q) (γ := γ) (c := c))) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  refine le_antisymm ?_ bot_le
  intro φ hφ
  change φ = 0
  let δ := (relativeCohomologyEquivDualHomology ℚ _ (2 * c)).symm φ
  obtain ⟨θ, hθ⟩ := a3b4a_cycleClass_exists_of_codimension q γ c hc
  have hnorm : a3b4_IsCycleClass q γ c (δ + θ) := by
    apply a3b4a_gysin_cycleClass_of_normal_evaluation
    intro r e hS x hx hxS he
    let C : A3b4aGysinNormalChart q γ c := ⟨r, e, hS, x, hx, hxS, he⟩
    have hzero : φ (a3b4a_gysin_normalCycle C) = 0 :=
      (Submodule.mem_dualAnnihilator _).mp hφ _ (Submodule.subset_span ⟨C, rfl⟩)
    have hvalue : relativeCohomologyEquivDualHomology ℚ _ (2 * c) (δ + θ)
        (a3b4a_gysin_normalCycle C) = a3b4_multiplicity q γ x := by
      rw [map_add, LinearMap.add_apply]
      rw [show relativeCohomologyEquivDualHomology ℚ _ (2 * c) δ = φ from
        (relativeCohomologyEquivDualHomology ℚ _ (2 * c)).apply_symm_apply φ,
        hzero, zero_add]
      exact a3b4a_gysin_normalCycle_pairing C θ hθ
    simpa only [a3b4a_gysin_normalCycle,
      relativeCohomologyEquivDualHomology_relativeCohomologyMap] using hvalue
  have heq : δ + θ = θ :=
    a3b4a_cycleClass_unique_of_regularBoundary q γ c hc
      (a3b4a_classRegularBoundary q γ c) (a3b4a_classRegularBoundary_le q γ c)
      (a3b4a_classRegularBoundary_coheight q γ c hc)
      (a3b4a_classRegularBoundary_charts q γ c hc) _ _ hnorm hθ
  have hδ : δ = 0 := add_right_cancel (heq.trans (zero_add θ).symm)
  have h := congrArg (relativeCohomologyEquivDualHomology ℚ _ (2 * c)) hδ
  simpa only [δ, LinearEquiv.apply_symm_apply, map_zero] using h

/-- Every ambient relative class has a finite expansion in marked normal cycles. -/
theorem a3b4a_gysin_exists_normalCycle_expansion
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (z : RelativeHomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c)) :
    ∃ a : A3b4aGysinNormalChart q γ c →₀ ℚ,
      a.sum (fun C m => m • a3b4a_gysin_normalCycle C) = z := by
  apply Finsupp.mem_span_range_iff_exists_finsupp.mp
  rw [a3b4a_gysin_normalCycles_span q γ c hc]
  trivial

/-- Evaluation of a finite normal-cycle sum is the weighted sum of exact multiplicities. -/
theorem a3b4a_gysin_normalCycle_sum_pairing
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    {γ : AlgebraicCycle Z ℚ} {c : ℕ}
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) (a : A3b4aGysinNormalChart q γ c →₀ ℚ) :
    relativeCohomologyEquivDualHomology ℚ _ (2 * c) β
      (a.sum fun C m => m • a3b4a_gysin_normalCycle C) =
        a.sum (fun C m => m * a3b4_multiplicity q γ C.point) := by
  classical
  simp only [Finsupp.sum, map_sum, map_smul,
    a3b4a_gysin_normalCycle_pairing _ β hβ, smul_eq_mul]

/-- Pullback evaluation is computed by any normal-cycle expansion of the image generator. -/
theorem a3b4a_gysin_pullback_evaluation_of_expansion
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    {γ : AlgebraicCycle Z ℚ} {c : ℕ}
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) {P : TopPair.{0}}
    (f : P ⟶ TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ)
    (z : RelativeHomology ℚ P (2 * c)) (a : A3b4aGysinNormalChart q γ c →₀ ℚ)
    (ha : a.sum (fun C m => m • a3b4a_gysin_normalCycle C) =
      relativeHomologyMap ℚ (2 * c) f z) :
    relativeCohomologyEquivDualHomology ℚ P (2 * c)
      (relativeCohomologyMap ℚ (2 * c) f β) z =
        a.sum (fun C m => m * a3b4_multiplicity q γ C.point) := by
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap, ← ha]
  exact a3b4a_gysin_normalCycle_sum_pairing β hβ a

/-- Homologous finite normal-cycle expansions have the same weighted multiplicity. -/
theorem a3b4a_gysin_normalCycle_weights_eq
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (a b : A3b4aGysinNormalChart q γ c →₀ ℚ)
    (hab : a.sum (fun C m => m • a3b4a_gysin_normalCycle C) =
      b.sum (fun C m => m • a3b4a_gysin_normalCycle C)) :
    a.sum (fun C m => m * a3b4_multiplicity q γ C.point) =
      b.sum (fun C m => m * a3b4_multiplicity q γ C.point) := by
  obtain ⟨β, hβ⟩ := a3b4a_cycleClass_exists_of_codimension q γ c hc
  rw [← a3b4a_gysin_normalCycle_sum_pairing β hβ a, hab,
    a3b4a_gysin_normalCycle_sum_pairing β hβ b]

end HodgeLean.Adapters
