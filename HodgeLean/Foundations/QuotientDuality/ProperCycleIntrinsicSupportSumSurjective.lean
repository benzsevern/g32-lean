import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentOpenCoefficients
import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentOpenUnion
import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentBoundaryCover
import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentBoundaryDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleClosedSupportBoundaryProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportSumInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionPointDetection

/-! # Spanning by specified intrinsic classes on actual pure cycle supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Specified intrinsic component classes span ordinary middle homology of the literal pure cycle support, using actual isolated smooth generic opens and the smaller algebraic boundary.
Source: properCycle_intrinsic_component_open_coefficients; properCycle_component_open_boundary_dimension; properCycle_closed_support_boundary_projection; properCycle_union_point_detection.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_sum_surjective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k) :
    Function.Surjective (properCycle_intrinsic_support_sum X k hdim γ hc) := by
  classical
  choose W hW hg hs hother using (fun ξ : γ.support =>
    properCycle_isolated_component_smooth_open X k hdim γ hc ξ.val ξ.property)
  let Y (ξ : γ.support) := openScheme (properCycle_component_over X ξ.val) (W ξ)
  letI (ξ : γ.support) : Nonempty (W ξ) := ⟨⟨genericPoint (properCycle_component_over X ξ.val).left, hg ξ⟩⟩
  letI (ξ : γ.support) : Nonempty (Y ξ).left := inferInstanceAs (Nonempty (W ξ).toScheme)
  letI (ξ : γ.support) : IsIntegral (Y ξ).left := isIntegral_of_isOpenImmersion (W ξ).ι
  letI (ξ : γ.support) : IsAffine (Y ξ).left := hW ξ
  letI (ξ : γ.support) : SmoothOfRelativeDimension k (Y ξ).hom := hs ξ
  letI (ξ : γ.support) : Smooth (Y ξ).hom := SmoothOfRelativeDimension.smooth k (Y ξ).hom
  letI (ξ : γ.support) : QuasiCompact (Y ξ).hom := inferInstance
  letI (ξ : γ.support) : IsSeparated (Y ξ).hom := inferInstance
  letI (ξ : γ.support) : QuasiSeparatedSpace (Y ξ).left := quasiSeparatedSpace_of_quasiSeparated (Y ξ).hom
  letI (ξ : γ.support) : ConnectedSpace (ComplexPoint (Y ξ)) :=
    AlgebraicGeometry.ComplexPoint.connectedSpace (Y ξ)
  letI (ξ : γ.support) : T2Space (ComplexPoint (Y ξ)) := f4_t2Space (Y ξ)
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  letI : CompactSpace (a3b4_an X.hom) := inferInstanceAs (CompactSpace (ComplexPoint X))
  let T := TopCat.of (a3b4_cycleSupport X.hom γ)
  letI : CompactSpace T := isCompact_iff_compactSpace.mp
    (a3b4a_classSupport_isClosed X.hom γ).isCompact
  let f (ξ : γ.support) := properCycle_component_open_support_map X γ ξ.val ξ.property (W ξ)
  have hf (ξ : γ.support) := properCycle_component_open_support_map_isOpenEmbedding
    X γ ξ.val ξ.property (W ξ) (hother ξ)
  let B := properCycle_component_open_boundary X γ W
  have hBdim : topologicalKrullDim B ≤ (k-1 : ℕ) :=
    properCycle_component_open_boundary_dimension X k hdim γ hc W hg
  obtain ⟨N, hN, hBN, hp⟩ := properCycle_closed_support_boundary_projection X
    (a3b4a_classAlgebraicSupport X.hom γ) B (k-1) hBdim
  have hproj : Function.Injective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := T) N) (2*k)).hom := by
    have hh := (hp (2*k-1) (by omega)).injective
    rw [show 2*k-1+1 = 2*k by omega] at hh
    exact hh
  have hcover (z : T) (hz : z ∉ N) : ∃ ξ : γ.support, z ∈ Set.range (f ξ) := by
    apply properCycle_component_open_boundary_cover X γ W z
    intro hb
    exact hz (hBN hb)
  intro c
  have hcoeff (ξ : γ.support) := properCycle_intrinsic_component_open_coefficients
    X γ ξ.val ξ.property k
    (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))
    (W ξ) (hW ξ) (hg ξ) (hother ξ) c
  choose v hv using hcoeff
  refine ⟨v, ?_⟩
  have hn : Module.finrank ℝ (Fin k → ℂ) = 2*k := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hz : c - properCycle_intrinsic_support_sum X k hdim γ hc v = 0 := by
    apply properCycle_union_point_detection (E := Fin k → ℂ) T
      (fun ξ => TopCat.of (ComplexPoint (Y ξ))) f hf
      (properCycle_component_open_union_injective X γ W hother) N hN hcover
      (2*k) hn hproj
    intro ξ y _
    change (relativeHomologyProjection ℚ (pointComplementPair (f ξ y)) (2*k)).hom
      (c - properCycle_intrinsic_support_sum X k hdim γ hc v) = 0
    rw [map_sub]
    have hsum := properCycle_intrinsic_support_sum_point_value X k hdim γ hc v ξ (f ξ y)
      (hother ξ (Point.map (openInclusion (properCycle_component_over X ξ.val) (W ξ)) y).underlying
        y.underlying.property)
    change localOrientation T (2*k) c (f ξ y) -
      localOrientation T (2*k) (properCycle_intrinsic_support_sum X k hdim γ hc v) (f ξ y) = 0
    rw [hsum, hv ξ y, sub_self]
  exact (sub_eq_zero.mp hz).symm

end HodgeLean.Foundations.QuotientDuality
