import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedReferenceCoefficients
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPieceCharts
import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentOpenPointValues
import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected

/-! # Actual intrinsic coefficients on connected smooth component opens
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Every actual support homology class has one rational coefficient against the specified intrinsic component class throughout an actual isolated affine smooth generic component open.
Source: properCycle_connected_reference_coefficients; properCycle_intrinsic_support_component_open_point_ne_zero; ComplexPoint.connectedSpace.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_component_open_coefficients
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) (d : ℕ)
    (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (d : ℕ))
    (W : (properCycle_component_over X ξ).left.Opens) (hW : IsAffineOpen W)
    (hgW : genericPoint (properCycle_component_over X ξ).left ∈ W)
    [SmoothOfRelativeDimension d (openScheme (properCycle_component_over X ξ) W).hom]
    (hother : ∀ z : (properCycle_component_over X ξ).left, z ∈ W →
      ∀ η ∈ γ.support, η ≠ ξ →
        (properCycle_component_over_inclusion X ξ).left z ∉ closure ({η} : Set X.left))
    (c : Homology ℚ (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d)) :
    ∃ q : ℚ, ∀ y : ComplexPoint (openScheme (properCycle_component_over X ξ) W),
      localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d) c
        (properCycle_component_open_support_map X γ ξ hξ W y) =
      q • localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d)
        (properCycle_intrinsic_component_on_support X γ ξ hξ d hdim)
        (properCycle_component_open_support_map X γ ξ hξ W y) := by
  let V := properCycle_component_over X ξ
  let Y := openScheme V W
  letI : Nonempty W := ⟨⟨genericPoint V.left, hgW⟩⟩
  letI : Nonempty Y.left := inferInstanceAs (Nonempty W.toScheme)
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion W.ι
  letI : IsAffine Y.left := hW
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth d Y.hom
  letI : QuasiCompact Y.hom := inferInstance
  letI : IsSeparated Y.hom := inferInstance
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  letI := AlgebraicGeometry.ComplexPoint.connectedSpace Y
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  let T := TopCat.of (a3b4_cycleSupport X.hom γ)
  let f := properCycle_component_open_support_map X γ ξ hξ W
  have hf := properCycle_component_open_support_map_isOpenEmbedding X γ ξ hξ W hother
  exact properCycle_connected_reference_coefficients T (TopCat.of (ComplexPoint Y)) f d
    (properCycle_open_piece_chart (E := Fin d → ℂ) T (TopCat.of (ComplexPoint Y)) f hf)
    (properCycle_intrinsic_component_on_support X γ ξ hξ d hdim)
    (properCycle_intrinsic_support_component_open_point_ne_zero X γ ξ hξ d hdim W hW hother) c

end HodgeLean.Foundations.QuotientDuality
