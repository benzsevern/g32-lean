import HodgeLean.Foundations.TubularEuler.AffineDifferentialInjectivityHelpers
import HodgeLean.Foundations.TubularEuler.RetainedConormalDifferentialHelpers
import HodgeLean.Foundations.BundleThom.AnalyticNormalFramesHelpers

/-! # Transverse rank of the original retained conormal differential

The affine fibre isomorphism and the original smooth conormal coordinates
retain the specified conormal fibre throughout the comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleThom

theorem retainedAffineConormalDifferential_rank
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (k : ℕ) [SmoothOfRelativeDimension k Y.hom] [SmoothOfRelativeDimension (k + k) X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin (k + k) → ℂ) z).source) :
    Function.Injective (retainedAffineConormalDifferential X Y j (k + k) V hV x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential X Y j (k + k) V hV x hx z hz)) = k := by
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth k Y.hom
  have hi : Function.Injective
      (retainedAffineConormalDifferential X Y j (k + k) V hV x hx z hz) :=
    (affineConormalTensorDifferential_injective X Y j (k + k) V hV x hx z hz).comp
      (actualConormalFibreAffineCotangentIso j.left V hV x hx).toLinearEquiv.injective
  refine ⟨hi, ?_⟩
  obtain ⟨e⟩ := i1_conormalFibre_coordinates_nonempty j.left k X.hom (Over.w j) x
  rw [LinearMap.finrank_range_of_inj hi, e.finrank_eq, Module.finrank_fin_fun]

#print axioms retainedAffineConormalDifferential_rank

end HodgeLean.Foundations.TubularEuler
