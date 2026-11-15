import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SliceChartCover

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A chart support equation detects the zero parameter at its actual point in the fibre. -/
theorem affine_slice_map_support_iff
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0)
    (X : Over (Spec ↧ℂ))
    (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap R))
    (j : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X)
    (hj : ∀ a, Point.map p (Point.map j a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a)
    (D : Set X.left)
    (hD : j.left ⁻¹' D = PrimeSpectrum.zeroLocus {RegularPairChart.ratio u v}) (z : ℂ) :
    (affineChartSliceMap u v φ hu hv X p j hj z).val.left
      (IsLocalRing.closedPoint ℂ) ∈ D ↔ z = 0 := by
  change j.left (((affineChartPointFibreHomeomorph u v φ hu hv).symm z).val.left
    (IsLocalRing.closedPoint ℂ)) ∈ D ↔ _
  change ((affineChartPointFibreHomeomorph u v φ hu hv).symm z).val.left
    (IsLocalRing.closedPoint ℂ) ∈ j.left ⁻¹' D ↔ _
  rw [hD]
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  change RegularPairChart.ratio u v ∈
    (((affineChartPointFibreHomeomorph u v φ hu hv).symm z).val.left
      (IsLocalRing.closedPoint ℂ)).asIdeal ↔ _
  exact affine_chart_ratio_prime_iff_zero u v φ hu hv z

end AlgebraicGeometry.RamifiedNormalization.StageFour
