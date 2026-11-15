import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineChartPointFibre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The prime of an actual affine complex point tests vanishing by its scalar-preserving evaluation. -/
theorem affine_point_mem_prime_iff
    {A : Type} [CommRing A] [Algebra ℂ A] (φ : A →ₐ[ℂ] ℂ) (a : A) :
    a ∈ (((ComplexPoint.affineSpecEquiv A).symm φ).left
      (IsLocalRing.closedPoint ℂ)).asIdeal ↔ φ a = 0 := by
  change φ a ∈ IsLocalRing.maximalIdeal ℂ ↔ φ a = 0
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

/-- The ratio belongs to the actual centre-chart point prime exactly at coordinate zero. -/
theorem affine_chart_ratio_prime_iff_zero
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0) (z : ℂ) :
    RegularPairChart.ratio u v ∈
      (((affineChartPointFibreHomeomorph u v φ hu hv).symm z).val.left
        (IsLocalRing.closedPoint ℂ)).asIdeal ↔ z = 0 := by
  change RegularPairChart.ratio u v ∈
    (((ComplexPoint.affineSpecEquiv (RegularPairChart.ring u v)).symm
      (centreChartEvaluation u v φ hu hv z)).left (IsLocalRing.closedPoint ℂ)).asIdeal ↔ z = 0
  rw [affine_point_mem_prime_iff, (centreChartEvaluation_spec u v φ hu hv z).2]

end AlgebraicGeometry.RamifiedNormalization.StageFour
