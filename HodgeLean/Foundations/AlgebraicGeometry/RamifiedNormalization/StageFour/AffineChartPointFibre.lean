import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartPointFibre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The chart coefficient map retains its complex scalar structure. -/
def regularPairCoefficientAlgHom
    {R : Type} [CommRing R] [Algebra ℂ R] (u v : R) :
    R →ₐ[ℂ] RegularPairChart.ring u v where
  __ := RegularPairChart.coeff u v
  commutes' _ := rfl

/-- The fibre of the actual affine-chart point map has the original ratio as its complex coordinate. -/
def affineChartPointFibreHomeomorph
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0) :
    {p : ComplexPoint (CategoryTheory.Over.mk
      (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v))) //
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) p =
        (ComplexPoint.affineSpecEquiv R).symm φ} ≃ₜ ℂ := by
  let H := ComplexPoint.affineSpecHomeomorph (RegularPairChart.ring u v)
  have hiff : ∀ p : ComplexPoint (CategoryTheory.Over.mk
      (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v))),
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) p =
        (ComplexPoint.affineSpecEquiv R).symm φ ↔
      (H p).toRingHom.comp (RegularPairChart.coeff u v) = φ.toRingHom := by
    intro p
    rw [← (ComplexPoint.affineSpecEquiv R).injective.eq_iff,
      ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap, Equiv.apply_symm_apply]
    constructor
    · intro he
      exact congrArg AlgHom.toRingHom he
    · intro he
      exact AlgHom.toRingHom_injective he
  exact (H.subtype hiff).trans (centreChartPointHomeomorph u v φ hu hv)

end AlgebraicGeometry.RamifiedNormalization.StageFour
