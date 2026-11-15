import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosurePresentation

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The two presentations of the original integral elements retain their actual complex scalar maps. -/
def normalizedChartIntegralClosureComplexEquiv
    {A L : Type} [CommRing A] [Field L] [Algebra ℂ A] [Algebra A L]
    [Algebra ℂ L] [IsScalarTower ℂ A L] :
    letI := ((StageTwo.integralCoeff (algebraMap A L)).comp (algebraMap ℂ A)).toAlgebra
    normalizedChart (algebraMap A L) ≃ₐ[ℂ] integralClosure A L := by
  letI := ((StageTwo.integralCoeff (algebraMap A L)).comp (algebraMap ℂ A)).toAlgebra
  exact { normalizedChartIntegralClosureEquiv with
    commutes' := fun z => by
      apply Subtype.ext
      change algebraMap A L (algebraMap ℂ A z) = algebraMap ℂ L z
      exact (IsScalarTower.algebraMap_apply ℂ A L z).symm }

end AlgebraicGeometry.RamifiedNormalization.StageFour
