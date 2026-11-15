import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Integral complex evaluations over the fixed original coefficient evaluation form the specified affine coefficient fibre. -/
abbrev integralCoefficientFibre
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ) :=
  {ev : integralClosure A L →ₐ[ℂ] ℂ //
    ∀ r, ev (algebraMap A (integralClosure A L) (f r)) = φ r}

end AlgebraicGeometry.RamifiedNormalization.StageFour
