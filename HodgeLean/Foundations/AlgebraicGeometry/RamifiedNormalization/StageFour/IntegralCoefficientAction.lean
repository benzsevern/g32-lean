import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientFibre
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosureRestriction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Precomposition with the original integral-ring restriction acts on the fixed coefficient fibre. -/
def integralCoefficientFibreDeck
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ) (δ : L ≃ₐ[A] L) :
    integralCoefficientFibre (L := L) f φ → integralCoefficientFibre (L := L) f φ :=
  fun x => ⟨x.val.comp (δ.mapIntegralClosure.restrictScalars ℂ).toAlgHom, by
    intro r
    change x.val (δ.mapIntegralClosure (algebraMap A (integralClosure A L) (f r))) = φ r
    rw [AlgEquiv.commutes]
    exact x.property r⟩

/-- Every iterate of the coefficient-fibre action retains the corresponding original integral-ring power. -/
theorem integralCoefficientFibreDeck_iterate_evaluation
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ) (δ : L ≃ₐ[A] L)
    (n : ℕ) (x : integralCoefficientFibre (L := L) f φ) (b : integralClosure A L) :
    ((integralCoefficientFibreDeck f φ δ)^[n] x).val b =
      x.val ((δ.mapIntegralClosure ^ n) b) := by
  induction n generalizing x b with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((integralCoefficientFibreDeck f φ δ)^[n] x).val (δ.mapIntegralClosure b) = _
    rw [ih, pow_succ, AlgEquiv.mul_apply]

end AlgebraicGeometry.RamifiedNormalization.StageFour
