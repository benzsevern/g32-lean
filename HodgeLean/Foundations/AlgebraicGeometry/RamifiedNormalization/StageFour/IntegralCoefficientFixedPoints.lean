import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientAction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Fixing every original integral evaluation is exactly fixing the corresponding point of the coefficient fibre. -/
theorem integralCoefficientFibreDeck_fixed_iff
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ) (δ : L ≃ₐ[A] L)
    (n : ℕ) (x : integralCoefficientFibre (L := L) f φ) :
    (integralCoefficientFibreDeck f φ δ)^[n] x = x ↔
      ∀ b, x.val ((δ.mapIntegralClosure ^ n) b) = x.val b := by
  constructor
  · intro h b
    rw [← integralCoefficientFibreDeck_iterate_evaluation, h]
  · intro h
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    rw [integralCoefficientFibreDeck_iterate_evaluation]
    exact h b

/-- The original field period fixes every point of its constructed coefficient evaluation fibre. -/
theorem integralCoefficientFibreDeck_period
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ) (δ : L ≃ₐ[A] L)
    (m : ℕ) (hm : δ ^ m = 1) (x : integralCoefficientFibre (L := L) f φ) :
    (integralCoefficientFibreDeck f φ δ)^[m] x = x := by
  apply (integralCoefficientFibreDeck_fixed_iff f φ δ m x).mpr
  have hp := congrArg (integralClosureRestrictionHom (A := A) (L := L)) hm
  rw [map_pow, map_one] at hp
  change δ.mapIntegralClosure ^ m = 1 at hp
  intro b
  rw [hp, AlgEquiv.one_apply]

end AlgebraicGeometry.RamifiedNormalization.StageFour
