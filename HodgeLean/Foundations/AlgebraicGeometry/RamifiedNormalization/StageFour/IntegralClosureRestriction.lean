import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restriction of the original algebra automorphism to integral elements retains multiplication and all powers. -/
def integralClosureRestrictionHom
    {A L : Type*} [CommRing A] [CommRing L] [Algebra A L] :
    (L ≃ₐ[A] L) →* (integralClosure A L ≃ₐ[A] integralClosure A L) where
  toFun := AlgEquiv.mapIntegralClosure
  map_one' := by
    apply AlgEquiv.ext
    intro b
    apply Subtype.ext
    rfl
  map_mul' := by
    intro f g
    apply AlgEquiv.ext
    intro b
    apply Subtype.ext
    rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
