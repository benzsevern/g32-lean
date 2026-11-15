import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedProjectionSmooth

/-! # Unit-scaled parameters on supplied polynomial charts -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- A variable unit multiple of the polynomial coordinate gives a smooth
map to the affine line whenever the coefficient scheme is smooth. -/
theorem pairedC3_scaled_projection_smooth
    (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    (E : B ≃+* A[X]) (c : R →+* B)
    (hc : ∀ r, E (c r) = C (algebraMap R A r))
    (α : Aˣ) (z : B) (hz : E z = C (↑α : A) * X)
    (hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Smooth (Spec.map (CommRingCat.ofHom (eval₂RingHom c z))) := by
  let e : A[X] ≃ₐ[A] A[X] := Polynomial.algEquivOfCompEqX
    (C (↑α : A) * X) (C (↑α⁻¹ : A) * X)
    (by simp [← mul_assoc, ← C_mul])
    (by simp [← mul_assoc, ← C_mul])
  have he : e X = C (↑α : A) * X := by
    simp only [e, Polynomial.algEquivOfCompEqX_apply, aeval_X]
  have hz' : z = E.symm (e X) := by
    apply E.injective
    rw [RingEquiv.apply_symm_apply, he, hz]
  rw [hz']
  exact pairedC3_supplied_projection_smooth R A B E c hc e hs

#print axioms pairedC3_scaled_projection_smooth
end HodgeLean.Foundations.Program.G32Native
