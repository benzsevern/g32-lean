import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedResidualEquations

/-! # Restriction of supplied residual polynomial coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- A map out of the actual residual quotient is determined in its polynomial
coordinates by its coefficient map and the restricted original Rees ratio. -/
theorem pairedC3_residual_coordinate_restriction
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (t : B)
    (E : (B ⧸ J) ≃+* (A ⧸ I)[X])
    (hcoeff : ∀ a, E (Ideal.Quotient.mk J (f a)) = Polynomial.C (Ideal.Quotient.mk I a))
    (ht : E (Ideal.Quotient.mk J t) = X)
    (r : (B ⧸ J) →+* C) (c : (A ⧸ I) →+* C)
    (hc : ∀ a, r (Ideal.Quotient.mk J (f a)) = c (Ideal.Quotient.mk I a)) :
    r.comp E.symm.toRingHom =
      eval₂RingHom c (r (Ideal.Quotient.mk J t)) := by
  apply Polynomial.ringHom_ext
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change r (E.symm (Polynomial.C (Ideal.Quotient.mk I a))) =
      eval₂ c (r (Ideal.Quotient.mk J t)) (Polynomial.C (Ideal.Quotient.mk I a))
    have he : E.symm (Polynomial.C (Ideal.Quotient.mk I a)) =
        Ideal.Quotient.mk J (f a) := by
      rw [← hcoeff a, RingEquiv.symm_apply_apply]
    rw [he, eval₂_C]
    exact hc a
  · change r (E.symm X) = eval₂ c (r (Ideal.Quotient.mk J t)) X
    have he : E.symm X = Ideal.Quotient.mk J t := by
      rw [← ht, RingEquiv.symm_apply_apply]
    rw [he, eval₂_X]

/-- Restriction of each supplied residual coordinate polynomial can be
calculated without choosing a polynomial representative in the ambient chart. -/
theorem pairedC3_residual_coordinate_restriction_apply
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (t : B)
    (E : (B ⧸ J) ≃+* (A ⧸ I)[X])
    (hcoeff : ∀ a, E (Ideal.Quotient.mk J (f a)) = Polynomial.C (Ideal.Quotient.mk I a))
    (ht : E (Ideal.Quotient.mk J t) = X)
    (r : (B ⧸ J) →+* C) (c : (A ⧸ I) →+* C)
    (hc : ∀ a, r (Ideal.Quotient.mk J (f a)) = c (Ideal.Quotient.mk I a))
    (z : B ⧸ J) :
    r z = eval₂ c (r (Ideal.Quotient.mk J t)) (E z) := by
  have h := congrArg (fun F : (A ⧸ I)[X] →+* C => F (E z))
    (pairedC3_residual_coordinate_restriction I J f t E hcoeff ht r c hc)
  change r (E.symm (E z)) = eval₂ c (r (Ideal.Quotient.mk J t)) (E z) at h
  rwa [RingEquiv.symm_apply_apply] at h

#print axioms pairedC3_residual_coordinate_restriction
#print axioms pairedC3_residual_coordinate_restriction_apply
end HodgeLean.Foundations.Program.G32Native
