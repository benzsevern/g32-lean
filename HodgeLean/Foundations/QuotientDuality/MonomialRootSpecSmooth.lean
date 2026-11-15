import HodgeLean.Foundations.QuotientDuality.MonomialEtaleSpecSmooth

/-! Smooth schemes obtained from the lifted root polynomial parameter ring. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

theorem etale_lifted_polynomial_spec_smooth
    (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ)
    (b : ULift.{0} (MvPolynomial (Fin n) k) →+* A) (hb : b.Etale)
    (hbase : ∀ t : k, b (ULift.up (MvPolynomial.C t)) = algebraMap k A t) :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  let u : MvPolynomial (Fin n) k ≃+* ULift.{0} (MvPolynomial (Fin n) k) :=
    ULift.ringEquiv.symm
  have hbu : (b.comp u.toRingHom).Etale :=
    RingHom.Etale.stableUnderComposition u.toRingHom b
      (RingHom.Etale.of_bijective u.bijective) hb
  apply etale_polynomial_spec_smooth k A n (algebraMap k A) (b.comp u.toRingHom) hbu
  ext t
  exact hbase t

#print axioms etale_lifted_polynomial_spec_smooth
end HodgeLean.Foundations.QuotientDuality
