import HodgeLean.Foundations.QuotientDuality.MonomialComponentEtale
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! Normal integral components of the smooth polynomial-root cover. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem etale_polynomial_root_component
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ)
    (A : Type*) [CommRing A]
    (b : ULift.{0} (MvPolynomial (Fin n) k) →+* A) (hb : b.Etale)
    (p : Ideal A) (hp : IsMinimalPrime p) :
    ((Ideal.Quotient.mk p).comp b).Etale ∧
      IsDomain (A ⧸ p) ∧ IsIntegrallyClosed (A ⧸ p) := by
  let B := ULift.{0} (MvPolynomial (Fin n) k)
  letI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv
    (MvPolynomial (Fin n) k) (ULift.ringEquiv.symm : MvPolynomial (Fin n) k ≃+* B)
  letI : Algebra B A := b.toAlgebra
  letI : Algebra.Etale B A := hb.toAlgebra
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing B A
  have hlocal (q : Ideal A) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
    (etale_root_localization_normal n A b hb q).1
  have hpEt := minimal_component_quotient_etale A hlocal p hp
  have hbQ : ((Ideal.Quotient.mk p).comp b).Etale := by
    letI : Algebra.Etale A (A ⧸ p) := (RingHom.etale_algebraMap).1 hpEt
    change (algebraMap B (A ⧸ p)).Etale
    exact (RingHom.etale_algebraMap).2 (Algebra.Etale.comp B A (A ⧸ p))
  letI : p.IsPrime := hp.isPrime
  refine ⟨hbQ, inferInstance, ?_⟩
  apply IsIntegrallyClosed.of_localization_maximal
  intro q hq hmax
  exact (etale_root_localization_normal n (A ⧸ p) ((Ideal.Quotient.mk p).comp b) hbQ q).2

#print axioms etale_polynomial_root_component
end HodgeLean.Foundations.QuotientDuality
