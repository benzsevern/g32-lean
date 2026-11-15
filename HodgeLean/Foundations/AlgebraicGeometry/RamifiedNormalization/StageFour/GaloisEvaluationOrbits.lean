import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.EvaluationOrbits
import Mathlib.RingTheory.Invariant.Galois

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Integral-closure evaluations above one scalar-preserving base evaluation form one Galois orbit. -/
theorem integralClosure_evaluation_orbit
    {k R K L : Type*} [Field k] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra k R] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p q : integralClosure R L →+* k)
    (hbase : ∀ r, p (algebraMap R (integralClosure R L) r) =
      q (algebraMap R (integralClosure R L) r))
    (hp : ∀ a : k, p (algebraMap R (integralClosure R L) (algebraMap k R a)) = a)
    (hq : ∀ a : k, q (algebraMap R (integralClosure R L) (algebraMap k R a)) = a) :
    letI := IsIntegralClosure.MulSemiringAction R K L (integralClosure R L)
    ∃ g : L ≃ₐ[K] L, ∀ b, p (g • b) = q b := by
  let B := integralClosure R L
  let c : k →+* B := (algebraMap R B).comp (algebraMap k R)
  letI : Algebra k B := c.toAlgebra
  letI := IsIntegralClosure.MulSemiringAction R K L B
  letI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  letI : Algebra.IsInvariant R B (L ≃ₐ[K] L) :=
    Algebra.isInvariant_of_isGalois R K L B
  letI : SMulCommClass (L ≃ₐ[K] L) R B := ⟨fun g r b => by
    simp only [Algebra.smul_def]
    change (galRestrict R K L B g) (algebraMap R B r * b) =
      algebraMap R B r * (galRestrict R K L B g) b
    rw [map_mul, AlgEquiv.commutes]⟩
  letI : SMulCommClass (L ≃ₐ[K] L) k B := ⟨fun g a b => by
    change (galRestrict R K L B g) (algebraMap R B (algebraMap k R a) * b) =
      algebraMap R B (algebraMap k R a) * (galRestrict R K L B g) b
    rw [map_mul, AlgEquiv.commutes]⟩
  let pA : B →ₐ[k] k := { p with commutes' := hp }
  let qA : B →ₐ[k] k := { q with commutes' := hq }
  exact invariant_evaluation_orbit pA qA hbase

end AlgebraicGeometry.RamifiedNormalization.StageFour
