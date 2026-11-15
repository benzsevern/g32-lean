import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.QuasiFinite.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The actual integral closure of a normal noetherian domain of characteristic zero in a faithful quasi-finite field algebra is finite. -/
theorem s2_integralClosure_finite_of_quasiFinite_field
    (R L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] [Field L] [Algebra R L]
    [FaithfulSMul R L] [Algebra.QuasiFinite R L] :
    Module.Finite R (integralClosure R L) := by
  let f : FractionRing R →ₐ[R] L := IsFractionRing.liftAlgHom
    (g := Algebra.ofId R L) (FaithfulSMul.algebraMap_injective R L)
  letI : Algebra (FractionRing R) L := f.toRingHom.toAlgebra
  haveI : IsScalarTower R (FractionRing R) L :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  haveI : Algebra.QuasiFinite (FractionRing R) L :=
    Algebra.QuasiFinite.of_restrictScalars R (FractionRing R) L
  haveI : FiniteDimensional (FractionRing R) L := Module.Finite.of_quasiFinite
  exact IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)

end HodgeLean.Foundations.Program
