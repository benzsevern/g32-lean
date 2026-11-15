import HodgeLean.Foundations.Program.SchoenCycleC2ConormalRankHelpers
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The dual conormal sequence of a smooth algebra quotient -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction of ambient cotangent functionals to the actual conormal module
has kernel exactly the functionals pulled back from the quotient differentials. -/
theorem dualConormal_kernel
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension A B) :
    LinearMap.ker P.cotangentComplex.dualMap = LinearMap.range P.toKaehler.dualMap := by
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _ P.toKaehler_surjective,
    P.exact_cotangentComplex_toKaehler.linearMap_ker_eq]

/-- For a smooth algebra quotient of a smooth algebra, every conormal
functional extends to an ambient cotangent functional. -/
theorem dualConormal_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension A B) [Algebra.FormallySmooth A P.Ring]
    [Algebra.FormallySmooth A B] : Function.Surjective P.cotangentComplex.dualMap := by
  obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp inferInstance
  intro ν
  refine ⟨ν.comp l, ?_⟩
  ext s
  change ν (l (P.cotangentComplex s)) = ν s
  exact congrArg ν (DFunLike.congr_fun hl s)

/-- The quotient by source tangent functionals identifies with the actual
normal dual module, via restriction rather than a choice of bases. -/
def dualConormalQuotientEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension A B) [Algebra.FormallySmooth A P.Ring]
    [Algebra.FormallySmooth A B] :
    (Module.Dual B P.CotangentSpace ⧸ LinearMap.range P.toKaehler.dualMap) ≃ₗ[B]
      Module.Dual B P.Cotangent :=
  (Submodule.quotEquivOfEq _ _ (dualConormal_kernel P).symm).trans
    (P.cotangentComplex.dualMap.quotKerEquivOfSurjective (dualConormal_surjective P))

/-- On each ambient functional the quotient identification is the original
cotangent restriction, retaining its value on every ideal class. -/
theorem dualConormalQuotientEquiv_mk
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension A B) [Algebra.FormallySmooth A P.Ring]
    [Algebra.FormallySmooth A B] (v : Module.Dual B P.CotangentSpace) :
    dualConormalQuotientEquiv P
      ((LinearMap.range P.toKaehler.dualMap).mkQ v) = P.cotangentComplex.dualMap v := by
  rfl

#print axioms dualConormalQuotientEquiv
#print axioms dualConormalQuotientEquiv_mk
#print axioms dualConormal_surjective
#print axioms dualConormal_kernel
end HodgeLean.Foundations.Program.G32Native
