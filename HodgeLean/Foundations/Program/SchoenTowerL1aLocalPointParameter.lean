import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Polynomial.Ideal

/-! # Local point ideals for actual unramified curve parameters

At a rational zero of an unramified polynomial parameter, that parameter
generates the localized point ideal. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- A parameter unramified at its rational zero generates the actual localized point ideal.
Source: Stacks Project, tag 02FM, the maximal ideal criterion for an unramified local map. -/
theorem s2v_l1a_unramified_parameter_local_point_ideal
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (g : A) (ev : A →ₐ[K] K) (hzero : ev g = 0)
    (hunram : letI : (RingHom.ker ev.toRingHom).IsPrime := RingHom.ker_isPrime _
      letI := (Polynomial.aeval (R := K) g).toRingHom.toAlgebra
      Algebra.IsUnramifiedAt (Polynomial K) (RingHom.ker ev.toRingHom)) :
    letI : (RingHom.ker ev.toRingHom).IsPrime := RingHom.ker_isPrime _
    (RingHom.ker ev.toRingHom).map
        (algebraMap A (Localization.AtPrime (RingHom.ker ev.toRingHom))) =
      Ideal.span {algebraMap A (Localization.AtPrime (RingHom.ker ev.toRingHom)) g} := by
  let P := Polynomial K
  let m := RingHom.ker ev.toRingHom
  let p : Ideal P := RingHom.ker (Polynomial.evalRingHom (0 : K))
  letI : m.IsPrime := RingHom.ker_isPrime _
  letI : p.IsPrime := RingHom.ker_isPrime _
  letI : Algebra P A := (Polynomial.aeval (R := K) g).toRingHom.toAlgebra
  letI : Algebra.IsUnramifiedAt P m := hunram
  letI : Algebra.FiniteType P A := .of_restrictScalars_finiteType K P A
  have hcomp : ev.toRingHom.comp (algebraMap P A) = Polynomial.evalRingHom (0 : K) := by
    apply Polynomial.ringHom_ext
    · intro k
      change ev (Polynomial.aeval (R := K) g (Polynomial.C k)) =
        Polynomial.evalRingHom (0 : K) (Polynomial.C k)
      simp
    · change ev (Polynomial.aeval (R := K) g Polynomial.X) =
        Polynomial.evalRingHom (0 : K) Polynomial.X
      simp [hzero]
  have hp : m.under P = p := by
    change RingHom.ker (ev.toRingHom.comp (algebraMap P A)) = p
    rw [hcomp]
  letI : m.LiesOver p := ⟨hp.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p m
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p m).mp inferInstance).2
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  rw [← hmap]
  have hpX : p = Ideal.span {Polynomial.X} := by
    change RingHom.ker (Polynomial.evalRingHom (0 : K)) = _
    rw [Polynomial.ker_evalRingHom]
    simp
  rw [hpX, Ideal.map_span, Set.image_singleton]
  congr 2
  rw [IsScalarTower.algebraMap_apply P A]
  change algebraMap A (Localization.AtPrime m) (Polynomial.aeval (R := K) g Polynomial.X) = _
  rw [Polynomial.aeval_X]

end HodgeLean.Foundations.Program
