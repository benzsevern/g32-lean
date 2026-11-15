import HodgeLean.Foundations.Program.SchoenCycleC1KummerInverseHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1UnitDiscriminantHelpers
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! # Actual integral closures in unit Kummer field presentations -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- A unit Kummer presentation of a power generator identifies an etale
structure on the actual integral closure, without a normality premise on
the root algebra. -/
theorem s2e_c1_kummer_integralClosure_etale
    {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.IsSeparable K L] (B : PowerBasis K L)
    (hint : IsIntegral R B.gen) (m : ℕ) (hm : 0 < m)
    (c d : Rˣ) (hd : (d : R) = (m : R))
    (hmin : minpoly R B.gen = X ^ m - C (c : R)) :
    Algebra.Etale R (integralClosure R L) := by
  haveI : Module.IsTorsionFree R L := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  have hz : B.gen ^ m = algebraMap R L (c : R) := by
    have hh := minpoly.aeval R B.gen
    rw [hmin] at hh
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hh
  have hinv : IsIntegral R (aeval B.gen (minpoly K B.gen).derivative)⁻¹ := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hint,
      derivative_map, aeval_map_algebraMap, hmin]
    exact s2e_c1_kummer_inverse_derivative_integral m hm c d hd B.gen hz
  obtain ⟨D, hD⟩ := s2e_c1_discriminant_unit_of_integral_inverse_derivative B hint hinv
  have hclosure := s2e_c1_integralClosure_eq_adjoin_of_unit_discriminant B hint D hD
  haveI : Algebra.Etale R (AdjoinRoot (minpoly R B.gen)) := by
    rw [hmin]
    exact s2e_c1_kummer_adjoinRoot_etale m (Nat.ne_of_gt hm) (c : R) c.isUnit
      (hd ▸ d.isUnit)
  exact Algebra.Etale.of_equiv ((minpoly.equivAdjoin hint).trans
    (Subalgebra.equivOfEq _ _ hclosure.symm))

/-- A Kummer minimal polynomial over the fraction field suffices: its
integral generator and its base-ring minimal polynomial are derived. -/
theorem s2e_c1_kummer_integralClosure_etale_of_generic_minpoly
    {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.IsSeparable K L] (B : PowerBasis K L)
    (m : ℕ) (hm : 0 < m) (c d : Rˣ) (hd : (d : R) = (m : R))
    (hmin : minpoly K B.gen = X ^ m - C (algebraMap R K (c : R))) :
    Algebra.Etale R (integralClosure R L) := by
  have hz : B.gen ^ m = algebraMap R L (c : R) := by
    have hh := minpoly.aeval K B.gen
    rw [hmin] at hh
    rw [IsScalarTower.algebraMap_apply R K L]
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hh
  have hint : IsIntegral R B.gen := by
    apply IsIntegral.of_pow hm
    rw [hz]
    exact isIntegral_algebraMap
  have hminR : minpoly R B.gen = X ^ m - C (c : R) := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hint, hmin]
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  exact s2e_c1_kummer_integralClosure_etale B hint m hm c d hd hminR

end HodgeLean.Foundations.Program
