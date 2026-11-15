import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The localization at a nonzero principal prime of a Noetherian domain is
a discrete valuation ring, with the displayed prime as a uniformizer. -/
theorem s2v_l1b_prime_localization_dvr
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : R) (hp : Prime p) :
    let P := Ideal.span ({p} : Set R)
    letI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap R (Localization.AtPrime P) p} := by
  let P := Ideal.span ({p} : Set R)
  letI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let A := Localization.AtPrime P
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap R A p} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P A]
    exact Ideal.map_span (algebraMap R A) {p} |>.trans (by simp only [Set.image_singleton])
  have hpA : algebraMap R A p ≠ 0 :=
    fun h => hp.ne_zero ((IsLocalization.injective A P.primeCompl_le_nonZeroDivisors)
      (h.trans (map_zero _).symm))
  have hmaxne : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    intro h
    have hh : algebraMap R A p ∈ IsLocalRing.maximalIdeal A := by
      rw [hmax]
      exact Ideal.subset_span (Set.mem_singleton _)
    rw [h, Ideal.mem_bot] at hh
    exact hpA hh
  have hnfield : ¬ IsField A := IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hmaxne
  have hprincipal : (IsLocalRing.maximalIdeal A).IsPrincipal := by
    rw [hmax]
    infer_instance
  exact ⟨((IsDiscreteValuationRing.TFAE A hnfield).out 5 1).mp hprincipal, hmax⟩

end HodgeLean.Foundations.Program
