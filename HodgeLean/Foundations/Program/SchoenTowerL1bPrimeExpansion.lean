import HodgeLean.Foundations.Program.SchoenTowerL1bPrimeLocalization
import HodgeLean.Foundations.Program.SchoenTowerL1bDvrExpansion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every principal prime of a Noetherian domain over a characteristic-zero
field has an injective scalar-preserving expansion detecting that prime. -/
theorem s2v_l1b_prime_series_expansion
    {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra k R]
    (p : R) (hp : Prime p) :
    let P := Ideal.span ({p} : Set R)
    letI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    let A := Localization.AtPrime P
    let K := IsLocalRing.ResidueField A
    ∃ j : R →+* PowerSeries K,
      Function.Injective j ∧ j p = PowerSeries.X ∧
      (∀ v : R, ¬ p ∣ v → (j v).constantCoeff ≠ 0) ∧
      ∀ c : k, j (algebraMap k R c) = PowerSeries.C (algebraMap k K c) := by
  let P := Ideal.span ({p} : Set R)
  letI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let A := Localization.AtPrime P
  let K := IsLocalRing.ResidueField A
  have hRA : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  have hpA : algebraMap R A p ≠ 0 := fun h => hp.ne_zero (hRA (h.trans (map_zero _).symm))
  obtain ⟨hDVR, hmax⟩ := s2v_l1b_prime_localization_dvr p hp
  obtain ⟨jA, hjA, hjp, hjk⟩ := s2v_l1b_dvr_series_expansion (k := k)
    (algebraMap R A p) hmax (fun _ _ h => mul_left_cancel₀ hpA h)
  refine ⟨jA.comp (algebraMap R A), hjA.comp hRA, hjp, ?_, ?_⟩
  · intro v hv
    have hvP : v ∈ P.primeCompl := by
      change v ∉ Ideal.span ({p} : Set R)
      simpa only [Ideal.mem_span_singleton] using hv
    have hu : IsUnit (algebraMap R A v) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff A P v).mpr hvP
    exact ((hu.map jA).map PowerSeries.constantCoeff).ne_zero
  · intro c
    change jA (algebraMap R A (algebraMap k R c)) = _
    rw [← IsScalarTower.algebraMap_apply k R A]
    exact hjk c

end HodgeLean.Foundations.Program
