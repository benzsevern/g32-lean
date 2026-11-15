import HodgeLean.Foundations.Program.SchoenTowerL1bPrimeExpansion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
universe u v
namespace HodgeLean.Foundations.Program

/-- The prime-detecting expansion can use algebraically closed coefficients
of characteristic zero while retaining the base scalars. -/
theorem s2v_l1b_closed_prime_series_expansion
    {k : Type u} {R : Type v} [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra k R] (p : R) (hp : Prime p) :
    ∃ (K : Type v) (hK : Field K),
      letI := hK
      ∃ (hzero : CharZero K) (hclosed : IsAlgClosed K)
        (σ : k →+* K) (β : R →+* PowerSeries K),
        Function.Injective β ∧ β p = PowerSeries.X ∧
        (∀ w : R, ¬ p ∣ w → (β w).constantCoeff ≠ 0) ∧
        ∀ c : k, β (algebraMap k R c) = PowerSeries.C (σ c) := by
  let P := Ideal.span ({p} : Set R)
  letI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let A := Localization.AtPrime P
  let K₀ := IsLocalRing.ResidueField A
  let K := AlgebraicClosure K₀
  letI : CharZero K₀ := charZero_of_injective_algebraMap (algebraMap k K₀).injective
  obtain ⟨β₀, hβ₀, hβp, hloc, hscalar⟩ := s2v_l1b_prime_series_expansion (k := k) p hp
  let σ : k →+* K := (algebraMap K₀ K).comp (algebraMap k K₀)
  let β : R →+* PowerSeries K := (PowerSeries.map (algebraMap K₀ K)).comp β₀
  refine ⟨K, inferInstance, inferInstance, inferInstance, σ, β,
    (PowerSeries.map_injective _ (algebraMap K₀ K).injective).comp hβ₀, ?_, ?_, ?_⟩
  · change PowerSeries.map (algebraMap K₀ K) (β₀ p) = PowerSeries.X
    rw [hβp, PowerSeries.map_X]
  · intro w hw
    change algebraMap K₀ K ((β₀ w).constantCoeff) ≠ 0
    intro h
    exact hloc w hw ((algebraMap K₀ K).injective (h.trans (map_zero _).symm))
  · intro c
    change PowerSeries.map (algebraMap K₀ K) (β₀ (algebraMap k R c)) = _
    rw [hscalar, PowerSeries.map_C]
    rfl

end HodgeLean.Foundations.Program
