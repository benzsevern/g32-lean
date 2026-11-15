import HodgeLean.Foundations.Program.SchoenTowerI2aFractionBase

/-! # Clearing the Kummer coefficient denominator in the original field
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Multiplication by one nonzero affine base element clears a Kummer coefficient denominator without changing the ambient field.
Source: Mathlib, IsFractionRing.div_surjective and field division identities. -/
theorem s2v_i2a_clear_kummer_denominator
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] (m : ℕ) (hm : 0 < m) (v : K) (a : F)
    (hv : v ^ m = algebraMap F K a) :
    ∃ s b : R, algebraMap R K s ≠ 0 ∧
      (algebraMap R K s * v) ^ m = algebraMap R K b := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective R a
  have hsF : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hsK : algebraMap R K s ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R F K]
    exact (map_ne_zero (algebraMap F K)).mpr hsF
  refine ⟨s, r * s ^ (m - 1), hsK, ?_⟩
  rw [mul_pow, hv, map_div₀, ← IsScalarTower.algebraMap_apply R F K,
    ← IsScalarTower.algebraMap_apply R F K, map_mul, map_pow]
  have hpow : algebraMap R K s ^ m = algebraMap R K s ^ (m - 1) * algebraMap R K s := by
    rw [← pow_succ, Nat.sub_one_add_one hm.ne']
  rw [hpow]
  field_simp [hsK] <;> ring

end HodgeLean.Foundations.Program
