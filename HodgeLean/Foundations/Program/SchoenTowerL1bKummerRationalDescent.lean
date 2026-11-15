import Mathlib.RingTheory.Invariant.Basic
import Mathlib.FieldTheory.Galois.Basic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Descent of invariant regular numerators gives descent of invariant rational functions. -/
theorem s2v_l1b_fixed_rational_function_descends
    (A B F E : Type*) [CommRing A] [CommRing B] [Field F] [Field E]
    [Algebra A B] [Algebra A F] [Algebra A E] [Algebra B E] [Algebra F E]
    [IsFractionRing A F] [IsFractionRing B E]
    [IsScalarTower A B E] [IsScalarTower A F E] [Algebra.IsIntegral A B]
    (I : Type*) (ρ : I → (B →+* B)) (τ : I → (E ≃ₐ[F] E))
    (hρ : ∀ i b, algebraMap B E (ρ i b) = τ i (algebraMap B E b))
    (hdesc : ∀ b : B, (∀ i, ρ i b = b) → ∃ a : A, algebraMap A B a = b)
    (z : E) (hz : ∀ i, τ i z = z) : ∃ c : F, algebraMap F E c = z := by
  have hc (a : A) : algebraMap F E (algebraMap A F a) =
      algebraMap B E (algebraMap A B a) := by
    simp only [← IsScalarTower.algebraMap_apply]
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A F).mpr inferInstance
  have : Nontrivial B := (IsFractionRing.nontrivial_iff_nontrivial B E).mpr inferInstance
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective B z
  have hy' : algebraMap B E y ≠ 0 := by simpa using nonZeroDivisors.ne_zero hy
  obtain ⟨b, a, ha, hb⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := A) y).exists_smul_eq_mul x hy
  rw [mul_comm, Algebra.smul_def, mul_comm] at hb
  replace ha : algebraMap B E (algebraMap A B a) ≠ 0 := by simpa [← hc]
  have hxy : algebraMap B E x / algebraMap B E y =
      algebraMap B E b / algebraMap B E (algebraMap A B a) := by
    rw [div_eq_div_iff hy' ha, ← map_mul, hb, map_mul]
  obtain ⟨b₀, hb₀⟩ := hdesc b (by
    intro i
    apply IsFractionRing.injective B E
    have h := hz i
    rw [hxy, map_div₀, ← hc, (τ i).commutes] at h
    rw [hc] at h
    exact (hρ i b).trans ((div_left_inj' ha).mp h))
  refine ⟨algebraMap A F b₀ / algebraMap A F a, ?_⟩
  rw [hxy, map_div₀, hc, hc, hb₀]

end HodgeLean.Foundations.Program
