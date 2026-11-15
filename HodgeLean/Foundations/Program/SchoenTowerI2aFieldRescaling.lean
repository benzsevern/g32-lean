import HodgeLean.Foundations.Program.SchoenTowerI2aFieldHelpers

/-! # Original-field generators under blowup coordinate rescaling
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Dividing the generator by a nonzero base element preserves the field it generates over that base.
Source: Mathlib, Subfield.closure_le and field division identities. -/
theorem s2v_i2a_rescaled_generator_field
    {R K : Type*} [CommRing R] [Field K] (φ : R →+* K) (v : K)
    (x : R) (hx : φ x ≠ 0) :
    Subfield.closure (Set.range φ ∪ {v / φ x}) =
      Subfield.closure (Set.range φ ∪ {v}) := by
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro z (hz | hz)
    · exact Subfield.subset_closure (Or.inl hz)
    · have hzv := Set.mem_singleton_iff.mp hz
      rw [hzv]
      exact div_mem (Subfield.subset_closure (Or.inr rfl))
        (Subfield.subset_closure (Or.inl ⟨x, rfl⟩))
  · apply Subfield.closure_le.mpr
    rintro z (hz | hz)
    · exact Subfield.subset_closure (Or.inl hz)
    · have hzv := Set.mem_singleton_iff.mp hz
      rw [hzv]
      have H : v / φ x * φ x ∈ Subfield.closure (Set.range φ ∪ {v / φ x}) :=
        mul_mem (Subfield.subset_closure (Or.inr rfl))
          (Subfield.subset_closure (Or.inl ⟨x, rfl⟩))
      rw [div_mul_cancel₀ v hx] at H
      exact H

/-- A paired monomial equation with exponent sum m loses the exceptional m-th power after dividing its generator by that parameter.
Source: Field division identities and pow_add. -/
theorem s2v_i2a_rescaled_paired_monomial
    {K : Type*} [Field K] (m a b : ℕ) (hab : a + b = m)
    (v ε x y Q : K) (hx : x ≠ 0)
    (hv : v ^ m = ε * x ^ a * y ^ b * Q) :
    (v / x) ^ m = ε * (y / x) ^ b * Q := by
  rw [div_pow, div_pow]
  apply (div_eq_iff (pow_ne_zero m hx)).mpr
  rw [hv, ← hab, pow_add]
  field_simp [hx]

end HodgeLean.Foundations.Program
