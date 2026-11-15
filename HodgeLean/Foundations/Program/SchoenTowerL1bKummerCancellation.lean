import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Dividing a field generator by a nonzero base section preserves its generated subfield. -/
theorem s2v_l1b_div_generator_subfield
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    (t : K) (a : R) (ha : ρ a ≠ 0) :
    Subfield.closure (Set.range ρ ∪ {t / ρ a}) =
      Subfield.closure (Set.range ρ ∪ {t}) := by
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro x (hx | hx)
    · exact Subfield.subset_closure (Or.inl hx)
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact Subfield.div_mem _ (Subfield.subset_closure (Or.inr rfl))
        (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  · apply Subfield.closure_le.mpr
    rintro x (hx | hx)
    · exact Subfield.subset_closure (Or.inl hx)
    · rw [Set.mem_singleton_iff] at hx
      subst x
      have ht : (t / ρ a) * ρ a ∈
          Subfield.closure (Set.range ρ ∪ {t / ρ a}) := Subfield.mul_mem
        (Subfield.closure (Set.range ρ ∪ {t / ρ a}))
        (Subfield.subset_closure (Or.inr (Set.mem_singleton _)))
        (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      rw [div_mul_cancel₀ t ha] at ht
      exact ht

/-- Removing the full exceptional product cancels its multiplicity from the field equation. -/
theorem s2v_l1b_exceptional_power_cancel
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    {J L : Type*} [Fintype J] [Fintype L]
    (g : J → R) (n : J → ℕ) (eE : L → R)
    (ε₀ δ : Rˣ) (u v : R) (m α : ℕ) (t₀ : K)
    (hE : ρ (∏ j, eE j) ≠ 0)
    (ht₀ : t₀ ^ m = ρ (ε₀ : R) * ∏ j, ρ (g j) ^ n j)
    (hfactors : (∏ j, g j ^ n j) =
      (δ : R) * u ^ α * v ^ (m - α) * (∏ j, eE j) ^ m) :
    (t₀ / ρ (∏ j, eE j)) ^ m =
      ρ ((ε₀ * δ : Rˣ) : R) * ρ u ^ α * ρ v ^ (m - α) := by
  have hf := congrArg ρ hfactors
  simp only [map_prod, map_mul, map_pow] at hf
  rw [div_pow, ht₀, hf]
  simp only [Units.val_mul, map_mul]
  simp only [map_prod] at hE ⊢
  rw [← mul_assoc, ← mul_assoc, mul_div_cancel_right₀ _ (pow_ne_zero m hE)]
  simp only [mul_assoc]

/-- Division by a fixed base section preserves the scalar of a deck eigenvector. -/
theorem s2v_l1b_div_generator_eigenvalue
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    (φ : K →+* K) (hfix : ∀ f, φ (ρ f) = ρ f)
    (t ξ : K) (ht : φ t = ξ * t) (a : R) :
    φ (t / ρ a) = ξ * (t / ρ a) := by
  rw [map_div₀, ht, hfix, mul_div_assoc]

/-- The divided generator retains nonvanishing, field generation, and the full exceptional identity. -/
theorem s2v_l1b_div_generator_data
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    {J L : Type*} [Fintype J] [Fintype L]
    (g : J → R) (n : J → ℕ) (eE : L → R)
    (ε₀ δ : Rˣ) (u v : R) (m α : ℕ) (t₀ : K)
    (hE : ρ (∏ j, eE j) ≠ 0) (hne : t₀ ≠ 0)
    (hgen : Subfield.closure (Set.range ρ ∪ {t₀}) = ⊤)
    (ht₀ : t₀ ^ m = ρ (ε₀ : R) * ∏ j, ρ (g j) ^ n j)
    (hfactors : (∏ j, g j ^ n j) =
      (δ : R) * u ^ α * v ^ (m - α) * (∏ j, eE j) ^ m) :
    ∃ t : K, t ≠ 0 ∧ Subfield.closure (Set.range ρ ∪ {t}) = ⊤ ∧
      t ^ m = ρ ((ε₀ * δ : Rˣ) : R) * ρ u ^ α * ρ v ^ (m - α) ∧
      t₀ = t * ρ (∏ j, eE j) := by
  refine ⟨t₀ / ρ (∏ j, eE j), div_ne_zero hne hE, ?_, ?_, ?_⟩
  · rw [s2v_l1b_div_generator_subfield ρ t₀ _ hE, hgen]
  · exact s2v_l1b_exceptional_power_cancel ρ g n eE ε₀ δ u v m α t₀ hE ht₀ hfactors
  · exact (div_mul_cancel₀ t₀ hE).symm

end HodgeLean.Foundations.Program
