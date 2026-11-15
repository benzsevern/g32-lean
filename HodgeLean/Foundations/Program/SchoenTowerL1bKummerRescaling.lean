import HodgeLean.Foundations.Program.SchoenTowerL1bKummerMultiplicities
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerCancellation

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Rescaling by a nonzero rational base coefficient preserves the generated subfield. -/
theorem s2v_l1b_rational_rescale_subfield
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    (t : K) (c d : R) (hc : ρ c ≠ 0) (hd : ρ d ≠ 0) :
    Subfield.closure (Set.range ρ ∪ {t * ρ d / ρ c}) =
      Subfield.closure (Set.range ρ ∪ {t}) := by
  rw [s2v_l1b_div_generator_subfield ρ (t * ρ d) c hc]
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro z (hz | hz)
    · exact Subfield.subset_closure (Or.inl hz)
    · rw [Set.mem_singleton_iff] at hz
      subst z
      exact Subfield.mul_mem _ (Subfield.subset_closure (Or.inr rfl))
        (Subfield.subset_closure (Or.inl ⟨d, rfl⟩))
  · apply Subfield.closure_le.mpr
    rintro z (hz | hz)
    · exact Subfield.subset_closure (Or.inl hz)
    · rw [Set.mem_singleton_iff] at hz
      subst z
      have ht := Subfield.div_mem (Subfield.closure (Set.range ρ ∪ {t * ρ d}))
        (Subfield.subset_closure (Or.inr (Set.mem_singleton _)))
        (Subfield.subset_closure (Or.inl ⟨d, rfl⟩))
      rwa [mul_div_cancel_right₀ t hd] at ht

/-- Correcting numerator and denominator orders by powers gives a regular weighted equation. -/
theorem s2v_l1b_branch_equation_after_rescaling
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field K]
    (ρ : R →+* K) {J : Type*} [Fintype J] (g : J → R) (n : J → ℕ)
    (a b c d : R) (m : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hg : ∀ j, g j ≠ 0) (hρb : ρ b ≠ 0) (hρc : ρ c ≠ 0) (hρd : ρ d ≠ 0)
    (hv : ∀ p : R, Prime p →
      emultiplicity p a + (m : ℕ∞) * emultiplicity p d =
      emultiplicity p b + (m : ℕ∞) * emultiplicity p c +
        ∑ j, (n j : ℕ∞) * emultiplicity p (g j))
    (t : K) (hne : t ≠ 0)
    (hgen : Subfield.closure (Set.range ρ ∪ {t}) = ⊤)
    (ht : t ^ m = ρ a / ρ b) :
    ∃ ε : Rˣ, t * ρ d / ρ c ≠ 0 ∧
      Subfield.closure (Set.range ρ ∪ {t * ρ d / ρ c}) = ⊤ ∧
      (t * ρ d / ρ c) ^ m = ρ (ε : R) * ∏ j, ρ (g j) ^ n j := by
  have hv' (p : R) (hp : Prime p) :
      emultiplicity p (a * d ^ m) = emultiplicity p (b * c ^ m) +
        ∑ j, (n j : ℕ∞) * emultiplicity p (g j) := by
    simpa only [emultiplicity_mul hp, emultiplicity_pow hp] using hv p hp
  have ht' : (t * ρ d / ρ c) ^ m = ρ (a * d ^ m) / ρ (b * c ^ m) := by
    rw [div_pow, mul_pow, ht]
    simp only [map_mul, map_pow]
    rw [div_mul_eq_mul_div, div_div]
  obtain ⟨ε, hε⟩ := s2v_l1b_branch_equation_of_prime_multiplicities ρ g n
    (a * d ^ m) (b * c ^ m) (mul_ne_zero ha (pow_ne_zero _ hd))
    (mul_ne_zero hb (pow_ne_zero _ hc)) hg
    (by simpa only [map_mul, map_pow] using mul_ne_zero hρb (pow_ne_zero m hρc))
    hv' (t * ρ d / ρ c) m ht'
  exact ⟨ε, div_ne_zero (mul_ne_zero hne hρd) hρc,
    (s2v_l1b_rational_rescale_subfield ρ t c d hρc hρd).trans hgen, hε⟩

/-- Rational base rescaling preserves the scalar for the retained field symmetry. -/
theorem s2v_l1b_rational_rescale_eigenvalue
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    (φ : K →+* K) (hfix : ∀ f, φ (ρ f) = ρ f)
    (t ξ : K) (ht : φ t = ξ * t) (c d : R) :
    φ (t * ρ d / ρ c) = ξ * (t * ρ d / ρ c) := by
  rw [map_div₀, map_mul, ht, hfix, hfix, mul_assoc, mul_div_assoc]

end HodgeLean.Foundations.Program
