import HodgeLean.Foundations.Program.SchoenTowerL1bRotationChosenCharacter

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Two nonzero functions with the same character differ by a nonzero base scalar. -/
theorem s2v_l1b_transport_eigenfunction_ratio
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (τ : E ≃ₐ[F] E) (hτ : orderOf τ = Module.finrank F E)
    {t u : E} (ht : t ≠ 0) (hu : u ≠ 0)
    {ξ : E} (hξ : ξ ≠ 0) (htξ : τ t = ξ * t) (huξ : τ u = ξ * u) :
    ∃ c : F, c ≠ 0 ∧ t = algebraMap F E c * u := by
  have htop : Subgroup.zpowers τ = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers τ)).mp
    rw [Nat.card_zpowers, hτ, IsGalois.card_aut_eq_finrank]
  have hratio : τ (t / u) = t / u := by
    rw [map_div₀, htξ, huξ, mul_div_mul_left _ _ hξ]
  have hfixed : ∀ σ : E ≃ₐ[F] E, σ (t / u) = t / u := by
    intro σ
    have hmem : σ ∈ Subgroup.zpowers τ := by rw [htop]; trivial
    obtain ⟨n, rfl : τ ^ n = σ⟩ := mem_powers_iff_mem_zpowers.mpr hmem
    clear hmem
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hratio, ih]
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (t / u)).mpr hfixed
  refine ⟨c, ?_, ?_⟩
  · intro hz
    rw [hz, map_zero] at hc
    exact (div_ne_zero ht hu) hc.symm
  · rw [hc, div_mul_cancel₀ _ hu]

/-- The ratio of two functions with the same character has a nonzero domain presentation. -/
theorem s2v_l1b_transport_eigenfunction_fraction
    {R F E : Type*} [CommRing R] [IsDomain R] [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (τ : E ≃ₐ[F] E) (hτ : orderOf τ = Module.finrank F E)
    {t u : E} (ht : t ≠ 0) (hu : u ≠ 0)
    {ξ : E} (hξ : ξ ≠ 0) (htξ : τ t = ξ * t) (huξ : τ u = ξ * u) :
    ∃ c d : R, c ≠ 0 ∧ d ≠ 0 ∧
      t = (algebraMap F E (algebraMap R F c) /
        algebraMap F E (algebraMap R F d)) * u := by
  obtain ⟨v, hv, htv⟩ := s2v_l1b_transport_eigenfunction_ratio τ hτ ht hu hξ htξ huξ
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective R v
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc, map_zero, zero_div] at hcd
    exact hv hcd.symm
  refine ⟨c, d, hc0, hd0, ?_⟩
  rw [← map_div₀, hcd]
  exact htv

end HodgeLean.Foundations.Program
