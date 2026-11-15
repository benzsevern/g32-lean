import HodgeLean.Foundations.Program.SchoenNormalizedChartNaturality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- Actual normalized homogeneous chart evaluation agrees with ordinary localization pullback after localizing the coefficient ring. -/
theorem s2_normalizedChartLift_toAway {A C σ : Type} [CommRing A] [CommRing C]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {r : A} {d : ℕ} (hr : r ∈ 𝒜 d) (φ : A →+* C) (hφ : φ r = 1) :
    (algebraMap C (Localization.Away (φ r))).comp (s2_normalizedChartLift 𝒜 r φ hφ) =
      (IsLocalization.map (M := Submonoid.powers r) (T := Submonoid.powers (φ r)) _ φ
        (by rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp
          (algebraMap (Away 𝒜 r) (Localization.Away r)) := by
  apply RingHom.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hr z
  rw [RingHom.comp_apply, s2_normalizedChartLift_mk, RingHom.comp_apply]
  change algebraMap C (Localization.Away (φ r)) (φ a) =
    (IsLocalization.map (M := Submonoid.powers r) (T := Submonoid.powers (φ r)) _ φ
      (by rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]))
        (Localization.mk a (⟨r ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers r) : Localization.Away r)
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']
  symm
  apply (IsLocalization.mk'_eq_iff_eq_mul (M := Submonoid.powers (φ r))).mpr
  change algebraMap C (Localization.Away (φ r)) (φ a) =
    algebraMap C (Localization.Away (φ r)) (φ a) * algebraMap C (Localization.Away (φ r)) (φ (r ^ n))
  have hden : φ (r ^ n) = 1 := by rw [map_pow, hφ, one_pow]
  rw [hden, map_one, mul_one]

end HodgeLean.Foundations.Program
