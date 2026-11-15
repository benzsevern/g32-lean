import HodgeLean.Foundations.Program.SchoenNormalizedChartLift

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- Normalized evaluation of actual homogeneous fractions commutes with a graded ring map. -/
theorem s2_normalizedChartLift_map {A B C σ τ : Type}
    [CommRing A] [CommRing B] [CommRing C]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) {r : A} {d : ℕ} (hr : r ∈ 𝒜 d)
    (φ : B →+* C) (hφ : φ (f r) = 1) :
    (s2_normalizedChartLift ℬ (f r) φ hφ).comp (Away.map f r) =
      s2_normalizedChartLift 𝒜 r (φ.comp f.toRingHom) hφ := by
  apply RingHom.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hr z
  simp only [RingHom.comp_apply, Away.map_mk f r hr n a ha,
    s2_normalizedChartLift_mk, GradedRingHom.coe_toRingHom]

end HodgeLean.Foundations.Program
