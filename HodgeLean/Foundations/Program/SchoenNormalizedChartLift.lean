import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- A ring evaluation sending the chart denominator to one evaluates actual homogeneous fractions. -/
def s2_normalizedChartLift {A B σ : Type} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (f : A) (φ : A →+* B) (hφ : φ f = 1) : Away 𝒜 f →+* B :=
  (IsLocalization.Away.lift (S := Localization.Away f) f
    (show IsUnit (φ f) from hφ ▸ isUnit_one)).comp
      (algebraMap (Away 𝒜 f) (Localization.Away f))

/-- Normalized chart evaluation sends every actual homogeneous fraction to its numerator value. -/
theorem s2_normalizedChartLift_mk {A B σ : Type} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (f : A) (φ : A →+* B) (hφ : φ f = 1)
    {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    s2_normalizedChartLift 𝒜 f φ hφ (Away.mk 𝒜 hf n a ha) = φ a := by
  change (IsLocalization.Away.lift (S := Localization.Away f) f
    (show IsUnit (φ f) from hφ ▸ isUnit_one))
      (Localization.mk a ⟨f ^ n, by use n⟩) = φ a
  rw [Localization.mk_eq_mk']
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  change φ a = φ (f ^ n) * φ a
  rw [map_pow, hφ, one_pow, one_mul]

end HodgeLean.Foundations.Program
