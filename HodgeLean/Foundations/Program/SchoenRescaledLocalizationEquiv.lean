import HodgeLean.Foundations.Program.SchoenRescaledLocalization
import HodgeLean.Foundations.Program.SchoenRescaledDegreeDivisibility

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- Rescaling is injective on actual homogeneous localization rings. -/
theorem s2_rescaledLocalizationHom_injective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] (M : Submonoid A) :
    Function.Injective (s2_rescaledLocalizationHom 𝒜 D M) := by
  intro a b h
  apply val_injective
  rw [← s2_rescaledLocalizationFun_val 𝒜 D M a, ← s2_rescaledLocalizationFun_val 𝒜 D M b]
  exact congrArg val h

/-- Every actual homogeneous fraction has a rescaled representative when denominators exclude zero. -/
theorem s2_rescaledLocalizationHom_surjective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] (M : Submonoid A) (hM : (0 : A) ∉ M) :
    Function.Surjective (s2_rescaledLocalizationHom 𝒜 D M) := by
  intro z
  have hden : z.den ≠ 0 := fun h => hM (h ▸ z.den_mem)
  obtain ⟨k, hk⟩ := s2_rescaled_degree_dvd_of_ne_zero 𝒜 D z.den_mem_deg hden
  let w : HomogeneousLocalization (fun n => 𝒜 (D * n)) M :=
    mk ⟨k, ⟨z.num, by rw [← hk]; exact z.num_mem_deg⟩,
      ⟨z.den, by rw [← hk]; exact z.den_mem_deg⟩, z.den_mem⟩
  refine ⟨w, ?_⟩
  apply val_injective
  change (s2_rescaledLocalizationFun 𝒜 D M w).val = z.val
  rw [s2_rescaledLocalizationFun_val]
  exact z.eq_num_div_den.symm

/-- Positive degree rescaling identifies actual homogeneous localization rings away from zero. -/
def s2_rescaledLocalizationEquiv {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] (M : Submonoid A) (hM : (0 : A) ∉ M) :
    HomogeneousLocalization (fun n => 𝒜 (D * n)) M ≃+* HomogeneousLocalization 𝒜 M :=
  RingEquiv.ofBijective (s2_rescaledLocalizationHom 𝒜 D M)
    ⟨s2_rescaledLocalizationHom_injective 𝒜 D M,
      s2_rescaledLocalizationHom_surjective 𝒜 D M hM⟩

end HodgeLean.Foundations.Program
