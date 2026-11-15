import HodgeLean.Foundations.Program.SchoenRescaledProjections
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- A fraction homogeneous for rescaled degrees is an actual fraction for the original grading. -/
def s2_rescaledLocalizationFun {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] (M : Submonoid A)
    (z : HomogeneousLocalization (fun n => 𝒜 (D * n)) M) : HomogeneousLocalization 𝒜 M :=
  mk ⟨D * z.deg, ⟨z.num, z.num_mem_deg⟩, ⟨z.den, z.den_mem_deg⟩, z.den_mem⟩

/-- The rescaling comparison preserves the actual ordinary localization value. -/
theorem s2_rescaledLocalizationFun_val {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] (M : Submonoid A)
    (z : HomogeneousLocalization (fun n => 𝒜 (D * n)) M) :
    (s2_rescaledLocalizationFun 𝒜 D M z).val = z.val :=
  z.eq_num_div_den.symm

/-- The actual rescaled fraction comparison is a ring homomorphism. -/
def s2_rescaledLocalizationHom {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] (M : Submonoid A) :
    HomogeneousLocalization (fun n => 𝒜 (D * n)) M →+* HomogeneousLocalization 𝒜 M where
  toFun := s2_rescaledLocalizationFun 𝒜 D M
  map_one' := by
    apply val_injective
    simp only [s2_rescaledLocalizationFun_val, val_one]
  map_mul' a b := by
    apply val_injective
    simp only [s2_rescaledLocalizationFun_val, val_mul]
  map_zero' := by
    apply val_injective
    simp only [s2_rescaledLocalizationFun_val, val_zero]
  map_add' a b := by
    apply val_injective
    simp only [s2_rescaledLocalizationFun_val, val_add]

/-- The actual rescaling homomorphism keeps the numerator and denominator of each fraction. -/
theorem s2_rescaledLocalizationHom_mk {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] (M : Submonoid A)
    (c : NumDenSameDeg (fun n => 𝒜 (D * n)) M) :
    s2_rescaledLocalizationHom 𝒜 D M (mk c) =
      mk ⟨D * c.deg, c.num, c.den, c.den_mem⟩ := by
  apply val_injective
  exact s2_rescaledLocalizationFun_val 𝒜 D M (mk c)

end HodgeLean.Foundations.Program
