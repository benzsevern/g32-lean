import HodgeLean.Foundations.Program.PrymVariationCentreSaturation

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b63d_saturation_complex_range {M : Type} [AddCommGroup M] [Module ℤ M]
    (L : Submodule ℤ M) :
    letI : Module ℤ L := L.module
    letI : Module ℤ (b63l_saturation L) := (b63l_saturation L).module
    LinearMap.range ((b63l_saturation L).subtype.baseChange ℂ) =
      LinearMap.range (L.subtype.baseChange ℂ) := by
  letI : Module ℤ L := L.module
  letI : Module ℤ (b63l_saturation L) := (b63l_saturation L).module
  obtain ⟨E, hE⟩ := b63d_saturation_complex_equiv L
  have h := LinearMap.range_comp_of_range_eq_top
    ((b63l_saturation L).subtype.baseChange ℂ) (LinearMap.range_eq_top.mpr E.surjective)
  rw [hE] at h
  exact h.symm

theorem b63d_saturated_operator_complex_range {M : Type} [AddCommGroup M]
    (f : M →+ M) :
    LinearMap.range ((b63l_saturation f.toIntLinearMap.range).subtype.baseChange ℂ) =
      LinearMap.range (b2_cplxMap f) := by
  let L := f.toIntLinearMap.range
  letI : Module ℤ L := L.module
  letI : Module ℤ (b63l_saturation L) := (b63l_saturation L).module
  rw [b63d_saturation_complex_range]
  ext z
  exact (SetLike.ext_iff.mp (LinearMap.lTensor_range ℂ (g := f.toIntLinearMap)) z).symm

end HodgeLean.Foundations.Program
