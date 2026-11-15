import HodgeLean.Foundations.Program.PrymVariationCentreSaturation
import HodgeLean.Foundations.Program.PrymVariationCentrePeriodRepresentation

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b63d_saturated_image_filtration_rank {M : Type} [AddCommGroup M]
    (f : M →+ M) (F : Submodule ℂ (ℂ ⊗[ℤ] M)) :
    Module.finrank ℂ (F.comap ((b63l_saturation f.toIntLinearMap.range).subtype.baseChange ℂ)) =
      Module.finrank ℂ (b2_imageF F f) := by
  let L := f.toIntLinearMap.range
  letI : Module ℤ L := L.module
  letI : Module ℤ (b63l_saturation L) := (b63l_saturation L).module
  obtain ⟨E, hE⟩ := b63d_saturation_complex_equiv L
  let e0 : f.range ≃ₗ[ℤ] L := (AddEquiv.refl f.range).toIntLinearEquiv
  let e := (LinearEquiv.baseChange ℤ ℂ _ _ e0).trans E
  have he : (b63l_saturation L).subtype.baseChange ℂ ∘ₗ e.toLinearMap =
      b2_cplxMap f.range.subtype := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      change (b63l_saturation L).subtype.baseChange ℂ (E (c ⊗ₜ[ℤ] e0 x)) = _
      have h := congrArg (fun A : (ℂ ⊗[ℤ] L) →ₗ[ℂ] (ℂ ⊗[ℤ] M) ↦ A (c ⊗ₜ[ℤ] e0 x)) hE
      exact h
    | add x y hx hy => simp only [map_add, LinearMap.comp_apply, hx, hy]
  let P := F.comap ((b63l_saturation L).subtype.baseChange ℂ)
  have hc : P.comap e.toLinearMap = b2_imageF F f := by
    change (F.comap ((b63l_saturation L).subtype.baseChange ℂ)).comap e.toLinearMap = _
    rw [← Submodule.comap_comp, he]
    rfl
  have hr := (Submodule.comap_equiv_self_of_inj_of_le (p := P) e.injective
    (by rw [LinearMap.range_eq_top.mpr e.surjective]; exact le_top)).finrank_eq
  rw [hc] at hr
  exact hr.symm

end HodgeLean.Foundations.Program
