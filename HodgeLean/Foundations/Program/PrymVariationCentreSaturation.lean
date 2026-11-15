import HodgeLean.Foundations.Program.PrymVariationCentreIsotypic

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b63d_le_saturation {R M : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (L : Submodule R M) : L ≤ b63l_saturation L :=
  fun x hx ↦ ⟨1, one_ne_zero, by simpa only [one_smul] using hx⟩

theorem b63d_saturation_complex_surjective {M : Type} [AddCommGroup M] [Module ℤ M]
    (L : Submodule ℤ M) :
    letI : Module ℤ L := L.module
    letI : Module ℤ (b63l_saturation L) := (b63l_saturation L).module
    let hL : L ≤ b63l_saturation L := b63d_le_saturation L
    Function.Surjective ((Submodule.inclusion hL).baseChange ℂ) := by
  letI : Module ℤ L := L.module
  letI : Module ℤ (b63l_saturation L) := (b63l_saturation L).module
  let hL : L ≤ b63l_saturation L := b63d_le_saturation L
  let i := Submodule.inclusion hL
  change Function.Surjective (i.baseChange ℂ)
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    obtain ⟨n, hn, hx⟩ := x.property
    let y : L := ⟨(inferInstance : Module ℤ M).smul n x.val, hx⟩
    have hy : i y = (inferInstance : Module ℤ (b63l_saturation L)).smul n x := Subtype.ext rfl
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    refine ⟨(n : ℂ)⁻¹ • (c ⊗ₜ[ℤ] y), ?_⟩
    rw [map_smul]
    change (n : ℂ)⁻¹ • (c ⊗ₜ[ℤ] i y) = c ⊗ₜ[ℤ] x
    rw [hy]
    have hs : c ⊗ₜ[ℤ] ((inferInstance : Module ℤ (b63l_saturation L)).smul n x) = (n : ℂ) • (c ⊗ₜ[ℤ] x) := by
      rw [int_smul_eq_zsmul (inferInstance : Module ℤ (b63l_saturation L))]
      calc
        c ⊗ₜ[ℤ] (n • x) = n • (c ⊗ₜ[ℤ] x) :=
          map_zsmul (TensorProduct.mk ℤ ℂ (b63l_saturation L) c) n x
        _ = (n : ℂ) • (c ⊗ₜ[ℤ] x) := (Int.cast_smul_eq_zsmul ℂ n _).symm
    rw [hs, inv_smul_smul₀ hnC]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv]⟩

theorem b63d_saturation_complex_equiv {M : Type} [AddCommGroup M] [Module ℤ M]
    (L : Submodule ℤ M) :
    letI : Module ℤ L := L.module
    letI : Module ℤ (b63l_saturation L) := (b63l_saturation L).module
    ∃ E : (ℂ ⊗[ℤ] L) ≃ₗ[ℂ] (ℂ ⊗[ℤ] b63l_saturation L),
      (b63l_saturation L).subtype.baseChange ℂ ∘ₗ E.toLinearMap = L.subtype.baseChange ℂ := by
  letI : Module ℤ L := L.module
  letI : Module ℤ (b63l_saturation L) := (b63l_saturation L).module
  let hL : L ≤ b63l_saturation L := b63d_le_saturation L
  let i := Submodule.inclusion hL
  have hi : Function.Injective (i.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap i (Submodule.inclusion_injective hL)
  let E := LinearEquiv.ofBijective (i.baseChange ℂ)
    ⟨hi, b63d_saturation_complex_surjective L⟩
  refine ⟨E, ?_⟩
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply, hx, hy]

end HodgeLean.Foundations.Program
