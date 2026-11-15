import HodgeLean.Foundations.Program.PrymVariationFramesDefs

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem b63e_conjSubmodule_map {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃ₗ[ℤ] N) (F : Submodule ℂ (ℂ ⊗[ℤ] M)) :
    (b2_conjSubmodule M F).map (e.toLinearMap.baseChange ℂ) =
      b2_conjSubmodule N (F.map (e.toLinearMap.baseChange ℂ)) := by
  unfold b2_conjSubmodule
  rw [Submodule.map_span]
  congr 1
  rw [Set.image_image]
  change (fun x ↦ b2_cplxMap e.toAddMonoidHom (b2_conj M x)) '' (F : Set _) = _
  simp_rw [← b2a_conj_cplxMap]
  rw [← Set.image_image]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem b63e_weightOne_comap {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃ₗ[ℤ] N) (F : Submodule ℂ (ℂ ⊗[ℤ] N)) (hF : b2_IsWeightOne N F) :
    b2_IsWeightOne M (F.comap (e.toLinearMap.baseChange ℂ)) := by
  have h := Submodule.isCompl_map (e.baseChange ℤ ℂ).symm hF
  change IsCompl _ _ at h ⊢
  have hc := b63e_conjSubmodule_map e.symm F
  rw [← LinearEquiv.coe_baseChange, LinearEquiv.baseChange_symm] at hc
  rw [hc] at h
  simpa only [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm, LinearEquiv.coe_baseChange] using h

set_option backward.isDefEq.respectTransparency false in
theorem b63e_riemann_comap {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃ₗ[ℤ] N) (F : Submodule ℂ (ℂ ⊗[ℤ] N)) (Q : LinearMap.BilinForm ℤ N)
    (hQ : b2_IsRiemannForm N F Q) :
    b2_IsRiemannForm M (F.comap (e.toLinearMap.baseChange ℂ))
      (Q.compl₁₂ e.toLinearMap e.toLinearMap) := by
  have he : e.toAddMonoidHom.toIntLinearMap = e.toLinearMap := by ext; rfl
  have hb (x y : ℂ ⊗[ℤ] M) :
      LinearMap.BilinForm.baseChange ℂ (Q.compl₁₂ e.toLinearMap e.toLinearMap) x y =
        Q.baseChange ℂ (b2_cplxMap e.toAddMonoidHom x) (b2_cplxMap e.toAddMonoidHom y) := by
    simpa only [he] using b2a_baseChange_compl Q e.toAddMonoidHom x y
  refine ⟨fun x ↦ hQ.alt (e x), ?_, ?_⟩
  · intro x hx y hy
    rw [hb]
    exact hQ.isotropic _ hx _ hy
  · intro x hx hx0
    rw [hb, ← b2a_conj_cplxMap]
    apply hQ.positive _ hx
    exact fun h ↦ hx0 ((e.baseChange ℤ ℂ).injective (h.trans (map_zero _).symm))

end HodgeLean.Foundations.Program
