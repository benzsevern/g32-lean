import HodgeLean.Foundations.Program.G32SelectedRealizationMarked

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_transport_lattice_map_preserves {L M L' M' : Type*}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup L'] [AddCommGroup M']
    (eL : L ≃+ L') (eM : M ≃+ M')
    (FL : Submodule ℂ (ℂ ⊗[ℤ] L)) (FM : Submodule ℂ (ℂ ⊗[ℤ] M))
    (FL' : Submodule ℂ (ℂ ⊗[ℤ] L')) (FM' : Submodule ℂ (ℂ ⊗[ℤ] M'))
    (hL : FL.map (b2_cplxMap eL.toAddMonoidHom) = FL')
    (hM : FM.map (b2_cplxMap eM.toAddMonoidHom) = FM')
    (f : L →+ M) (hf : FL ≤ FM.comap (b2_cplxMap f)) :
    FL' ≤ FM'.comap
      (b2_cplxMap (eM.toAddMonoidHom.comp (f.comp eL.symm.toAddMonoidHom))) := by
  let g := eM.toAddMonoidHom.comp (f.comp eL.symm.toAddMonoidHom)
  have hc : b2_cplxMap g ∘ₗ b2_cplxMap eL.toAddMonoidHom =
      b2_cplxMap eM.toAddMonoidHom ∘ₗ b2_cplxMap f := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c l =>
      change c ⊗ₜ[ℤ] eM (f (eL.symm (eL l))) = c ⊗ₜ[ℤ] eM (f l)
      rw [eL.symm_apply_apply]
    | add x y hx hy => simp only [map_add, LinearMap.comp_apply, hx, hy]
  intro x hx
  rw [← hL] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change b2_cplxMap g (b2_cplxMap eL.toAddMonoidHom y) ∈ FM'
  have hh := LinearMap.congr_fun hc y
  simp only [LinearMap.comp_apply] at hh
  rw [hh, ← hM]
  exact Submodule.mem_map_of_mem (hf hy)

end HodgeLean.Foundations.Program
