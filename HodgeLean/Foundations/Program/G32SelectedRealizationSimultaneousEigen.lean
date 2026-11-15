import HodgeLean.Foundations.Program.G32SelectedRealizationEigenImage

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_simultaneous_eigenspace_equiv {K U V I : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (e : U ≃ₗ[K] V) (A : I → Module.End K U) (B : I → Module.End K V)
    (h : ∀ i, e.toLinearMap ∘ₗ A i = B i ∘ₗ e.toLinearMap) (μ : I → K) :
    (⨅ i, Module.End.eigenspace (A i) (μ i)).map e.toLinearMap =
      ⨅ i, Module.End.eigenspace (B i) (μ i) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro i
    apply Module.End.mem_eigenspace_iff.mpr
    have he := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hu i)
    have hh := LinearMap.congr_fun (h i) u
    change e (A i u) = B i (e u) at hh
    change B i (e u) = μ i • e u
    exact hh.symm.trans ((congrArg e he).trans (map_smul e (μ i) u))
  · intro v hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    apply (Submodule.mem_iInf _).mpr
    intro i
    apply Module.End.mem_eigenspace_iff.mpr
    apply e.injective
    rw [map_smul, e.apply_symm_apply]
    have he := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i)
    exact (LinearMap.congr_fun (h i) (e.symm v)).trans (by
      change B i (e (e.symm v)) = μ i • v
      rw [e.apply_symm_apply]
      exact he)

end HodgeLean.Foundations.Program
