import HodgeLean.Foundations.Program.G32SelectedRealizationEigenGenerator

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_eigenspace_image {K U V : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (f : U →ₗ[K] V) (hf : Function.Injective f)
    (A : Module.End K U) (B : Module.End K V) (h : f ∘ₗ A = B ∘ₗ f) (μ : K) :
    (Module.End.eigenspace A μ).map f =
      Module.End.eigenspace B μ ⊓ LinearMap.range f := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_inf, Module.End.mem_eigenspace_iff,
    LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, u, rfl⟩
    have hh := LinearMap.congr_fun h u
    change f (A u) = B (f u) at hh
    rw [← hh, hu, map_smul]
  · rintro ⟨hx, u, rfl⟩
    refine ⟨u, ?_, rfl⟩
    apply hf
    rw [map_smul]
    exact (LinearMap.congr_fun h u).trans hx

end HodgeLean.Foundations.Program
