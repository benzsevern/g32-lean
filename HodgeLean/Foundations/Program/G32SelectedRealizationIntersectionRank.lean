import HodgeLean.Foundations.Program.G32SelectedRealizationEigenImage

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_intersection_finrank_image {K U V : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (f : U →ₗ[K] V) (hf : Function.Injective f)
    (A : Submodule K U) (B : Submodule K V) :
    Module.finrank K ↥(A ⊓ B.comap f) = Module.finrank K ↥(A.map f ⊓ B) := by
  rw [Submodule.map_inf_eq_map_inf_comap]
  exact (Submodule.equivMapOfInjective f hf (A ⊓ B.comap f)).finrank_eq

end HodgeLean.Foundations.Program
