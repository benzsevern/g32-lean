import HodgeLean.Foundations.Program.MilneTensorIntertwining

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_tensorMap_fixed (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (n : ℕ) (f : Fin n → V →ₗ[ℂ] W)
    (hf : ∀ u ∈ T, ∃ v ∈ S, ∀ i, u.comp (f i) = (f i).comp v)
    (t : ⨂[ℂ]^n V) (ht : t ∈ m1b_fixed S n) :
    PiTensorProduct.map f t ∈ m1b_fixed T n := by
  have hfixed : ∀ v ∈ S, SchurWeyl.tensorPow (Fin n) v t = t := by
    simpa only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using ht
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro u hu
  obtain ⟨v, hv, hfv⟩ := hf u hu
  exact (LinearMap.congr_fun (m1b_tensorMap_intertwines n f u v hfv) t).trans
    (congrArg (PiTensorProduct.map f) (hfixed v hv))

end HodgeLean.Foundations.Program
