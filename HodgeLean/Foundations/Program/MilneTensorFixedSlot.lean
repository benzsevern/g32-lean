import HodgeLean.Foundations.Program.MilneTensorSlotTransport

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_fixed_reindex_fin {ι : Type*} [Fintype ι]
    (S : Set (Module.End ℂ V)) (k : ℕ) (e : Fin k ≃ ι)
    (x : ⨂[ℂ] _ : ι, V) (hx : ∀ u ∈ S, SchurWeyl.tensorPow ι u x = x) :
    (PiTensorProduct.reindex ℂ (fun _ => V) e).symm x ∈ m1b_fixed S k := by
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro u hu
  rw [PiTensorProduct.reindex_symm, ← m1b_tensorPow_reindex, hx u hu]

end HodgeLean.Foundations.Program
