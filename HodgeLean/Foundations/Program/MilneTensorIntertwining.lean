import HodgeLean.Foundations.Program.MilneTensorFamilyMaps

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_tensorMap_intertwines (n : ℕ) (f : Fin n → V →ₗ[ℂ] W)
    (u : Module.End ℂ W) (v : Module.End ℂ V)
    (hf : ∀ i, u.comp (f i) = (f i).comp v) :
    (SchurWeyl.tensorPow (Fin n) u).comp (PiTensorProduct.map f) =
      (PiTensorProduct.map f).comp (SchurWeyl.tensorPow (Fin n) v) := by
  ext x
  change SchurWeyl.tensorPow (Fin n) u (PiTensorProduct.map f (PiTensorProduct.tprod ℂ x)) =
    PiTensorProduct.map f (SchurWeyl.tensorPow (Fin n) v (PiTensorProduct.tprod ℂ x))
  simp only [SchurWeyl.tensorPow_tprod, PiTensorProduct.map_tprod]
  congr 1
  funext i
  exact LinearMap.congr_fun (hf i) (x i)

end HodgeLean.Foundations.Program
