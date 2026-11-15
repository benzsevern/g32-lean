import HodgeLean.Foundations.Program.MilneTensorPairing

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_tensorFunction_adjoint (B : LinearMap.BilinForm ℂ V) (n : ℕ)
    (u w : Module.End ℂ V) (huw : ∀ x y, B (u x) y = B x (w y))
    (t : ⨂[ℂ]^n V) (v : Fin n → V) :
    m1b_tensorFunction B n (SchurWeyl.tensorPow (Fin n) u t) v =
      m1b_tensorFunction B n t (fun i => w (v i)) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, MultilinearMap.smul_apply, SchurWeyl.tensorPow_tprod,
      m1b_tensorFunction_apply, m1b_tensorBilin_tprod, huw]
  | add x y hx hy =>
    simp only [map_add, MultilinearMap.add_apply, hx, hy]

end HodgeLean.Foundations.Program
