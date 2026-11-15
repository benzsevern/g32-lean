import HodgeLean.Foundations.Program.MilneTensorPairing

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_tensorFunction_pairing_change (B C : LinearMap.BilinForm ℂ V) (n : ℕ)
    (u : Module.End ℂ V) (hu : ∀ x y, C (u x) y = B x y)
    (t : ⨂[ℂ]^n V) :
    m1b_tensorFunction C n (SchurWeyl.tensorPow (Fin n) u t) =
      m1b_tensorFunction B n t := by
  apply MultilinearMap.ext
  intro v
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, MultilinearMap.smul_apply, SchurWeyl.tensorPow_tprod,
      m1b_tensorFunction_apply, m1b_tensorBilin_tprod, hu]
  | add x y hx hy => simp only [map_add, MultilinearMap.add_apply, hx, hy]

end HodgeLean.Foundations.Program
