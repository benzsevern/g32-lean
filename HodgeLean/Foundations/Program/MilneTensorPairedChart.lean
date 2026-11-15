import HodgeLean.Foundations.Program.MilneTensorSplitPolynomial
import HodgeLean.Foundations.Program.MilneTensorFormOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

def m1b_blockShearEquiv (b : W →ₗ[ℂ] U) : (U × W) ≃ₗ[ℂ] (U × W) where
  toFun v := (v.1 + b v.2, v.2)
  invFun v := (v.1 - b v.2, v.2)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' x y := by ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' a x := by ext <;> simp [smul_add]

def m1b_pairScaleEquiv (a : ℂˣ) : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearEquiv.piCongrRight (fun i : Fin 2 =>
    LinearEquiv.smulOfUnit (if i = 0 then a else 1))

def m1b_pairChartEquiv (a : ℂˣ) (b : W →ₗ[ℂ] (Fin 2 → ℂ)) (e : W ≃ₗ[ℂ] W) :
    ((Fin 2 → ℂ) × W) ≃ₗ[ℂ] ((Fin 2 → ℂ) × W) :=
  (m1b_blockShearEquiv b).trans ((m1b_pairScaleEquiv a).prodCongr e.symm)

end HodgeLean.Foundations.Program
