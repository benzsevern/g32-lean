import HodgeLean.Foundations.Program.MilneTensorPairedChart

noncomputable section
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def m1b_pairForm : LinearMap.BilinForm ℂ (Fin 2 → ℂ) :=
  (LinearMap.mul ℂ ℂ).compl₁₂ (LinearMap.proj 0) (LinearMap.proj 1) -
    (LinearMap.mul ℂ ℂ).compl₁₂ (LinearMap.proj 1) (LinearMap.proj 0)

def m1b_pairCross (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (i : Fin 2) :
    W →ₗ[ℂ] ℂ :=
  (Q (Pi.single i 1, 0)).comp (LinearMap.inr ℂ (Fin 2 → ℂ) W)

def m1b_pairRestriction (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) :
    LinearMap.BilinForm ℂ W :=
  Q.compl₁₂ (LinearMap.inr ℂ (Fin 2 → ℂ) W) (LinearMap.inr ℂ (Fin 2 → ℂ) W)

def m1b_pairShear (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (a : ℂˣ) :
    W →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi (fun i => if i = 0 then -a.inv • m1b_pairCross Q 1
    else a.inv • m1b_pairCross Q 0)

def m1b_pairSchur (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (a : ℂˣ) :
    LinearMap.BilinForm ℂ W :=
  m1b_pairRestriction Q + a.inv •
    ((LinearMap.mul ℂ ℂ).compl₁₂ (m1b_pairCross Q 1) (m1b_pairCross Q 0) -
      (LinearMap.mul ℂ ℂ).compl₁₂ (m1b_pairCross Q 0) (m1b_pairCross Q 1))

end HodgeLean.Foundations.Program
