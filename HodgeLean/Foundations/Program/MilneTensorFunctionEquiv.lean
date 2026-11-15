import HodgeLean.Foundations.Program.MilneTensorPairing

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def m1b_tensorFunctionEquiv (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (n : ℕ) :
    (⨂[ℂ]^n V) ≃ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  LinearEquiv.ofBijective (m1b_tensorFunction B n) (m1b_tensorFunction_bijective B hB n)

end HodgeLean.Foundations.Program
