import HodgeLean.Foundations.Program.MilneTensorCovarianceCoordinates
import Mathlib.LinearAlgebra.Multilinear.Pi

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def m1b_rankOneForm : MultilinearMap ℂ (fun _ : Fin 2 => ι → ℂ) (ι × ι → ℂ) :=
  MultilinearMap.pi fun ij =>
    (MultilinearMap.mkPiAlgebra ℂ (Fin 2) ℂ).compLinearMap
      (fun s => LinearMap.proj (if s = 0 then ij.1 else ij.2))

theorem m1b_rankOneForm_apply (v : Fin 2 → ι → ℂ) (i j : ι) :
    m1b_rankOneForm v (i, j) = v 0 i * v 1 j := by
  simp [m1b_rankOneForm, Fin.prod_univ_two]

end HodgeLean.Foundations.Program
