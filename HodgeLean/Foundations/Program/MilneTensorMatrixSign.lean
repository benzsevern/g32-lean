import HodgeLean.Foundations.Program.MilneTensorFormOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_matrixForm_transpose_sign (ε : ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.transpose = ε • Q) (x y : ι → ℂ) :
    Q.toBilin' y x = ε * Q.toBilin' x y := by
  have hf : Q.toBilin'.flip = ε • Q.toBilin' := by
    apply (Pi.basisFun ℂ ι).ext
    intro i
    apply (Pi.basisFun ℂ ι).ext
    intro j
    have h := congrFun (congrFun hQ i) j
    simp only [Pi.basisFun_apply]
    change Q.toBilin' (Pi.single j 1) (Pi.single i 1) =
      ε * Q.toBilin' (Pi.single i 1) (Pi.single j 1)
    simpa only [Matrix.toBilin'_single, Matrix.transpose_apply,
      Matrix.smul_apply, smul_eq_mul] using h
  exact LinearMap.congr_fun (LinearMap.congr_fun hf x) y

end HodgeLean.Foundations.Program
