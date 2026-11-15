import HodgeLean.Foundations.Program.G32Native.EulerModel.GlobalNormalChart
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # The derivative of the global section at its projective zero -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators ComplexConjugate
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The Hermitian normalization factor is differentiable at the projective base point. -/
theorem normalChartScalar_differentiable (k : ℕ) :
    DifferentiableAt ℝ (fun z : Fin k → ℂ => (normalLengthSq k (1, z) : ℂ)⁻¹) 0 := by
  have hd : DifferentiableAt ℝ (fun z : Fin k → ℂ => (normalLengthSq k (1, z) : ℂ)) 0 := by
    apply Complex.ofRealCLM.differentiableAt.comp
    simp only [Complex.normSq_apply]
    apply DifferentiableAt.add (differentiableAt_const _)
    have hs : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (fun z : Fin k → ℂ => (z i).re * (z i).re + (z i).im * (z i).im) 0 := by
      intro i hi
      apply DifferentiableAt.add
      · apply DifferentiableAt.mul <;> exact Complex.reCLM.differentiableAt.comp _ (differentiableAt_apply i 0)
      · apply DifferentiableAt.mul <;> exact Complex.imCLM.differentiableAt.comp _ (differentiableAt_apply i 0)
    exact DifferentiableAt.fun_sum hs
  exact hd.inv (by simp [normalLengthSq])

#print axioms normalChartScalar_differentiable

/-- The global section has the signed conjugation derivative in its kernel chart at zero. -/
theorem projectiveNormalSection_chart_fderiv (k : ℕ) :
    fderiv ℝ (fun z : Fin k → ℂ =>
      (projectiveNormalSectionVector k (normalProjectiveChart k z)).2) 0 =
      (-normalConjugation k).toContinuousLinearMap := by
  have he : (fun z : Fin k → ℂ =>
      (projectiveNormalSectionVector k (normalProjectiveChart k z)).2) =
      (fun z => (normalLengthSq k (1, z) : ℂ)⁻¹ • (-normalConjugation k z)) :=
    funext (projectiveNormalSectionVector_chart k)
  rw [he]
  have hg : DifferentiableAt ℝ (fun z => -normalConjugation k z) 0 :=
    (-normalConjugation k).toContinuousLinearMap.differentiableAt
  rw [fderiv_fun_smul (normalChartScalar_differentiable k) hg]
  simp [normalLengthSq]
  exact (normalConjugation k).toContinuousLinearMap.fderiv

#print axioms projectiveNormalSection_chart_fderiv

/-- The real determinant of the global section derivative has the required parity sign. -/
theorem projectiveNormalSection_chart_derivative_det (k : ℕ) :
    LinearMap.det (fderiv ℝ (fun z : Fin k → ℂ =>
      (projectiveNormalSectionVector k (normalProjectiveChart k z)).2) 0).toLinearMap =
      (-1 : ℝ) ^ k := by
  rw [projectiveNormalSection_chart_fderiv]
  exact neg_normalConjugation_det k

#print axioms projectiveNormalSection_chart_derivative_det
end HodgeLean.Foundations.Program.G32Native.EulerModel
