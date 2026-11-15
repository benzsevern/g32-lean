import HodgeLean.Foundations.Curves.AbelTheorem.ComplexMultiplierWedge

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

/-- Source: Farkas–Kra, Riemann Surfaces, III.2, wedge products of complex differentials on a curve. -/
theorem complex_linear_wedge_zero (h : Module.finrank ℂ E = 1)
    (θ ψ : TangentBundle 𝓘(ℂ, E) C → ℂ)
    (hθ : HurwitzPrymRR_IsLinear θ) (hψ : HurwitzPrymRR_IsLinear ψ)
    (P : ℂ →L[ℝ] ℝ) :
    b3Forms_wedgeForm (b4c_residue_realForm h θ Complex.reCLM) (b4c_residue_realForm h ψ P) +
      b3Forms_wedgeForm (b4c_residue_realForm h θ Complex.imCLM)
        (b4c_residue_realForm h ψ (P.comp (ContinuousLinearMap.mul ℝ ℂ Complex.I))) = 0 := by
  funext x
  let α := (b3Forms_wedgeForm (b4c_residue_realForm h θ Complex.reCLM) (b4c_residue_realForm h ψ P) +
    b3Forms_wedgeForm (b4c_residue_realForm h θ Complex.imCLM)
      (b4c_residue_realForm h ψ (P.comp (ContinuousLinearMap.mul ℝ ℂ Complex.I)))) x
  let A := θ ⟨x, b4cov_lineEquiv h 1⟩
  let W := ψ ⟨x, b4cov_lineEquiv h 1⟩
  have hI (χ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hχ : HurwitzPrymRR_IsLinear χ) :
      χ ⟨x, b4cov_lineEquiv h Complex.I⟩ = Complex.I * χ ⟨x, b4cov_lineEquiv h 1⟩ := by
    have he := b4c_residue_linear_value h χ hχ x (b4cov_lineEquiv h Complex.I)
    rw [ContinuousLinearEquiv.symm_apply_apply] at he
    exact he.trans (mul_comm _ _)
  have hb : α (b4c_residue_basis h) = 0 := by
    rw [b4c_residue_basis_coe]
    simp only [α, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      b3Forms_wedgeForm, b3Forms_wedge_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    simp only [b4c_residue_realForm_apply h θ hθ, b4c_residue_realForm_apply h ψ hψ,
      hI θ hθ, hI ψ hψ]
    change A.re * P (Complex.I * W) - (Complex.I * A).re * P W +
      (A.im * P (Complex.I * (Complex.I * W)) - (Complex.I * A).im * P (Complex.I * W)) = 0
    have hII : Complex.I * (Complex.I * W) = -W := by rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [hII, map_neg]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add]
    ring
  have hz := (α.toAlternatingMap.map_basis_eq_zero_iff (b4c_residue_basis h)).mp hb
  ext v
  exact congrArg (fun f : E [⋀^Fin 2]→ₗ[ℝ] ℝ => f v) hz

end HodgeLean.Foundations.Curves.AbelTheorem
