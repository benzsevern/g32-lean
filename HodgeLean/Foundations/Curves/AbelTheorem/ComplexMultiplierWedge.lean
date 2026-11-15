import HodgeLean.Foundations.Curves.AbelTheorem.ProjectedScalarDerivative
import HodgeLean.Foundations.Curves.AbelTheorem.ComplexProductProjection

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

def complex_multiplier_wedge (h : Module.finrank ℂ E = 1) (G : C → ℂ)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (P : ℂ →L[ℝ] ℝ) :
    C → E [⋀^Fin 2]→L[ℝ] ℝ :=
  b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).re)))
    (b4c_residue_realForm h θ P) +
  b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).im)))
    (b4c_residue_realForm h θ (P.comp (ContinuousLinearMap.mul ℝ ℂ Complex.I)))

theorem complex_multiplier_wedge_zero_of_analytic (h : Module.finrank ℂ E = 1)
    (G : C → ℂ) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (P : ℂ →L[ℝ] ℝ) (x : C) (ha : AnalyticAt ℂ (centeredScalar h G x) 0) :
    complex_multiplier_wedge h G θ P x = 0 := by
  let α := complex_multiplier_wedge h G θ P x
  let A := fderiv ℝ (centeredScalar h G x) 0 1
  let B := fderiv ℝ (centeredScalar h G x) 0 Complex.I
  let W := θ ⟨x, b4cov_lineEquiv h 1⟩
  have hCR : B = Complex.I * A := by
    dsimp only [A, B]
    rw [ha.differentiableAt.fderiv_restrictScalars ℝ]
    change fderiv ℂ (centeredScalar h G x) 0 Complex.I =
      Complex.I * fderiv ℂ (centeredScalar h G x) 0 1
    simpa only [smul_eq_mul, mul_one] using
      (fderiv ℂ (centeredScalar h G x) 0).map_smul Complex.I (1 : ℂ)
  have hI : θ ⟨x, b4cov_lineEquiv h Complex.I⟩ = Complex.I * W := by
    have he := b4c_residue_linear_value h θ hθ x (b4cov_lineEquiv h Complex.I)
    rw [ContinuousLinearEquiv.symm_apply_apply] at he
    exact he.trans (mul_comm _ _)
  have hb : α (b4c_residue_basis h) = 0 := by
    rw [b4c_residue_basis_coe]
    simp only [α, complex_multiplier_wedge, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      b3Forms_wedgeForm, b3Forms_wedge_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have hre (z : ℂ) : b3Forms_d (b3Forms_fun (E := E) (fun y => (G y).re)) x
        (fun _ => b4cov_lineEquiv h z) = (fderiv ℝ (centeredScalar h G x) 0 z).re :=
      projected_scalar_differential_apply h G hG Complex.reCLM x z
    have him (z : ℂ) : b3Forms_d (b3Forms_fun (E := E) (fun y => (G y).im)) x
        (fun _ => b4cov_lineEquiv h z) = (fderiv ℝ (centeredScalar h G x) 0 z).im :=
      projected_scalar_differential_apply h G hG Complex.imCLM x z
    have hev (Q : ℂ →L[ℝ] ℝ) (z : ℂ) :
        b4c_residue_realForm h θ Q x (fun _ => b4cov_lineEquiv h z) =
          Q (θ ⟨x, b4cov_lineEquiv h z⟩) := b4c_residue_realForm_apply h θ hθ Q x _
    rw [hre 1, hre Complex.I, him 1, him Complex.I, hev P 1, hev P Complex.I,
      hev _ 1, hev _ Complex.I, hI]
    change A.re * P (Complex.I * W) - B.re * P W +
      (A.im * P (Complex.I * (Complex.I * W)) - B.im * P (Complex.I * W)) = 0
    have hII : Complex.I * (Complex.I * W) = -W := by rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [hCR, hII, map_neg]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add]
    ring
  have hz := (α.toAlternatingMap.map_basis_eq_zero_iff (b4c_residue_basis h)).mp hb
  ext v
  exact congrArg (fun f : E [⋀^Fin 2]→ₗ[ℝ] ℝ => f v) hz

theorem complex_multiplier_wedge_real_product (h : Module.finrank ℂ E = 1)
    (G : C → ℂ) (μ : C → ℝ) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (P : ℂ →L[ℝ] ℝ) :
    complex_multiplier_wedge h G (fun v => (μ v.proj : ℂ) * θ v) P =
      b3Forms_smulFun μ (complex_multiplier_wedge h G θ P) := by
  unfold complex_multiplier_wedge
  rw [projected_real_product, projected_real_product]
  funext x
  simp only [Pi.add_apply, b3Forms_wedgeForm, b3Forms_smulFun,
    b3Forms_wedge_smul_right, smul_add]

end HodgeLean.Foundations.Curves.AbelTheorem
