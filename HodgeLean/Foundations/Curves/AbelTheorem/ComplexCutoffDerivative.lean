import HodgeLean.Foundations.Curves.AbelTheorem.ComplexProductDerivative
import HodgeLean.Foundations.Curves.AbelTheorem.ComplexCutoffForm

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem complex_cutoff_derivative_of_constant_germ (h : Module.finrank ℂ E = 1)
    (w : b4c_MeroForm E C h) (G : C → ℂ)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G) (μ : C → ℝ)
    (hμ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ μ)
    (hpoles : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0 < 0 → μ =ᶠ[𝓝 x] 0)
    (P : ℂ →L[ℝ] ℝ) (x : C) (c : ℝ) (hc : μ =ᶠ[𝓝 x] fun _ => c) :
    b3Forms_d (b4c_residue_realForm h
      (fun v => G v.proj * ((μ v.proj : ℂ) * b4c_residue_normalizedForm h w v)) P) x =
      c • complex_multiplier_wedge h G (b4c_residue_normalizedForm h w) P x := by
  let θ : TangentBundle 𝓘(ℂ, E) C → ℂ :=
    fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm h w v
  have hθ : HurwitzPrymRR_IsLinear θ := by
    intro y a v v'
    change (μ y : ℂ) * _ = a * ((μ y : ℂ) * _) + (μ y : ℂ) * _
    rw [b4c_residue_normalizedForm_linear h w]
    ring
  have he := congrFun (projected_complex_product_derivative h G hG θ hθ
    (b4c_residue_cutoff_coefficient_smooth h w μ hμ hpoles) P) x
  rw [show θ = (fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm h w v) from rfl,
    complex_multiplier_wedge_real_product] at he
  simp only [Pi.add_apply, b3Forms_smulFun] at he
  rw [b4c_residue_d_eq_zero_of_constant h w μ hμ hpoles P hc,
    b4c_residue_d_eq_zero_of_constant h w μ hμ hpoles _ hc,
    hc.self_of_nhds, smul_zero, smul_zero, add_zero, add_zero] at he
  exact he

end HodgeLean.Foundations.Curves.AbelTheorem
