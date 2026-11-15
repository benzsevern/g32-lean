import HodgeLean.Foundations.Curves.AbelTheorem.Defs

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

theorem projected_complex_product (h : Module.finrank ℂ E = 1)
    (G : C → ℂ) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (P : ℂ →L[ℝ] ℝ) :
    b4c_residue_realForm h (fun v => G v.proj * θ v) P =
      b3Forms_smulFun (fun x => (G x).re) (b4c_residue_realForm h θ P) +
      b3Forms_smulFun (fun x => (G x).im)
        (b4c_residue_realForm h θ (P.comp (ContinuousLinearMap.mul ℝ ℂ Complex.I))) := by
  funext x
  ext v
  change P ((G x * θ ⟨x, b4cov_lineEquiv h 1⟩) * (b4cov_lineEquiv h).symm (v 0)) =
    (G x).re * P (θ ⟨x, b4cov_lineEquiv h 1⟩ * (b4cov_lineEquiv h).symm (v 0)) +
      (G x).im * P (Complex.I * (θ ⟨x, b4cov_lineEquiv h 1⟩ * (b4cov_lineEquiv h).symm (v 0)))
  rw [mul_assoc]
  let z := θ ⟨x, b4cov_lineEquiv h 1⟩ * (b4cov_lineEquiv h).symm (v 0)
  have he : G x * z = (G x).re • z + (G x).im • (Complex.I * z) := by
    conv_lhs => rw [← Complex.re_add_im (G x)]
    simp only [Complex.real_smul]
    ring
  rw [he, map_add, map_smul, map_smul]
  rfl

theorem projected_real_product (h : Module.finrank ℂ E = 1)
    (μ : C → ℝ) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (P : ℂ →L[ℝ] ℝ) :
    b4c_residue_realForm h (fun v => (μ v.proj : ℂ) * θ v) P =
      b3Forms_smulFun μ (b4c_residue_realForm h θ P) := by
  funext x
  ext v
  change P (((μ x : ℂ) * θ ⟨x, b4cov_lineEquiv h 1⟩) * (b4cov_lineEquiv h).symm (v 0)) =
    μ x * P (θ ⟨x, b4cov_lineEquiv h 1⟩ * (b4cov_lineEquiv h).symm (v 0))
  rw [mul_assoc, ← Complex.real_smul, map_smul]
  rfl

end HodgeLean.Foundations.Curves.AbelTheorem
