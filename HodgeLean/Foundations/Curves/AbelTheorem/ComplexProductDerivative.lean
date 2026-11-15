import HodgeLean.Foundations.Curves.AbelTheorem.ComplexMultiplierWedge
import HodgeLean.Foundations.Curves.AbelTheorem.ComplexProductProjection

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

theorem projected_complex_product_derivative (h : Module.finrank ℂ E = 1)
    (G : C → ℂ) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (hs : ∀ x, ContDiffAt ℝ ∞ (HurwitzPrymRR_loc h θ x) 0) (P : ℂ →L[ℝ] ℝ) :
    b3Forms_d (b4c_residue_realForm h (fun v => G v.proj * θ v) P) =
      complex_multiplier_wedge h G θ P +
      b3Forms_smulFun (fun x => (G x).re) (b3Forms_d (b4c_residue_realForm h θ P)) +
      b3Forms_smulFun (fun x => (G x).im)
        (b3Forms_d (b4c_residue_realForm h θ (P.comp (ContinuousLinearMap.mul ℝ ℂ Complex.I)))) := by
  have hgr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => (G x).re) :=
    Complex.reCLM.contDiff.contMDiff.comp hG
  have hgi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => (G x).im) :=
    Complex.imCLM.contDiff.contMDiff.comp hG
  have hα (Q : ℂ →L[ℝ] ℝ) := b4c_residue_realForm_smooth h θ hθ Q hs
  rw [projected_complex_product, b3Forms_d_add ((hα P).smulFun hgr) ((hα _).smulFun hgi),
    b3Forms_d_smulFun (b3Forms_isSmooth_fun hgr) (hα P),
    b3Forms_d_smulFun (b3Forms_isSmooth_fun hgi) (hα _)]
  unfold complex_multiplier_wedge
  abel

end HodgeLean.Foundations.Curves.AbelTheorem
