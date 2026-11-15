import HodgeLean.Foundations.Curves.AbelTheorem.ComplexMultiplierRegularity

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

theorem projected_scalar_differential_apply (h : Module.finrank ℂ E = 1)
    (G : C → ℂ) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G)
    (P : ℂ →L[ℝ] ℝ) (x : C) (z : ℂ) :
    b3Forms_d (b3Forms_fun (E := E) (fun y => P (G y))) x
      (fun _ => b4cov_lineEquiv h z) =
      P (fderiv ℝ (centeredScalar h G x) 0 z) := by
  let L := b4cov_lineEquiv h
  let A : ℂ → E := fun u => chartAt E x x + L u
  let F : E → ℂ := G ∘ (chartAt E x).symm
  have hF : DifferentiableAt ℝ F (chartAt E x x) :=
    ((hG.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x))).contDiffOn.contDiffAt
      ((chartAt E x).open_target.mem_nhds ((chartAt E x).map_source (mem_chart_source E x)))).differentiableAt
        (by simp)
  have hA : HasFDerivAt A (L.toContinuousLinearMap.restrictScalars ℝ) 0 :=
    (L.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.const_add _
  have hF' : HasFDerivAt F (fderiv ℝ F (chartAt E x x)) (A 0) := by
    simpa only [A, _root_.map_zero, add_zero] using hF.hasFDerivAt
  have hc := hF'.comp 0 hA
  have hp := P.hasFDerivAt.comp (chartAt E x x) hF.hasFDerivAt
  rw [b3Forms_d_fun, ofSubsingleton_apply_apply]
  change fderiv ℝ (P ∘ F) (chartAt E x x) (L z) = P (fderiv ℝ (F ∘ A) 0 z)
  rw [hp.fderiv, hc.fderiv]
  rfl

end HodgeLean.Foundations.Curves.AbelTheorem
