import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.DiscCoefficientComparison
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.OpenDifferentialCoefficients
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.PuncturedExponentialPrimitive

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Forster, Lectures on Riemann Surfaces, §§9, 10, the ambient logarithmic derivative of a punctured primitive. -/
theorem puncturedPrimitive_ambient_derivative
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]
    (h : Module.finrank ℂ E = 1) (D : C →₀ ℤ) [ConnectedSpace (divisorComplement D)]
    (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (p : divisorComplement D) (F : divisorComplement D → ℂ)
    (hF : ∀ (q : divisorComplement D) (γ : ℝ → divisorComplement D),
      b3A_IsGoodPath (E := E) γ p q →
        F q = Complex.exp (b3_pathIntegral E (divisorComplement D) γ
          (divisorDifferentialRestriction h D w ha)))
    (f : C → ℂ) (hf : ∀ x : divisorComplement D, f x.val = F x)
    (x : divisorComplement D) :
    HasDerivAt (fun z : ℂ => f ((extChartAt 𝓘(ℂ, E) (x : C)).symm
      (extChartAt 𝓘(ℂ, E) (x : C) (x : C) + b4cov_lineEquiv h z)))
      (HurwitzPrymRR_loc h w (x : C) 0 * f x.val) 0 := by
  let U := divisorComplement D
  let θ := divisorDifferentialRestriction h D w ha
  let L := b4cov_lineEquiv h
  let κ := L.symm.toContinuousLinearMap
  have hκ (v : E) : v = κ v • L 1 := by
    change v = L.symm v • L 1
    rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
  have hκ1 : κ (L 1) = 1 := L.symm_apply_apply 1
  have hu : L 1 ≠ 0 := by
    intro he
    exact one_ne_zero (L.injective (he.trans L.map_zero.symm))
  have hd := exponentialPrimitive_disc_derivative θ p F hF κ (L 1) hκ hκ1 hu x
  have hco := (discCoefficient_lineEquiv h (θ : TangentBundle 𝓘(ℂ, E) U → ℂ) x).trans
    (openRestriction_local_coefficient h U w w.property.1 x)
  have hc0 : b3A_discCoef θ x (L 1) 0 = HurwitzPrymRR_loc h w (x : C) 0 :=
    hco.eq_of_nhds
  rw [hc0] at hd
  have hcoord (z : ℂ) : z • L 1 = L z := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hcont : Continuous (fun z : ℂ => chartAt E (x : C) (x : C) + z • L 1) := by
    fun_prop
  have hmap : Tendsto (fun z : ℂ => chartAt E (x : C) (x : C) + z • L 1)
      (𝓝 0) (𝓝 (chartAt E (x : C) (x : C))) := by
    simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := 0)).tendsto
  have hv := U.chartAt_subtype_val_symm_eventuallyEq (H := E) (x := x)
  have he : (fun z : ℂ => f ((extChartAt 𝓘(ℂ, E) (x : C)).symm
      (extChartAt 𝓘(ℂ, E) (x : C) (x : C) + L z))) =ᶠ[𝓝 0]
      (fun z => F (b3A_disc x (L 1) z)) := by
    filter_upwards [hmap hv] with z hz
    change f ((chartAt E (x : C)).symm (chartAt E (x : C) (x : C) + L z)) = _
    rw [← hcoord z, hz]
    exact hf _
  simpa only [← hf x, mul_comm] using hd.congr_of_eventuallyEq he

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
