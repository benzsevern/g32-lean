import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.ExponentialPrimitiveDerivative
import HodgeLean.Foundations.Program.RiemannRoch

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Forster, Lectures on Riemann Surfaces, §§9, 10, agreement of the centered line coefficient models. -/
theorem discCoefficient_lineEquiv
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (h : Module.finrank ℂ E = 1) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (x : C) :
    b3A_discCoef θ x (b4cov_lineEquiv h 1) =ᶠ[𝓝 0] HurwitzPrymRR_loc h θ x := by
  let L := b4cov_lineEquiv h
  have hcoord (z : ℂ) : z • L 1 = L z := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hcont : Continuous (fun z : ℂ => extChartAt 𝓘(ℂ, E) x x + L z) :=
    continuous_const.add L.continuous
  have ht : ∀ᶠ z in 𝓝 (0 : ℂ), extChartAt 𝓘(ℂ, E) x x + L z ∈
      (extChartAt 𝓘(ℂ, E) x).target :=
    hcont.continuousAt.preimage_mem_nhds (by
      simpa only [map_zero, add_zero] using
        (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  filter_upwards [ht] with z hz
  have hy := (extChartAt 𝓘(ℂ, E) x).map_target hz
  have hb := b4cov_mem_baseSet x _ hy
  have hd : b3A_disc x (L 1) z = (extChartAt 𝓘(ℂ, E) x).symm
      (extChartAt 𝓘(ℂ, E) x x + L z) := by
    change (chartAt E x).symm (chartAt E x x + z • L 1) = _
    rw [hcoord]
    rfl
  change b3A_discCoef θ x (L 1) z = HurwitzPrymRR_loc h θ x z
  simp only [b3A_discCoef, b3A_coef, b3A_frame, HurwitzPrymRR_loc, b4cov_coef, b4cov_vec]
  rw [hd, Bundle.Trivialization.symmL_apply _ hb]

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
