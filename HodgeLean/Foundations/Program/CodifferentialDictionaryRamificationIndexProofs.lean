import HodgeLean.Foundations.Program.CodifferentialDictionaryStandardSplittingsProofs

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option maxHeartbeats 400000 in
theorem b66d_ramIndex_of_chart_power {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hnc : ∃ x y, f x ≠ f y) (p : C) (F : ℂ → ℂ) (n : ℕ)
    (hF : AnalyticAt ℂ F (extChartAt 𝓘(ℂ, ℂ) p p))
    (hF0 : F (extChartAt 𝓘(ℂ, ℂ) p p) = 0)
    (hFd : deriv F (extChartAt 𝓘(ℂ, ℂ) p p) ≠ 0)
    (hpow : writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) p f =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) p p)]
      (fun z => writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) p f
        (extChartAt 𝓘(ℂ, ℂ) p p) + F z ^ n)) :
    b4_ramIndex ℂ ℂ f p = n := by
  let α := extChartAt 𝓘(ℂ, ℂ) p p
  let G := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) p f
  let L : ℂ ≃L[ℂ] ℂ := b4cov_lineEquiv (by simp)
  let c : ℂ := L.symm 1
  let K : ℂ → ℂ := fun z => F (α + L z)
  have hc : c ≠ 0 := L.symm.map_ne_zero_iff.mpr one_ne_zero
  have hL : L 1 ≠ 0 := L.map_ne_zero_iff.mpr one_ne_zero
  have hA : HasDerivAt (fun z : ℂ => α + L z) (L 1) 0 :=
    (L.hasFDerivAt.hasDerivAt).const_add α
  have hK : AnalyticAt ℂ K 0 := by
    apply AnalyticAt.comp (by simpa only [map_zero, add_zero] using hF)
    exact analyticAt_const.add (L.toContinuousLinearMap.analyticAt 0)
  have hK0 : K 0 = 0 := by simpa only [K, map_zero, add_zero] using hF0
  have hKd : deriv K 0 ≠ 0 := by
    have hdF : HasDerivAt F (deriv F α) (α + L 0) := by
      simpa only [map_zero, add_zero] using hF.differentiableAt.hasDerivAt
    have hd := hdF.comp 0 hA
    change deriv (F ∘ fun z : ℂ => α + L z) 0 ≠ 0
    rw [hd.deriv]
    exact mul_ne_zero hFd hL
  have hKo : analyticOrderAt K 0 = 1 := hK.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hK0 hKd
  have hG : AnalyticAt ℂ G α :=
    (b4cov_analyticOnNhd f hf p) _ (b4cov_mem_good (E' := ℂ) f p)
  obtain ⟨he, hne, hlow⟩ := b4cov_ramIndex_spec f hf hnc p
  have hT := b4cov_analyticOrderAt_transport (by simp : Module.finrank ℂ ℂ = 1)
    (by simp : Module.finrank ℂ ℂ = 1) hG he hlow hne
  have hmodel : b4cov_transport (by simp : Module.finrank ℂ ℂ = 1)
      (by simp : Module.finrank ℂ ℂ = 1) G α =ᶠ[𝓝 (0 : ℂ)]
        (fun z => c * K z ^ n) := by
    have hnear : Tendsto (fun z : ℂ => α + L z) (𝓝 0) (𝓝 α) := by
      simpa only [map_zero, add_zero] using hA.continuousAt.tendsto
    filter_upwards [hnear.eventually hpow] with z hz
    change L.symm (G (α + L z)) - L.symm (G α) = c * F (α + L z) ^ n
    change G (α + L z) = G α + F (α + L z) ^ n at hz
    rw [hz, map_add, add_sub_cancel_left]
    simpa only [c, smul_eq_mul, mul_one, one_mul, mul_comm] using L.symm.map_smul (F (α + L z) ^ n) 1
  have ho : analyticOrderAt (fun z => c * K z ^ n) 0 = (n : ℕ∞) := by
    change analyticOrderAt ((fun _ : ℂ => c) * (K ^ n)) 0 = _
    rw [analyticOrderAt_mul (f := fun _ : ℂ => c) (g := K ^ n) analyticAt_const (hK.pow n),
      (analyticOrderAt_eq_zero (f := fun _ : ℂ => c) (z₀ := 0)).mpr (Or.inr hc), zero_add, analyticOrderAt_pow hK, hKo]
    simp
  have hh := (analyticOrderAt_congr hmodel).trans ho
  exact_mod_cast hT.symm.trans hh

end HodgeLean.Foundations.Program
