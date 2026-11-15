import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]

theorem weighted_meromorphic_local_data (h : Module.finrank ℂ E = 1)
    (w : b4c_MeroForm E C h) (G : C → ℂ) (x : C)
    (ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (ha : AnalyticAt ℂ (centeredScalar h G x) 0) :
    let f := HurwitzPrymRR_loc h (b4c_residue_normalizedForm h w) x * centeredScalar h G x
    ∃ r > 0, (∀ z : ℂ, ‖z‖ < r → z ≠ 0 → AnalyticAt ℂ f z) ∧
      ∀ a b : ℝ, 0 < a → a < b → b < r →
        (∫ z : ℂ, (Complex.I * fderiv ℝ
          (fun y : ℂ => (b4c_residue_profile a b ‖y‖ : ℂ)) z 1 -
          fderiv ℝ (fun y : ℂ => (b4c_residue_profile a b ‖y‖ : ℂ)) z Complex.I) * f z) =
          -(2 * (Real.pi : ℂ) * Complex.I * (G x * b4c_res (hE := h) w x)) := by
  dsimp only
  let f := HurwitzPrymRR_loc h (b4c_residue_normalizedForm h w) x * centeredScalar h G x
  have hm : MeromorphicAt (HurwitzPrymRR_loc h (b4c_residue_normalizedForm h w) x) 0 :=
    (b4c_residue_normalizedForm_mem h w).2 x
  have hgerm : HurwitzPrymRR_loc h (b4c_residue_normalizedForm h w) x =ᶠ[𝓝[≠] 0]
      HurwitzPrymRR_loc h w x :=
    ((b4c_residue_normalizedForm_loc h w x).filter_mono nhdsWithin_le_nhds).trans
      (w.property.2 x).eq_nhdsNE_toMeromorphicNFAt.symm
  have horder : (-1 : WithTop ℤ) ≤
      meromorphicOrderAt (HurwitzPrymRR_loc h (b4c_residue_normalizedForm h w) x) 0 := by
    rw [meromorphicOrderAt_congr hgerm]
    exact ho
  have hf : MeromorphicAt f 0 := hm.mul ha.meromorphicAt
  have hres : TauCeti.Contour.residue f 0 = G x * b4c_res (hE := h) w x := by
    rw [RiemannRochEichler_residue_mul_analytic hm horder ha]
    have hz : centeredScalar h G x 0 = G x := by
      simp only [centeredScalar, map_zero, add_zero,
        (extChartAt 𝓘(ℂ, E) x).left_inv (mem_extChartAt_source x)]
    change b4c_res (hE := h) (b4c_residue_normalizedForm h w) x * centeredScalar h G x 0 = _
    rw [b4c_residue_normalizedForm_res, hz, mul_comm]
  have hA : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → AnalyticAt ℂ f z := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] using hf.eventually_analyticAt
  obtain ⟨rA, hrA, hA⟩ := Metric.eventually_nhds_iff.mp hA
  obtain ⟨rL, hrL, hL⟩ := b4c_residue_local_cutoff hf
  refine ⟨min rA rL, lt_min hrA hrL, ?_, ?_⟩
  · intro z hz hne
    exact hA (by simpa only [dist_zero_right] using hz.trans_le (min_le_left rA rL)) hne
  · intro a b ha hab hbr
    rw [hL a b ha hab (hbr.trans_le (min_le_right rA rL)), hres]

end HodgeLean.Foundations.Curves.AbelTheorem
