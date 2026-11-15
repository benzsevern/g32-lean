import HodgeLean.Foundations.Curves.AbelTheorem.MeromorphicRegularForms

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold Metric ContinuousAlternatingMap
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem constant_germ_of_differential_zero_near (f : C → ℝ)
    (hf : b3Forms_IsSmooth (b3Forms_fun (E := E) f)) (x : C)
    (hd : b3Forms_d (b3Forms_fun (E := E) f) =ᶠ[𝓝 x] 0) :
    f =ᶠ[𝓝 x] fun _ => f x := by
  obtain ⟨U, hsub, hU, hxU⟩ := mem_nhds_iff.mp hd
  have ho : IsOpen ((chartAt E x).target ∩ (chartAt E x).symm ⁻¹' U) :=
    (chartAt E x).continuousOn_symm.isOpen_inter_preimage (chartAt E x).open_target hU
  have hc : chartAt E x x ∈ (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' U := by
    refine ⟨(chartAt E x).map_source (mem_chart_source E x), ?_⟩
    simpa only [Set.mem_preimage, (chartAt E x).left_inv (mem_chart_source E x)] using hxU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho _ hc
  have hV : (chartAt E x).source ∩ chartAt E x ⁻¹' ball (chartAt E x x) r ∈ 𝓝 x :=
    ((chartAt E x).continuousOn.isOpen_inter_preimage (chartAt E x).open_source
      isOpen_ball).mem_nhds ⟨mem_chart_source E x, mem_ball_self hr⟩
  filter_upwards [hV] with y hy
  let γ := b3Forms_segPath x (chartAt E x x) (chartAt E x y)
  have hseg := ((convex_ball _ _).segment_subset (mem_ball_self hr) hy.2).trans
    (fun _ hu => (hball hu).1)
  have hγ := b3A_isGoodPath_segment x (chartAt E x x) (chartAt E x y) hseg
  have he0 : γ 0 = x := by
    exact hγ.apply_zero.trans ((chartAt E x).left_inv (mem_chart_source E x))
  have he1 : γ 1 = y := hγ.apply_one.trans ((chartAt E x).left_inv hy.1)
  have hzero : b3Forms_lineIntegral (b3Forms_d (b3Forms_fun (E := E) f)) γ 0 1 = 0 := by
    unfold b3Forms_lineIntegral
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t _ => ?_).trans
      intervalIntegral.integral_zero
    have ht : γ t ∈ U := (hball (Convex.add_smul_sub_mem (convex_ball _ _)
      (mem_ball_self hr) hy.2 ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)).2
    have hz := hsub ht
    change b3Forms_d (b3Forms_fun (E := E) f) (γ t) = 0 at hz
    rw [hz]
    rfl
  rw [b3Forms_lineIntegral_d hf (γ := γ) hγ.1, he0, he1] at hzero
  exact sub_eq_zero.mp hzero

end HodgeLean.Foundations.Curves.AbelTheorem
