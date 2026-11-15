import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem chart_segment_transverse_of_not_bad (h : Module.finrank ℂ E = 1)
    (γ : b3_SmoothLoop E C) (x : C) (a b : E) {r : ℝ}
    (ha : a ∈ ball (chartAt E x x) r) (hb : b ∈ ball (chartAt E x x) r)
    (hball : ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (henda : ∀ s, γ.val s ≠ (chartAt E x).symm a)
    (hendb : ∀ s, γ.val s ≠ (chartAt E x).symm b)
    (hbad : b ∉ b3Rest_bad γ.val x a) :
    ∀ s t, γ.val s = b3Forms_segPath x a b t →
      b3_orient E (b3_velocity E C γ.val s)
        (b3_velocity E C (b3Forms_segPath x a b) t) ≠ 0 := by
  have hseg := ((convex_ball _ _).segment_subset ha hb).trans hball
  have hδ := (b3A_isGoodPath_segment x a b hseg).1
  have hmem (t : ℝ) : a + Real.smoothTransition (3 * t - 1) • (b - a) ∈
      (chartAt E x).target := hball
    (Convex.add_smul_sub_mem (convex_ball _ _) ha hb
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
  intro s t hst
  let σ := Real.smoothTransition (3 * t - 1)
  have hσ0 : σ ≠ 0 := by
    intro hz
    change Real.smoothTransition (3 * t - 1) = 0 at hz
    apply henda s
    simpa only [b3Forms_segPath, hz, zero_smul, add_zero] using hst
  have hσ1 : σ ≠ 1 := by
    intro hz
    change Real.smoothTransition (3 * t - 1) = 1 at hz
    apply hendb s
    simpa only [b3Forms_segPath, hz, one_smul, add_sub_cancel] using hst
  have hy0 : 0 < 3 * t - 1 := by
    by_contra hy
    exact hσ0 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hy))
  have hy1 : 3 * t - 1 < 1 := by
    by_contra hy
    exact hσ1 (Real.smoothTransition.one_of_one_le (not_lt.mp hy))
  obtain ⟨d, hdpos, hd⟩ := b3Rest_smoothTransition_hasDerivAt_pos ⟨hy0, hy1⟩
  have heq : chartAt E x ∘ b3Forms_segPath x a b =
      fun u => a + Real.smoothTransition (3 * u - 1) • (b - a) := by
    funext u
    exact (chartAt E x).right_inv (hmem u)
  have hgd : HasDerivAt (fun u : ℝ => a + Real.smoothTransition (3 * u - 1) • (b - a))
      ((d * 3) • (b - a)) t := by
    simpa only [Function.comp_apply, id_eq, mul_one] using
      ((hd.comp t (((hasDerivAt_id t).const_mul 3).sub_const 1)).smul_const (b - a)).const_add a
  have hfd : fderiv ℝ (chartAt E x ∘ b3Forms_segPath x a b) t 1 =
      (d * 3) • (b - a) := by rw [heq, hgd.hasFDerivAt.fderiv]; simp
  have hs : γ.val s ∈ (chartAt E x).source := by
    rw [hst]
    exact (chartAt E x).map_target (hmem t)
  apply b3Rest_orient_ne_zero_of_chart h γ.val (b3Forms_segPath x a b) s t
    (γ.property.2 s) (hδ t) hst x hs
  intro u v huv
  rw [hfd, smul_smul] at huv
  have hcross : chartAt E x (γ.val s) = a + σ • (b - a) := by
    rw [hst]
    exact (chartAt E x).right_inv (hmem t)
  have hind : u = 0 ∧ v * (d * 3) = 0 := by
    by_contra hn
    exact hbad ⟨s, σ, hs,
      ⟨lt_of_le_of_ne (Real.smoothTransition.nonneg _) hσ0.symm,
        Real.smoothTransition.le_one _⟩, hcross, u, v * (d * 3), not_and_or.mp hn, huv⟩
  exact ⟨hind.1, (mul_eq_zero.mp hind.2).resolve_right (by positivity)⟩

end HodgeLean.Foundations.Curves.AbelTheorem
