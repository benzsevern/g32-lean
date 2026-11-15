import HodgeLean.Foundations.Curves.AbelTheorem.TransverseReparam

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

theorem transverse_path_concat (γ : b3_SmoothLoop E C) (δ ε : ℝ → C)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ)
    (hε : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ε)
    (htrδ : ∀ s t, γ.val s = δ t →
      b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C δ t) ≠ 0)
    (htrε : ∀ s t, γ.val s = ε t →
      b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C ε t) ≠ 0)
    (q : C) (hδ1 : δ 1 = q) (hoff : ∀ s, γ.val s ≠ q) :
    ∀ s t, γ.val s = (if t ≤ 1 / 2 then δ (2 * t) else ε (2 * t - 1)) →
      b3_orient E (b3_velocity E C γ.val s)
        (b3_velocity E C (fun u => if u ≤ 1 / 2 then δ (2 * u) else ε (2 * u - 1)) t) ≠ 0 := by
  let cat : ℝ → C := fun u => if u ≤ 1 / 2 then δ (2 * u) else ε (2 * u - 1)
  have hv {ξ ζ : ℝ → C} {t : ℝ} (he : ξ =ᶠ[𝓝 t] ζ) :
      b3_velocity E C ξ t = b3_velocity E C ζ t := by
    rw [b3_velocity, b3_velocity, he.mfderiv_eq]
    rfl
  intro s t he
  rcases lt_trichotomy t (1 / 2) with ht | ht | ht
  · have hg : cat =ᶠ[𝓝 t] δ ∘ (fun u : ℝ => 2 * u) := by
      filter_upwards [Iio_mem_nhds ht] with u hu
      change u < 1 / 2 at hu
      simp only [cat, if_pos hu.le, Function.comp_apply]
    change b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C cat t) ≠ 0
    rw [hv hg]
    apply transverse_path_reparam γ δ hδ htrδ (fun u : ℝ => 2 * u)
      (contDiff_const.mul contDiff_id) (fun _ t _ => ?_) s t (he.trans hg.eq_of_nhds)
    have hd : deriv (fun u : ℝ => 2 * u) t = 2 := by
      simpa using ((hasDerivAt_id t).const_mul 2).deriv
    rw [hd]
    norm_num
  · subst t
    apply False.elim
    apply hoff s
    simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, le_refl, if_true, hδ1] using he
  · have hg : cat =ᶠ[𝓝 t] ε ∘ (fun u : ℝ => 2 * u - 1) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      change 1 / 2 < u at hu
      simp only [cat, if_neg (not_le.mpr hu), Function.comp_apply]
    change b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C cat t) ≠ 0
    rw [hv hg]
    apply transverse_path_reparam γ ε hε htrε (fun u : ℝ => 2 * u - 1)
      ((contDiff_const.mul contDiff_id).sub contDiff_const) (fun _ t _ => ?_) s t
      (he.trans hg.eq_of_nhds)
    have hd : deriv (fun u : ℝ => 2 * u - 1) t = 2 := by
      simpa using (((hasDerivAt_id t).const_mul 2).sub_const 1).deriv
    rw [hd]
    norm_num

end HodgeLean.Foundations.Curves.AbelTheorem
