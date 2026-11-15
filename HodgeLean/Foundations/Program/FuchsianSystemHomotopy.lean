import HodgeLean.Foundations.Program.FuchsianSystemNearby
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
open Set Metric Filter
open scoped Topology unitInterval
namespace HodgeLean.Foundations.Program

theorem b65f_homotopy_transport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U)
    (hA : AnalyticOnNhd ℂ A U) {x y : U} {γ δ : Path x y}
    (F : γ.Homotopy δ) :
    b65f_transport E A (fun t ↦ (γ.extend t).val) =
      b65f_transport E A (fun t ↦ (δ.extend t).val) := by
  let H : I × I → ℂ := fun q ↦ (F q).val
  have hH : Continuous H := continuous_subtype_val.comp F.continuous
  obtain ⟨r, hr, hsub⟩ := (isCompact_range hH).exists_thickening_subset_open hU
    (by rintro z ⟨q, rfl⟩; exact (F q).property)
  obtain ⟨ε, hε, he⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hH)
    (r / 16) (by positivity)
  let T : I → E →L[ℂ] E := fun s ↦
    b65f_transport E A (fun t ↦ ((F.eval s).extend t).val)
  have hT : IsLocallyConstant T := by
    apply (IsLocallyConstant.iff_eventually_eq T).mpr
    intro s
    filter_upwards [Metric.ball_mem_nhds s hε] with s' hs'
    apply b65f_nearby_paths_transport hU hA (F.eval s) (F.eval s') hr
    · intro t ht
      apply Subset.trans _ hsub
      apply ball_subset_thickening
      rw [Path.extend_apply _ ht]
      exact mem_range.mpr ⟨(s, ⟨t, ht⟩), rfl⟩
    · intro t ht
      rw [Path.extend_apply _ ht, Path.extend_apply _ ht]
      apply he
      simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist s' s)]
        using mem_ball.mp hs'
  have hh := hT.apply_eq_of_preconnectedSpace (0 : I) 1
  simpa [T] using hh

end HodgeLean.Foundations.Program
