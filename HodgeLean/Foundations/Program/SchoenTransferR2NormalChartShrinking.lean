import HodgeLean.Foundations.Program.SchoenTransferR2ChartDeformation
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! # Shrinking a flat chart to a normal-star-shaped target

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A product ball around a point with zero normal coordinate is stable under
normal contraction. Restriction of the inverse chart gives that exact target.
Source: Hatcher, Algebraic Topology, §0, coordinate contractions.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_normal_chart_shrinking
    {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph X (E × F)) (x : X) (hx : x ∈ e.source)
    (hn : (e x).2 = 0) :
    ∃ d : OpenPartialHomeomorph X (E × F),
      x ∈ d.source ∧ d.source ⊆ e.source ∧ (∀ z, d z = e z) ∧
      ∀ y ∈ d.target, ∀ s ∈ Set.Icc (0 : ℝ) 1, (y.1, s • y.2) ∈ d.target := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let R : Set (E × F) := Metric.ball (e x).1 r ×ˢ Metric.ball (0 : F) r
  have hR : IsOpen R := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hRe : R ⊆ e.target := by
    have he : ((e x).1, (0 : F)) = e x := Prod.ext rfl hn.symm
    dsimp only [R]
    rw [ball_prod_same, he]
    exact hball
  let d := (e.symm.restrOpen R hR).symm
  have htarget : d.target = R := Set.inter_eq_right.mpr hRe
  have hxR : e x ∈ R := by
    exact ⟨Metric.mem_ball_self hr, by simpa only [hn] using Metric.mem_ball_self (x := (0 : F)) hr⟩
  have hxd : x ∈ d.source := by
    change x ∈ e.source ∩ e ⁻¹' R
    exact ⟨hx, hxR⟩
  refine ⟨d, hxd, Set.inter_subset_left, fun _ => rfl, ?_⟩
  intro y hy s hs
  rw [htarget] at hy ⊢
  refine ⟨hy.1, ?_⟩
  have hyn : ‖y.2‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hy.2
  have hsabs : ‖s‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hs.1] using hs.2
  change dist (s • y.2) 0 < r
  rw [dist_zero_right, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hsabs).trans_lt hyn

#print axioms s4_assembly_normal_chart_shrinking
end HodgeLean.Foundations.Program
