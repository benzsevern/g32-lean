import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! An intrinsic interior point permits a short extension away from any point of its set. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Topology

theorem s2v_hardt6rb_intrinsicInterior_extend {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) {x y : E} (hx : x ∈ intrinsicInterior ℝ C) (hy : y ∈ C) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ C := by
  obtain ⟨xA, hxA, rfl⟩ := mem_intrinsicInterior.mp hx
  letI : Nonempty (affineSpan ℝ C) := ⟨xA⟩
  let yA : affineSpan ℝ C := ⟨y, subset_affineSpan ℝ C hy⟩
  let f : ℝ → affineSpan ℝ C := fun t => t • (xA -ᵥ yA) +ᵥ xA
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = xA := by simp only [f, zero_smul, zero_vadd]
  have hN : ((↑) ⁻¹' C : Set (affineSpan ℝ C)) ∈ 𝓝 (f 0) := by
    rw [hf0]
    exact mem_interior_iff_mem_nhds.mp hxA
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ ((↑) ⁻¹' C : Set (affineSpan ℝ C)) :=
    (hf.tendsto 0).eventually hN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  have ht : 0 < δ / 2 := by linarith
  have htball : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  have hpoint := hball htball
  change (δ / 2) • (xA.val - y) + xA.val ∈ C at hpoint
  exact ⟨δ / 2, ht, by simpa only [add_comm] using hpoint⟩

end HodgeLean.Foundations.Program
