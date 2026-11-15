import HodgeLean.Foundations.Program.HolomorphicODELimit
import HodgeLean.Foundations.Program.HolomorphicODEPrimitiveBounds

noncomputable section
open Set Metric Filter Topology
namespace HodgeLean.Foundations.Program

theorem b65_summable_uniform_limit {X F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {U : Set X} {f : ℕ → X → F} {u : ℕ → ℝ} (hu : Summable u)
    (hf : ∀ n x, x ∈ U → ‖f (n + 1) x - f n x‖ ≤ u n) :
    ∃ g : X → F, TendstoUniformlyOn f g atTop U := by
  let d : ℕ → X → F := fun n x ↦ f (n + 1) x - f n x
  have ht := tendstoUniformlyOn_tsum_nat hu (f := d) hf
  have heq (n : ℕ) (x : X) : f n x = f 0 x + ∑ i ∈ Finset.range n, d i x := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ← ih]; dsimp [d]; abel
  let g : X → F := fun x ↦ f 0 x + ∑' n, d n x
  refine ⟨g, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with n hn x hx
  dsimp [g]
  rw [heq n x, dist_add_left]
  exact hn x hx

theorem b65_segmentPrimitive_power_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {c x : ℂ} {r C : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (hx : x ∈ ball c r) (hb : ∀ v ∈ ball c r, ‖f v‖ ≤ C * ‖v - c‖ ^ n) :
    ‖b65_segmentPrimitive f c x‖ ≤ C * ‖x - c‖ ^ (n + 1) / (n + 1) := by
  have hbound : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖f (c + (t : ℂ) * (x - c))‖ ≤ (C * ‖x - c‖ ^ n) * t ^ n := by
    intro t ht
    have hh := hb _ (b65_segment_mem_ball hx ⟨ht.1.le, ht.2⟩)
    simpa [add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.1.le, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hh
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) zero_le_one
    (Filter.Eventually.of_forall hbound)
    (show IntervalIntegrable (fun t : ℝ ↦ (C * ‖x - c‖ ^ n) * t ^ n)
      MeasureTheory.volume 0 1 from (by fun_prop : Continuous _).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, integral_pow] at hi
  simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.cast_add, Nat.cast_one] at hi
  rw [b65_segmentPrimitive, norm_smul]
  apply (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq
  rw [pow_succ]
  ring

end HodgeLean.Foundations.Program
