import HodgeLean.Foundations.Program.G32Native.AbelCollisionTaylor

/-! # Moment cancellation in the local Abel trace -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Vanishing lower moments leave the exact divided-difference trace remainder. -/
theorem collision_trace_expansion {n : ℕ} (hn : 0 < n) (ζ : Fin n → ℂ)
    (hζ : ∀ i, ζ i ^ n = 1)
    (hmoment : ∀ k, 0 < k → k < n → ∑ i, ζ i ^ k = 0)
    (H : ℂ → ℂ) (t : ℂ) :
    (∑ i, H (ζ i * t)) = (n : ℂ) * H 0 +
      t ^ n * ∑ i, collisionTaylorRemainder H n (ζ i * t) := by
  classical
  have hlow : (∑ i : Fin n, ∑ j ∈ Finset.range n,
      (ζ i * t) ^ j * collisionTaylorRemainder H j 0) = (n : ℂ) * H 0 := by
    rw [Finset.sum_comm]
    have he (j : ℕ) : (∑ i : Fin n, (ζ i * t) ^ j * collisionTaylorRemainder H j 0) =
        (t ^ j * collisionTaylorRemainder H j 0) * ∑ i, ζ i ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow]
      ring
    simp_rw [he]
    rw [Finset.sum_eq_single 0]
    · simp only [pow_zero, collisionTaylorRemainder, Function.iterate_zero, id_eq,
        one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, mul_comm]
    · intro j hj hj0
      rw [hmoment j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hj), mul_zero]
    · intro h0
      exact (h0 (Finset.mem_range.mpr hn)).elim
  calc
    (∑ i, H (ζ i * t)) =
        (∑ i, ∑ j ∈ Finset.range n, (ζ i * t) ^ j * collisionTaylorRemainder H j 0) +
        ∑ i, (ζ i * t) ^ n * collisionTaylorRemainder H n (ζ i * t) := by
      simp_rw [collisionTaylorRemainder_expansion H n]
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [hlow, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, hζ i, one_mul]

/-- The normalized collision trace tends to the retained Taylor coefficient with its multiplicity. -/
theorem collision_trace_limit {n : ℕ} (hn : 0 < n) (ζ : Fin n → ℂ)
    (hζ : ∀ i, ζ i ^ n = 1)
    (hmoment : ∀ k, 0 < k → k < n → ∑ i, ζ i ^ k = 0)
    {H : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt H p 0) :
    Tendsto (fun t : ℂ => ((∑ i, H (ζ i * t)) - (n : ℂ) * H 0) / t ^ n)
      (𝓝[≠] 0) (𝓝 ((n : ℂ) * p.coeff n)) := by
  have hc : Tendsto (fun t : ℂ => ∑ i, collisionTaylorRemainder H n (ζ i * t))
      (𝓝 0) (𝓝 (∑ i, collisionTaylorRemainder H n (ζ i * (0 : ℂ)))) := by
    apply tendsto_finsetSum
    intro i _
    exact ((collisionTaylorRemainder_continuousAt hp n).comp_of_eq
      (continuousAt_const.mul continuousAt_id) (mul_zero _)).tendsto
  have hv : (∑ i : Fin n, collisionTaylorRemainder H n (ζ i * (0 : ℂ))) =
      (n : ℂ) * p.coeff n := by
    simp only [mul_zero, collisionTaylorRemainder_zero hp, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hv] at hc
  apply (hc.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  rw [collision_trace_expansion hn ζ hζ hmoment H t, add_sub_cancel_left]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero n ht0)).symm

#print axioms collision_trace_expansion
#print axioms collision_trace_limit
end HodgeLean.Foundations.Program.G32Native
