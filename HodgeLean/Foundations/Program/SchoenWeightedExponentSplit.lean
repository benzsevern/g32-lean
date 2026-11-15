import HodgeLean.Foundations.Program.SchoenBoundedExponentSums

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A sufficiently large multiple of common weight chunks can be extracted from every positive multiple. -/
theorem s2_weighted_exponent_split {ι : Type} (s : Finset ι)
    (a d c : ι → ℕ) (D N m : ℕ) (hD : 0 < D) (hN : s.card < N) (hm : 0 < m)
    (hc : ∀ i ∈ s, c i * d i = D)
    (ha : ∑ i ∈ s, a i * d i = m * (N * D)) :
    ∃ b : ι → ℕ, (∀ i, b i ≤ a i) ∧ ∑ i ∈ s, b i * d i = N * D := by
  classical
  let q := ∑ i ∈ s, a i / c i
  let r := ∑ i ∈ s, (a i % c i) * d i
  have hsum : r + D * q = m * N * D := by
    rw [mul_assoc]
    rw [← ha]
    dsimp only [r, q]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hc i hi]
    nlinarith [Nat.mod_add_div (a i) (c i)]
  have hr : r < N * D := by
    have hle : r ≤ s.card * D := by
      calc
        r ≤ ∑ i ∈ s, D := by
          apply Finset.sum_le_sum
          intro i hi
          have hci : 0 < c i := by nlinarith [hc i hi]
          have := Nat.mod_lt (a i) hci
          nlinarith [hc i hi]
        _ = s.card * D := by simp only [Finset.sum_const, smul_eq_mul]
    nlinarith
  have hq : q ≤ m * N := by nlinarith
  let j := m * N - q
  have hjq : j + q = m * N := Nat.sub_add_cancel hq
  have hrj : r = j * D := by nlinarith
  have hj : j < N := by nlinarith
  have halloc : N - j ≤ q := by
    have hmn : N ≤ m * N := by nlinarith
    omega
  obtain ⟨t, ht, htsum⟩ := s2_exists_bounded_sum s (fun i => a i / c i) (N - j) halloc
  refine ⟨fun i => a i % c i + c i * t i, ?_, ?_⟩
  · intro i
    change a i % c i + c i * t i ≤ a i
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left (c i) (ht i)) _).trans_eq
      (Nat.mod_add_div (a i) (c i))
  · have heq : (∑ i ∈ s, (a i % c i + c i * t i) * d i) = r + D * (N - j) := by
      rw [← htsum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [add_mul]
      congr 1
      rw [← hc i hi]
      ac_rfl
    rw [heq, hrj]
    nlinarith [Nat.sub_add_cancel hj.le]

end HodgeLean.Foundations.Program
