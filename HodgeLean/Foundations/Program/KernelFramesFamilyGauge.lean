import HodgeLean.Foundations.Program.KernelFramesFamilyTaylor

/-! # B6-5 stage 5d, family part: Taylor coefficients of normal-form gauges

Taylor series of `(s − b)⁻¹`, of the regular part at a fixed pole, and the recursion
`n H_n = Λ H_n − H_n Λ + Σ_{l<n} (P⁻¹ G_l P) H_{n−1−l}` satisfied by the Taylor coefficients of
any analytic solution of the normal-form equation (`b65q_gauge_taylor`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Polynomial Matrix Filter
open scoped LaurentSeries RatFunc Topology Nat
namespace HodgeLean.Foundations.Program

theorem b65q_T_sum {ι : Type*} (S : Finset ι) {a : ℂ} {f : ι → ℂ → ℂ}
    (h : ∀ i ∈ S, AnalyticAt ℂ (f i) a) :
    b65q_T (fun s ↦ ∑ i ∈ S, f i s) a = ∑ i ∈ S, b65q_T (f i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [b65q_T_const]
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    rw [b65q_T_add (f := f j) (g := fun s ↦ ∑ i ∈ S, f i s) (h j (Finset.mem_insert_self j S))
      (b65q_anAt_sum _ fun i hi ↦ h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]

theorem b65q_T_const_mul {f : ℂ → ℂ} {a : ℂ} (c : ℂ) (hf : AnalyticAt ℂ f a) :
    b65q_T (fun s ↦ c * f s) a = PowerSeries.C c * b65q_T f a := by
  rw [b65q_T_mul analyticAt_const hf, b65q_T_const]

theorem b65q_T_sub_const (a : ℂ) : b65q_T (fun s ↦ s - a) a = PowerSeries.X := by
  rw [show (fun s : ℂ ↦ s - a) = fun s ↦ s + (-a) by funext s; ring,
    b65q_T_add (f := fun s ↦ s) (g := fun _ ↦ -a) analyticAt_id analyticAt_const, b65q_T_id,
    b65q_T_const, map_neg]
  ring

theorem b65q_T_inv_sub {a b : ℂ} (h : a ≠ b) (l : ℕ) :
    PowerSeries.coeff l (b65q_T (fun s ↦ (s - b)⁻¹) a) = -((b - a) ^ (l + 1))⁻¹ := by
  have hab : a - b ≠ 0 := sub_ne_zero.mpr h
  have han : AnalyticAt ℂ (fun s ↦ (s - b)⁻¹) a :=
    (analyticAt_id.sub analyticAt_const).inv hab
  have hT : (PowerSeries.X + PowerSeries.C (a - b)) * b65q_T (fun s ↦ (s - b)⁻¹) a = 1 := by
    have h1 : b65q_T (fun s ↦ s - b) a = PowerSeries.X + PowerSeries.C (a - b) := by
      rw [show (fun s : ℂ ↦ s - b) = fun s ↦ s + (-b) by funext s; ring,
        b65q_T_add (f := fun s ↦ s) (g := fun _ ↦ -b) analyticAt_id analyticAt_const, b65q_T_id,
        b65q_T_const]
      simp [sub_eq_add_neg]; ring
    rw [← h1, ← b65q_T_mul (f := fun s ↦ s - b) (g := fun s ↦ (s - b)⁻¹)
      (analyticAt_id.sub analyticAt_const) han, ← map_one PowerSeries.C, ← b65q_T_const 1 a]
    apply b65q_T_congr
    filter_upwards [(continuousAt_id.sub continuousAt_const).eventually_ne hab] with s hs
    exact mul_inv_cancel₀ hs
  have hG : (PowerSeries.X + PowerSeries.C (a - b)) * b65q_G (a - b) 1 = 1 := by
    rw [b65q_G_succ hab 0, b65q_G_zero]
  have heq : b65q_T (fun s ↦ (s - b)⁻¹) a = b65q_G (a - b) 1 := by
    have := hT.trans hG.symm
    have hne : PowerSeries.X + PowerSeries.C (a - b) ≠ 0 := by
      intro h0
      have := congrArg (PowerSeries.coeff 0) h0
      simp at this; exact hab this
    exact mul_left_cancel₀ hne this
  rw [heq]
  simp only [b65q_G, PowerSeries.coeff_mk]
  rw [show 1 + l - 1 = l by omega, Nat.choose_self, show a - b = (-1) * (b - a) by ring,
    show 1 + l = l + 1 by ring, mul_pow, pow_succ (-1 : ℂ) l]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have h1 : ((-1 : ℂ) ^ l) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : (b - a) ^ (l + 1) ≠ 0 := pow_ne_zero _ hba
  field_simp
  ring

/-- Taylor coefficients of a matrix-valued function. -/
def b65q_TM (F : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (a : ℂ) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j ↦ PowerSeries.coeff n (b65q_T (fun s ↦ F s i j) a)

theorem b65q_regular_entry (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (s : ℂ) (i p : Fin 4) :
    (P⁻¹ * b65q_regular t A k s * P) i p =
      ∑ q, if q = Sum.inl k then 0 else (P⁻¹ * A q * P) i p * (s - t q)⁻¹ := by
  simp only [b65q_regular, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  split_ifs <;> simp [Matrix.mul_smul, Matrix.smul_mul, mul_comm]

theorem b65q_taylor_entry (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (l : ℕ) (i p : Fin 4) :
    (P⁻¹ * b65q_taylor t A k l * P) i p =
      ∑ q, if q = Sum.inl k then 0 else
        (P⁻¹ * A q * P) i p * -((t q - t (Sum.inl k)) ^ (l + 1))⁻¹ := by
  simp only [b65q_taylor, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  split_ifs <;> simp [Matrix.mul_smul, Matrix.smul_mul, mul_comm]

theorem b65q_T_regular (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4)
    (hne : ∀ q, q ≠ Sum.inl k → t (Sum.inl k) ≠ t q) (i p : Fin 4) :
    b65q_T (fun s ↦ (P⁻¹ * b65q_regular t A k s * P) i p) (t (Sum.inl k)) =
      PowerSeries.mk fun l ↦ (P⁻¹ * b65q_taylor t A k l * P) i p := by
  have hq : ∀ q ∈ (Finset.univ : Finset (Fin 4 ⊕ Fin 12)), AnalyticAt ℂ (fun s ↦
      if q = Sum.inl k then (0 : ℂ) else (P⁻¹ * A q * P) i p * (s - t q)⁻¹) (t (Sum.inl k)) := by
    intro q _
    split_ifs with h
    · exact analyticAt_const
    · exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
        (sub_ne_zero.mpr (hne q h)))
  simp only [b65q_regular_entry]
  rw [b65q_T_sum _ hq]
  ext l
  rw [map_sum, PowerSeries.coeff_mk, b65q_taylor_entry]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  split_ifs with h
  · simp [b65q_T_const]
  · rw [b65q_T_const_mul (f := fun s ↦ (s - t q)⁻¹) _
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (hne q h))),
      PowerSeries.coeff_C_mul, b65q_T_inv_sub (hne q h)]

/-- **The Taylor coefficients of a normal-form gauge satisfy the recursion.** -/
theorem b65q_gauge_taylor (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (lam : Fin 4 → ℂ)
    (hne : ∀ q, q ≠ Sum.inl k → t (Sum.inl k) ≠ t q) (H : ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (hH : ∀ i j, AnalyticAt ℂ (fun s ↦ H s i j) (t (Sum.inl k)))
    (hode : ∀ᶠ s in 𝓝 (t (Sum.inl k)), ∀ i j : Fin 4,
      (s - t (Sum.inl k)) * deriv (fun s ↦ H s i j) s =
        (diagonal lam * H s - H s * diagonal lam +
          (s - t (Sum.inl k)) • (P⁻¹ * b65q_regular t A k s * P * H s)) i j)
    (n : ℕ) (i j : Fin 4) :
    (n : ℂ) * b65q_TM H (t (Sum.inl k)) n i j =
      (diagonal lam * b65q_TM H (t (Sum.inl k)) n - b65q_TM H (t (Sum.inl k)) n * diagonal lam +
        ∑ l ∈ Finset.range n, (P⁻¹ * b65q_taylor t A k l * P) *
          b65q_TM H (t (Sum.inl k)) (n - 1 - l)) i j := by
  set a := t (Sum.inl k) with ha
  have hreg : ∀ i p, AnalyticAt ℂ (fun s ↦ (P⁻¹ * b65q_regular t A k s * P) i p) a := by
    intro i p
    have : (fun s ↦ (P⁻¹ * b65q_regular t A k s * P) i p) = fun s ↦
        ∑ q, if q = Sum.inl k then (0 : ℂ) else (P⁻¹ * A q * P) i p * (s - t q)⁻¹ :=
      funext fun s ↦ b65q_regular_entry t A P k s i p
    rw [this]
    refine b65q_anAt_sum _ fun q _ ↦ ?_
    split_ifs with h
    · exact analyticAt_const
    · exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
        (sub_ne_zero.mpr (hne q h)))
  have hT := b65q_T_congr (a := a) (hode.mono fun s hs ↦ hs i j)
  have hL : b65q_T (fun s ↦ (s - a) * deriv (fun s ↦ H s i j) s) a =
      PowerSeries.X * b65q_T (deriv fun s ↦ H s i j) a := by
    rw [b65q_T_mul (f := fun s ↦ s - a) (analyticAt_id.sub analyticAt_const) (hH i j).deriv,
      b65q_T_sub_const]
  have hR : b65q_T (fun s ↦ (diagonal lam * H s - H s * diagonal lam +
      (s - a) • (P⁻¹ * b65q_regular t A k s * P * H s)) i j) a =
      PowerSeries.C (lam i - lam j) * b65q_T (fun s ↦ H s i j) a +
        PowerSeries.X * ∑ p, b65q_T (fun s ↦ (P⁻¹ * b65q_regular t A k s * P) i p) a *
          b65q_T (fun s ↦ H s p j) a := by
    have e1 : (fun s ↦ (diagonal lam * H s - H s * diagonal lam +
        (s - a) • (P⁻¹ * b65q_regular t A k s * P * H s)) i j) = fun s ↦
        (lam i - lam j) * H s i j +
          (s - a) * ∑ p, (P⁻¹ * b65q_regular t A k s * P) i p * H s p j := by
      funext s
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [Matrix.mul_apply (M := P⁻¹ * b65q_regular t A k s * P) (N := H s)]
      ring
    have hsumAn : AnalyticAt ℂ (fun s ↦ ∑ p, (P⁻¹ * b65q_regular t A k s * P) i p * H s p j) a :=
      b65q_anAt_sum _ fun p _ ↦ (hreg i p).mul (hH p j)
    rw [e1, b65q_T_add (f := fun s ↦ (lam i - lam j) * H s i j)
      (g := fun s ↦ (s - a) * ∑ p, (P⁻¹ * b65q_regular t A k s * P) i p * H s p j)
      (analyticAt_const.mul (hH i j)) ((analyticAt_id.sub analyticAt_const).mul hsumAn),
      b65q_T_const_mul (f := fun s ↦ H s i j) _ (hH i j),
      b65q_T_mul (f := fun s ↦ s - a)
        (g := fun s ↦ ∑ p, (P⁻¹ * b65q_regular t A k s * P) i p * H s p j)
        (analyticAt_id.sub analyticAt_const) hsumAn, b65q_T_sub_const,
      b65q_T_sum (f := fun p s ↦ (P⁻¹ * b65q_regular t A k s * P) i p * H s p j) _
        fun p _ ↦ (hreg i p).mul (hH p j)]
    congr 2
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [b65q_T_mul (f := fun s ↦ (P⁻¹ * b65q_regular t A k s * P) i p) (g := fun s ↦ H s p j)
      (hreg i p) (hH p j)]
  rw [hL, hR] at hT
  have hc := congrArg (PowerSeries.coeff n) hT
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sum_apply]
  simp only [b65q_TM, Matrix.of_apply]
  rcases n with _ | n
  · simp only [PowerSeries.coeff_zero_X_mul, map_add, PowerSeries.coeff_C_mul] at hc
    simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.sum_empty, add_zero]
    linear_combination hc
  · rw [PowerSeries.coeff_succ_X_mul, b65q_T_deriv, map_add, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, map_sum] at hc
    simp only [PowerSeries.coeff_mul] at hc
    simp only [ha, b65q_T_regular t A P k hne, PowerSeries.coeff_mk] at hc
    have hsum : ∑ x ∈ Finset.range (n + 1), (P⁻¹ * b65q_taylor t A k x * P *
        Matrix.of fun i j ↦ PowerSeries.coeff (n - x) (b65q_T (fun s ↦ H s i j) (t (Sum.inl k))))
          i j = ∑ p, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
        (P⁻¹ * b65q_taylor t A k q.1 * P) i p *
          PowerSeries.coeff q.2 (b65q_T (fun s ↦ H s p j) (t (Sum.inl k))) := by
      simp only [Matrix.mul_apply (M := P⁻¹ * b65q_taylor t A k _ * P), Matrix.of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [ha] at *
    push_cast
    rw [hsum]
    linear_combination hc

end HodgeLean.Foundations.Program
