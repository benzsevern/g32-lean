import HodgeLean.Foundations.Program.NumeratorJetBranchCertificates
import HodgeLean.Foundations.Program.NumeratorJetFirstOrder
import HodgeLean.Foundations.Program.KernelFramesFamilySystems

/-! # Taylor coefficients of the moving powers and of the branch polynomial

The order-`n` Taylor coefficient of `t_x(θ)^m` is the evaluation at the labelled root of the
stored moving-power coordinates; summing over the fibres gives the traced power sums. The
coefficients of `D_θ = s Π_x (s − t_x(θ))` are elementary symmetric functions of the negated
moving poles, and the Newton identities determine their Taylor coefficients from the traced power
sums.
-/

noncomputable section
open Set Metric Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Taylor coefficients commute with finite sums of analytic germs. -/
theorem b65e_coeffT_finsum {κ : Type*} (s : Finset κ) (f : κ → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (k : ℕ) :
    PowerSeries.coeff k (b65q_T (fun θ ↦ ∑ i ∈ s, f i θ) 0) =
      ∑ i ∈ s, PowerSeries.coeff k (b65q_T (f i) 0) := by
  rw [b65q_T_sum s hf, map_sum]

/-- Taylor coefficients of a finite sum of products of analytic germs. -/
theorem b65e_coeffT_finsum_mul {κ : Type*} (s : Finset κ) (f g : κ → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (hg : ∀ i ∈ s, AnalyticAt ℂ (g i) 0) (k : ℕ) :
    PowerSeries.coeff k (b65q_T (fun θ ↦ ∑ i ∈ s, f i θ * g i θ) 0) =
      ∑ a ∈ Finset.range (k + 1), ∑ i ∈ s,
        PowerSeries.coeff a (b65q_T (f i) 0) * PowerSeries.coeff (k - a) (b65q_T (g i) 0) := by
  have hs : b65q_T (fun θ ↦ ∑ i ∈ s, f i θ * g i θ) 0 =
      ∑ i ∈ s, b65q_T (fun θ ↦ f i θ * g i θ) 0 :=
    b65q_T_sum s fun i hi ↦ (hf i hi).mul (hg i hi)
  rw [hs, map_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [b65q_T_mul (hf i hi) (hg i hi), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem b65e_coordinateEval_add (u v : Fin 6 → ℚ) (z : ℂ) :
    b65e_coordinateEvalQ (fun c ↦ u c + v c) z =
      b65e_coordinateEvalQ u z + b65e_coordinateEvalQ v z := by
  simp only [b65e_coordinateEvalQ, Rat.cast_add, add_mul, Finset.sum_add_distrib]

theorem b65e_coordinateEval_zero (z : ℂ) : b65e_coordinateEvalQ 0 z = 0 := by
  simp [b65e_coordinateEvalQ]

theorem b65e_coordinateEval_one (z : ℂ) : b65e_coordinateEvalQ b65e_oneCoordQ z = 1 := by
  simp [b65e_coordinateEvalQ, b65e_oneCoordQ, Fin.sum_univ_succ]

theorem b65e_coordinateEval_root (z : ℂ) : b65e_coordinateEvalQ b65e_rootCoordQ z = z := by
  simp [b65e_coordinateEvalQ, b65e_rootCoordQ, Fin.sum_univ_succ]

theorem b65e_coordinateEval_velocity (x : Fin 12) (z : ℂ) :
    b65e_coordinateEvalQ (b65e_velocityQ (b65q_fibreIndex x)) z = b65p_V (b65p_fibre x) z := by
  have h : ((b65q_fibreValue (b65q_fibreIndex x) : ℤ)) = b65p_fibre x := by
    revert x; decide
  rw [← h, b65e_velocityQ_eval]
  rfl

theorem b65e_movingPole_an (p : Fin 12 → ℂ) (x : Fin 12) (m : ℕ) :
    AnalyticAt ℂ (fun θ ↦ b65p_poles p θ (Sum.inr x) ^ m) 0 :=
  ((b65q_poles_an p univ (Sum.inr x)) 0 (mem_univ _)).pow m

/-- Taylor series of a moving pole. -/
theorem b65e_movingPole_T (p : Fin 12 → ℂ) (x : Fin 12) :
    b65q_T (fun θ ↦ b65p_poles p θ (Sum.inr x)) 0 =
      PowerSeries.C (p x) + PowerSeries.C (b65p_V (b65p_fibre x) (p x)) * PowerSeries.X := by
  simp only [b65p_poles, Sum.elim_inr]
  rw [b65q_T_add (f := fun _ ↦ p x) (g := fun θ ↦ θ * b65p_V (b65p_fibre x) (p x))
    analyticAt_const (by fun_prop), b65q_T_const]
  have : (fun θ : ℂ ↦ θ * b65p_V (b65p_fibre x) (p x)) =
      fun θ ↦ b65p_V (b65p_fibre x) (p x) * θ := funext fun θ ↦ mul_comm _ _
  rw [this, b65q_T_const_mul (f := fun θ : ℂ ↦ θ) _ analyticAt_id, b65q_T_id]
  simp

/-- Taylor coefficients of the moving powers are the stored coordinates at the labelled root. -/
theorem b65e_movingPower_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) (x : Fin 12) :
    ∀ m ≤ 12, ∀ n < 8,
      PowerSeries.coeff n (b65q_T (fun θ ↦ b65p_poles p θ (Sum.inr x) ^ m) 0) =
        b65e_coordinateEvalQ (b65e_TcN (b65q_fibreIndex x) m n) (p x) := by
  have hroot : (b65q_fibreC (b65q_fibreIndex x)).eval (p x) = 0 :=
    b65q_fibre_root O _ (by simp [b65q_fibreSet])
  intro m
  induction m with
  | zero =>
    intro _ n hn
    simp only [pow_zero, b65q_T_const, PowerSeries.coeff_C]
    have ht : b65e_TcN (b65q_fibreIndex x) 0 n =
        if n = 0 then b65e_oneCoordQ else 0 := by
      funext c
      simp only [b65e_TcN, show (0 : ℕ) < 13 by omega, hn, ↓reduceDIte]
      have := b65e_TcQ_zero_table (b65q_fibreIndex x) ⟨n, hn⟩ c
      rw [show (⟨0, by omega⟩ : Fin 13) = 0 from rfl, this]
      split_ifs <;> rfl
    rw [ht]
    split_ifs
    · rw [b65e_coordinateEval_one]
    · rw [b65e_coordinateEval_zero]
  | succ m ih =>
    intro hm n hn
    have hf : (fun θ ↦ b65p_poles p θ (Sum.inr x) ^ (m + 1)) =
        fun θ ↦ b65p_poles p θ (Sum.inr x) * b65p_poles p θ (Sum.inr x) ^ m :=
      funext fun θ ↦ pow_succ' _ _
    rw [hf, b65q_T_mul (b65e_movingPole_an p x 1 |>.congr (by simp))
      (b65e_movingPole_an p x m), b65e_movingPole_T, add_mul, map_add, PowerSeries.coeff_C_mul,
      mul_assoc, PowerSeries.coeff_C_mul]
    have ht : b65e_TcN (b65q_fibreIndex x) (m + 1) n =
        fun c ↦ b65e_TcStepQ (b65q_fibreIndex x) m n c := by
      funext c
      simp only [b65e_TcN, show m + 1 < 13 by omega, hn, ↓reduceDIte]
      exact b65e_TcQ_step_table (b65q_fibreIndex x) ⟨m, by omega⟩ ⟨n, hn⟩ c
    rw [ht]
    unfold b65e_TcStepQ
    rw [b65e_coordinateEval_add, b65e_coordinateMulQ_eval _ _ _ _ hroot,
      b65e_coordinateEval_root, ih (by omega) n hn]
    congr 1
    rcases n with _ | n
    · simp [b65e_coordinateEvalQ]
    · rw [PowerSeries.coeff_succ_X_mul]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [b65e_coordinateMulQ_eval _ _ _ _ hroot, b65e_coordinateEval_velocity,
        ih (by omega) n (by omega)]

/-- Taylor coefficients of the traced power sums of the moving poles. -/
theorem b65e_powerTrace_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) (b : ℕ) (hb : b ≤ 12)
    (n : ℕ) (hn : n < 8) :
    PowerSeries.coeff n (b65q_T (fun θ ↦ ∑ x : Fin 12, b65p_poles p θ (Sum.inr x) ^ b) 0) =
      (b65e_powerTraceQ b n : ℂ) := by
  rw [b65e_coeffT_finsum _ _ (fun x _ ↦ b65e_movingPole_an p x b)]
  simp only [fun x ↦ b65e_movingPower_T p O x b hb n hn]
  rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
  unfold b65e_powerTraceQ
  push_cast
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hfs : (Finset.univ.filter fun x ↦ b65q_fibreIndex x = e) = b65q_fibreSet e := rfl
  rw [hfs]
  rw [Finset.sum_congr rfl fun x hx ↦ by
    rw [show b65q_fibreIndex x = e from (Finset.mem_filter.mp hx).2]]
  rw [b65q_fibre_reduce O e (fun r ↦ b65e_coordinateEvalQ (b65e_TcN e b n) r)
    (b65e_TcN e b n) fun r _ ↦ rfl]
  push_cast
  rfl

/-- The negated moving poles. -/
def b65e_negPoles (p : Fin 12 → ℂ) (θ : ℂ) (x : Fin 12) : ℂ := -b65p_poles p θ (Sum.inr x)

/-- Elementary symmetric functions of the negated moving poles. -/
def b65e_esym (p : Fin 12 → ℂ) (k : ℕ) (θ : ℂ) : ℂ :=
  ∑ T ∈ Finset.univ.powersetCard k, ∏ x ∈ T, b65e_negPoles p θ x

theorem b65e_esym_an (p : Fin 12 → ℂ) (k : ℕ) : AnalyticAt ℂ (b65e_esym p k) 0 := by
  unfold b65e_esym
  apply b65q_anAt_sum
  intro T _
  apply Finset.analyticAt_fun_prod
  intro x _
  exact ((b65q_poles_an p univ (Sum.inr x)) 0 (mem_univ _)).neg

theorem b65e_antidiag_filter_sum (g : ℕ → ℕ → ℂ) (k : ℕ) :
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k, g a.1 a.2 =
      ∑ a ∈ Finset.range k, g a (k - a) := by
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
    if i < k then g i j else 0), Finset.sum_range_succ]
  simp only [lt_irrefl, ↓reduceIte, add_zero]
  exact Finset.sum_congr rfl fun a ha ↦ by simp [Finset.mem_range.mp ha]

/-- **Newton identities** for the negated moving poles at one parameter. -/
theorem b65e_esym_newton (p : Fin 12 → ℂ) (k : ℕ) (θ : ℂ) :
    (k : ℂ) * b65e_esym p k θ = (-1) ^ (k + 1) * ∑ a ∈ Finset.range k,
      ((-1) ^ a * b65e_esym p a θ) *
        ((-1) ^ (k - a) * ∑ x : Fin 12, b65p_poles p θ (Sum.inr x) ^ (k - a)) := by
  have h := congrArg (MvPolynomial.eval (b65e_negPoles p θ))
    (MvPolynomial.mul_esymm_eq_sum (Fin 12) ℂ k)
  have he : ∀ a, MvPolynomial.eval (b65e_negPoles p θ) (MvPolynomial.esymm (Fin 12) ℂ a) =
      b65e_esym p a θ := by
    intro a
    simp [MvPolynomial.esymm, b65e_esym]
  have hp : ∀ b, MvPolynomial.eval (b65e_negPoles p θ) (MvPolynomial.psum (Fin 12) ℂ b) =
      (-1) ^ b * ∑ x : Fin 12, b65p_poles p θ (Sum.inr x) ^ b := by
    intro b
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X, b65e_negPoles]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ neg_pow _ _
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, he, hp] at h
  rw [h, b65e_antidiag_filter_sum (fun a b ↦ (-1) ^ a * b65e_esym p a θ *
    ((-1) ^ b * ∑ x : Fin 12, b65p_poles p θ (Sum.inr x) ^ b))]

/-- The branch-polynomial coefficients are the elementary symmetric functions. -/
theorem b65e_denominator_coeff (p : Fin 12 → ℂ) (θ : ℂ) (i : ℕ) :
    (b65q_denominator (b65p_poles p θ)).coeff i =
      if 1 ≤ i ∧ i ≤ 13 then b65e_esym p (13 - i) θ else 0 := by
  rcases i with _ | i
  · simp [b65q_denominator]
  · rw [b65q_denominator, coeff_X_mul]
    have hprod : ∏ x : Fin 12, (X - C (b65p_poles p θ (Sum.inr x))) =
        ∏ x : Fin 12, (X + C (b65e_negPoles p θ x)) := by
      simp [b65e_negPoles, sub_eq_add_neg]
    rw [hprod]
    split_ifs with h
    · rw [Finset.prod_X_add_C_coeff _ _ (by simp; omega)]
      simp only [Finset.card_univ, Fintype.card_fin, b65e_esym]
      congr 2
      omega
    · apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_prod_of_monic _ _ fun x _ ↦ monic_X_add_C _]
      simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
      omega

/-- Taylor coefficients of the elementary symmetric functions. -/
theorem b65e_esym_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ k ≤ 12, ∀ n < 8,
      PowerSeries.coeff n (b65q_T (b65e_esym p k) 0) = (b65e_esymN k n : ℂ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk n hn
    rcases k with _ | k
    · have h0 : b65e_esym p 0 = fun _ ↦ 1 := by
        funext θ
        simp [b65e_esym]
      rw [h0, b65q_T_const, PowerSeries.coeff_C]
      have := b65e_esymQ_zero_table ⟨n, hn⟩
      simp only [b65e_esymN, show (0 : ℕ) < 13 by omega, hn, ↓reduceDIte]
      rw [show (⟨0, by omega⟩ : Fin 13) = 0 from rfl, this]
      split_ifs <;> simp
    · have hf : (fun θ ↦ ((k + 1 : ℕ) : ℂ) * b65e_esym p (k + 1) θ) =
          fun θ ↦ (-1) ^ (k + 1 + 1) * ∑ a ∈ Finset.range (k + 1),
            ((-1) ^ a * b65e_esym p a θ) *
              ((-1) ^ (k + 1 - a) * ∑ x : Fin 12, b65p_poles p θ (Sum.inr x) ^ (k + 1 - a)) :=
        funext fun θ ↦ b65e_esym_newton p (k + 1) θ
      have hL := congrArg (fun f ↦ PowerSeries.coeff n (b65q_T f 0)) hf
      have hfa : ∀ a ∈ Finset.range (k + 1),
          AnalyticAt ℂ (fun θ ↦ (-1 : ℂ) ^ a * b65e_esym p a θ) 0 :=
        fun a _ ↦ analyticAt_const.mul (b65e_esym_an p a)
      have hga : ∀ a ∈ Finset.range (k + 1), AnalyticAt ℂ (fun θ ↦ (-1 : ℂ) ^ (k + 1 - a) *
          ∑ x : Fin 12, b65p_poles p θ (Sum.inr x) ^ (k + 1 - a)) 0 :=
        fun a _ ↦ analyticAt_const.mul (b65q_anAt_sum _ fun x _ ↦ b65e_movingPole_an p x _)
      have hAn : AnalyticAt ℂ (fun θ ↦ ∑ a ∈ Finset.range (k + 1),
          ((-1 : ℂ) ^ a * b65e_esym p a θ) *
            ((-1) ^ (k + 1 - a) * ∑ x : Fin 12, b65p_poles p θ (Sum.inr x) ^ (k + 1 - a))) 0 :=
        b65q_anAt_sum _ fun a ha ↦ (hfa a ha).mul (hga a ha)
      rw [b65q_T_const_mul _ (b65e_esym_an p (k + 1)), PowerSeries.coeff_C_mul,
        b65q_T_const_mul _ hAn, PowerSeries.coeff_C_mul,
        b65e_coeffT_finsum_mul _ _ _ hfa hga] at hL
      have hterm : ∀ r ∈ Finset.range (n + 1), ∀ a ∈ Finset.range (k + 1),
          PowerSeries.coeff r (b65q_T (fun θ ↦ (-1 : ℂ) ^ a * b65e_esym p a θ) 0) *
            PowerSeries.coeff (n - r) (b65q_T (fun θ ↦ (-1 : ℂ) ^ (k + 1 - a) *
              ∑ x : Fin 12, b65p_poles p θ (Sum.inr x) ^ (k + 1 - a)) 0) =
          (-1) ^ a * ((b65e_esymN a r : ℂ) * ((-1) ^ (k + 1 - a) *
            (b65e_powerTraceQ (k + 1 - a) (n - r) : ℂ))) := by
        intro r hr a ha
        have hr' := Finset.mem_range.mp hr
        have ha' := Finset.mem_range.mp ha
        rw [b65q_T_const_mul _ (b65e_esym_an p a), PowerSeries.coeff_C_mul,
          ih a (by omega) (by omega) r (by omega),
          b65q_T_const_mul _ (b65q_anAt_sum _ fun x _ ↦ b65e_movingPole_an p x _),
          PowerSeries.coeff_C_mul, b65e_powerTrace_T p O _ (by omega) _ (by omega)]
        ring
      rw [Finset.sum_congr rfl fun r hr ↦ Finset.sum_congr rfl fun a ha ↦ hterm r hr a ha,
        Finset.sum_comm] at hL
      have hc : ((k + 1 : ℕ) : ℚ) * b65e_esymQ (Fin.succ ⟨k, by omega⟩) ⟨n, hn⟩ =
          b65e_newtonQ (k + 1) n := b65e_esymQ_newton_table ⟨k, by omega⟩ ⟨n, hn⟩
      have hN : b65e_esymN (k + 1) n = b65e_esymQ (Fin.succ ⟨k, by omega⟩) ⟨n, hn⟩ := by
        simp only [b65e_esymN, show k + 1 < 13 by omega, hn, ↓reduceDIte]
        rfl
      rw [hN]
      have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      apply mul_left_cancel₀ hk0
      rw [hL]
      have hcast : ((k + 1 : ℕ) : ℂ) * (b65e_esymQ (Fin.succ ⟨k, by omega⟩) ⟨n, hn⟩ : ℂ) =
          ((((k + 1 : ℕ) : ℚ) * b65e_esymQ (Fin.succ ⟨k, by omega⟩) ⟨n, hn⟩ : ℚ) : ℂ) := by
        push_cast; ring
      rw [hcast, hc]
      unfold b65e_newtonQ
      push_cast
      simp only [Finset.mul_sum]

/-- Taylor coefficients of the coefficients of the branch polynomial. -/
theorem b65e_denominator_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) (i n : ℕ) (hn : n < 8) :
    PowerSeries.coeff n (b65q_T (fun θ ↦ (b65q_denominator (b65p_poles p θ)).coeff i) 0) =
      (b65e_DjQ i n : ℂ) := by
  simp only [b65e_denominator_coeff]
  unfold b65e_DjQ
  split_ifs with h
  · exact b65e_esym_T p O _ (by omega) n hn
  · rw [b65q_T_const, PowerSeries.coeff_C]
    split_ifs <;> simp

theorem b65e_denominator_an (p : Fin 12 → ℂ) (i : ℕ) :
    AnalyticAt ℂ (fun θ ↦ (b65q_denominator (b65p_poles p θ)).coeff i) 0 := by
  simp only [b65e_denominator_coeff]
  split_ifs
  · exact b65e_esym_an p _
  · exact analyticAt_const

end HodgeLean.Foundations.Program
