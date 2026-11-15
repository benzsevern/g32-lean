import HodgeLean.Foundations.Program.NumeratorJetRegularPole0
import HodgeLean.Foundations.Program.NumeratorJetRegularPole1
import HodgeLean.Foundations.Program.NumeratorJetRegularPole2
import HodgeLean.Foundations.Program.NumeratorJetRegularPole3
import HodgeLean.Foundations.Program.NumeratorJetBasisEvaluation
import HodgeLean.Foundations.Program.NumeratorJetFixedContractionEvaluation

/-! # Taylor coefficients of the regular-part coefficients along the path -/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- The Taylor series of an affine function. -/
theorem b65e_T_affine (d V : ℂ) :
    b65q_T (fun θ ↦ d + θ * V) 0 = PowerSeries.C d + PowerSeries.C V * PowerSeries.X := by
  rw [b65q_T_add (f := fun _ ↦ d) (g := fun θ ↦ θ * V) analyticAt_const
    (analyticAt_id.mul analyticAt_const), b65q_T_const,
    show (fun θ : ℂ ↦ θ * V) = fun θ ↦ V * θ by funext θ; ring,
    b65q_T_const_mul (f := fun θ ↦ θ) V analyticAt_id, b65q_T_id]
  simp

/-- Coefficients of the product of an affine series with another series. -/
theorem b65e_coeff_affine_mul (d V : ℂ) (g : PowerSeries ℂ) (m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.C d + PowerSeries.C V * PowerSeries.X) * g) =
      d * PowerSeries.coeff m g +
        if m = 0 then 0 else V * PowerSeries.coeff (m - 1) g := by
  rw [add_mul, map_add, PowerSeries.coeff_C_mul, mul_assoc, PowerSeries.coeff_C_mul]
  rcases m with _ | m
  · simp
  · rw [PowerSeries.coeff_succ_X_mul]
    simp

/-- Inverse powers of an affine function have the coefficients of the linear recursion. -/
theorem b65e_invPower_T (d V : ℂ) (hd : d ≠ 0) (L M : ℕ) (c : ℕ → ℕ → ℂ)
    (hc : ∀ l < L, ∀ m < M, d * c l m + (if m = 0 then 0 else V * c l (m - 1)) =
      if l = 0 then (if m = 0 then 1 else 0) else c (l - 1) m) :
    ∀ l < L, ∀ m < M,
      PowerSeries.coeff m (b65q_T (fun θ ↦ ((d + θ * V) ^ (l + 1))⁻¹) 0) = c l m := by
  have han (l : ℕ) : AnalyticAt ℂ (fun θ ↦ ((d + θ * V) ^ (l + 1))⁻¹) 0 :=
    ((analyticAt_const.add (analyticAt_id.mul analyticAt_const)).pow _).inv
      (by simp [hd])
  have hev : ∀ᶠ θ in 𝓝 (0 : ℂ), d + θ * V ≠ 0 :=
    (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually_ne
      (by simp [hd])
  have hrel (l : ℕ) (m : ℕ) :
      d * PowerSeries.coeff m (b65q_T (fun θ ↦ ((d + θ * V) ^ (l + 1))⁻¹) 0) +
        (if m = 0 then 0 else
          V * PowerSeries.coeff (m - 1) (b65q_T (fun θ ↦ ((d + θ * V) ^ (l + 1))⁻¹) 0)) =
      if l = 0 then (if m = 0 then 1 else 0) else
        PowerSeries.coeff m (b65q_T (fun θ ↦ ((d + θ * V) ^ (l - 1 + 1))⁻¹) 0) := by
    rw [← b65e_coeff_affine_mul, ← b65e_T_affine,
      ← b65q_T_mul (f := fun θ ↦ d + θ * V) (g := fun θ ↦ ((d + θ * V) ^ (l + 1))⁻¹)
        (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (han l)]
    rcases l with _ | l
    · simp only [↓reduceIte]
      rw [b65q_T_congr (g := fun _ ↦ 1) (by
        filter_upwards [hev] with θ hθ
        rw [zero_add, pow_one, mul_inv_cancel₀ hθ]), b65q_T_const, PowerSeries.coeff_C]
    · simp only [show l + 1 ≠ 0 by omega, ↓reduceIte]
      rw [b65q_T_congr (g := fun θ ↦ ((d + θ * V) ^ (l + 1 - 1 + 1))⁻¹) (by
        filter_upwards [hev] with θ hθ
        rw [show l + 1 - 1 + 1 = l + 1 by omega, pow_succ' _ (l + 1), mul_inv,
          ← mul_assoc, mul_inv_cancel₀ hθ, one_mul])]
  intro l
  induction l with
  | zero =>
    intro hl m
    induction m with
    | zero =>
      intro hm
      have h1 := hrel 0 0
      have h2 := hc 0 hl 0 hm
      simp only [↓reduceIte, add_zero] at h1 h2
      exact mul_left_cancel₀ hd (h1.trans h2.symm)
    | succ m ih =>
      intro hm
      have h1 := hrel 0 (m + 1)
      have h2 := hc 0 hl (m + 1) hm
      simp only [↓reduceIte, show m + 1 ≠ 0 by omega, Nat.add_sub_cancel] at h1 h2
      rw [ih (by omega)] at h1
      exact mul_left_cancel₀ hd (add_right_cancel (h1.trans h2.symm))
  | succ l ihl =>
    intro hl m
    induction m with
    | zero =>
      intro hm
      have h1 := hrel (l + 1) 0
      have h2 := hc (l + 1) hl 0 hm
      simp only [↓reduceIte, add_zero, show l + 1 ≠ 0 by omega, Nat.add_sub_cancel] at h1 h2
      rw [ihl (by omega) 0 hm] at h1
      exact mul_left_cancel₀ hd (h1.trans h2.symm)
    | succ m ih =>
      intro hm
      have h1 := hrel (l + 1) (m + 1)
      have h2 := hc (l + 1) hl (m + 1) hm
      simp only [show m + 1 ≠ 0 by omega, show l + 1 ≠ 0 by omega, ↓reduceIte,
        Nat.add_sub_cancel] at h1 h2
      rw [ih (by omega), ihl (by omega) (m + 1) hm] at h1
      exact mul_left_cancel₀ hd (add_right_cancel (h1.trans h2.symm))

/-- The inverse-power recursion checks assembled over poles and fibres. -/
theorem b65e_invPower_rec (k : Fin 4) (e : Fin 2) (l : Fin 5) (m : Fin 8) (c : Fin 6) :
    b65e_invPowerLhsQ k e l m c = b65e_invPowerRhsQ k e l m c := by
  fin_cases k <;> fin_cases e
  · exact b65e_invPower_rec_0_0 l m c
  · exact b65e_invPower_rec_0_1 l m c
  · exact b65e_invPower_rec_1_0 l m c
  · exact b65e_invPower_rec_1_1 l m c
  · exact b65e_invPower_rec_2_0 l m c
  · exact b65e_invPower_rec_2_1 l m c
  · exact b65e_invPower_rec_3_0 l m c
  · exact b65e_invPower_rec_3_1 l m c

/-- Coordinates of `x − t_k` evaluate to the shifted root. -/
theorem b65e_shiftCoords_eval (k : Fin 4) (z : ℂ) :
    b65e_coordinateEvalQ (b65e_shiftCoordsQ k) z = z - b65p_fixedPole k := by
  simp [b65e_coordinateEvalQ, b65e_shiftCoordsQ, Fin.sum_univ_succ, b65q_fixedPole_cast]
  ring

/-- The fibre value of a labelled root is its fibre. -/
theorem b65e_fibreValue_index (x : Fin 12) :
    b65q_fibreValue (b65q_fibreIndex x) = b65p_fibre x := by
  fin_cases x <;> decide +kernel

/-- The moving pole relative to a fixed pole is affine with the root velocity. -/
theorem b65e_poles_sub_inl (p : Fin 12 → ℂ) (θ : ℂ) (x : Fin 12) (k : Fin 4) :
    b65p_poles p θ (.inr x) - b65p_poles p θ (.inl k) =
      (p x - b65p_fixedPole k) + θ * b65p_V (b65p_fibre x) (p x) := by
  simp only [b65p_poles, Sum.elim_inr, Sum.elim_inl]
  ring

/-- The inverse powers of a moving-to-fixed pole difference have the stored coordinates. -/
theorem b65e_invPower_moving_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4)
    (x : Fin 12) : ∀ l < 5, ∀ m < 8,
      PowerSeries.coeff m (b65q_T (fun θ ↦
        ((b65p_poles p θ (.inr x) - b65p_poles p θ (.inl k)) ^ (l + 1))⁻¹) 0) =
      b65e_coordinateEvalQ
        (b65e_invPowerCoordsQ k (b65q_fibreIndex x) (Fin.ofNat 5 l) (Fin.ofNat 8 m)) (p x) := by
  have hx : x ∈ b65q_fibreSet (b65q_fibreIndex x) := by
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hz := b65q_fibre_root O _ hx
  have hfun (l : ℕ) : (fun θ ↦
      ((b65p_poles p θ (.inr x) - b65p_poles p θ (.inl k)) ^ (l + 1))⁻¹) =
      fun θ ↦ (((p x - b65p_fixedPole k) + θ * b65p_V (b65p_fibre x) (p x)) ^ (l + 1))⁻¹ := by
    funext θ
    rw [b65e_poles_sub_inl]
  intro l hl m hm
  rw [hfun l]
  revert l m
  apply b65e_invPower_T _ _ (b65q_fibre_ne_fixed O _ k hx)
  intro l hl m hm
  have h5 : ((Fin.ofNat 5 l : Fin 5) : ℕ) = l := by simp [Nat.mod_eq_of_lt hl]
  have h8 : ((Fin.ofNat 8 m : Fin 8) : ℕ) = m := by simp [Nat.mod_eq_of_lt hm]
  set H := fun a b ↦ b65e_invPowerCoordsQ k (b65q_fibreIndex x) (Fin.ofNat 5 a) (Fin.ofNat 8 b)
    with hH
  have hr : b65e_coordinateEvalQ (fun c ↦
      b65e_coordinateMulQ (b65q_fibreIndex x) (b65e_shiftCoordsQ k) (H l m) c +
        (if m = 0 then 0 else b65e_coordinateMulQ (b65q_fibreIndex x)
          (b65e_velocityQ (b65q_fibreIndex x)) (H l (m - 1)) c)) (p x) =
      b65e_coordinateEvalQ (fun c ↦ if l = 0 then (if m = 0 ∧ c = 0 then 1 else 0)
        else H (l - 1) m c) (p x) := by
    congr 1
    funext c
    have h := b65e_invPower_rec k (b65q_fibreIndex x) (Fin.ofNat 5 l) (Fin.ofNat 8 m) c
    simp only [b65e_invPowerLhsQ, b65e_invPowerRhsQ, h5, h8] at h
    simp only [hH]
    exact h
  rw [b65e_coordinateEvalQ_add, b65e_coordinateMulQ_eval _ _ _ _ hz,
    b65e_shiftCoords_eval] at hr
  have e1 : b65e_coordinateEvalQ (fun c ↦ if m = 0 then 0 else
      b65e_coordinateMulQ (b65q_fibreIndex x) (b65e_velocityQ (b65q_fibreIndex x))
        (H l (m - 1)) c) (p x) =
      if m = 0 then 0 else b65p_V (b65p_fibre x) (p x) * b65e_coordinateEvalQ (H l (m - 1)) (p x) := by
    by_cases hm0 : m = 0
    · simp [hm0, b65e_coordinateEvalQ]
    · simp only [hm0, ↓reduceIte]
      rw [b65e_coordinateMulQ_eval _ _ _ _ hz, ← b65e_fibreValue_index, b65e_velocityQ_eval]
      rfl
  have e2 : b65e_coordinateEvalQ (fun c ↦ if l = 0 then (if m = 0 ∧ c = 0 then 1 else 0)
      else H (l - 1) m c) (p x) =
      if l = 0 then (if m = 0 then 1 else 0) else b65e_coordinateEvalQ (H (l - 1) m) (p x) := by
    by_cases hl0 : l = 0
    · by_cases hm0 : m = 0
      · simp [hl0, hm0, b65e_coordinateEvalQ, Fin.sum_univ_succ]
      · simp [hl0, hm0, b65e_coordinateEvalQ]
    · simp only [hl0, ↓reduceIte]
  rw [e1, e2] at hr
  exact hr

/-- Taylor coefficients commute with finite sums of analytic matrix germs. -/
theorem b65e_TC_finsetSum {m n κ : Type*} (s : Finset κ) (F : κ → ℂ → Matrix m n ℂ)
    (hF : ∀ q ∈ s, ∀ i j, AnalyticAt ℂ (fun θ ↦ F q θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ ∑ q ∈ s, F q θ) k = ∑ q ∈ s, b65e_TC (F q) k := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply, Matrix.sum_apply]
  have hs : b65q_T (fun θ ↦ ∑ q ∈ s, F q θ i j) 0 = ∑ q ∈ s, b65q_T (fun θ ↦ F q θ i j) 0 :=
    b65q_T_sum s fun q hq ↦ hF q hq i j
  rw [hs, map_sum]

/-- Taylor coefficients of an analytic scalar multiple of an analytic matrix germ. -/
theorem b65e_TC_scalar {m n : Type*} (c : ℂ → ℂ) (F : ℂ → Matrix m n ℂ)
    (hc : AnalyticAt ℂ c 0) (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ c θ • F θ) k =
      ∑ a ∈ Finset.range (k + 1), PowerSeries.coeff a (b65q_T c 0) • b65e_TC F (k - a) := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  have hm : b65q_T (fun θ ↦ c θ * F θ i j) 0 = b65q_T c 0 * b65q_T (fun θ ↦ F θ i j) 0 :=
    b65q_T_mul hc (hF i j)
  rw [hm, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Taylor coefficients of a negated scalar germ. -/
theorem b65e_T_neg_coeff (f : ℂ → ℂ) (k : ℕ) :
    PowerSeries.coeff k (b65q_T (fun θ ↦ -f θ) 0) = -PowerSeries.coeff k (b65q_T f 0) := by
  simp only [b65q_T_coeff]
  rw [show (fun θ ↦ -f θ) = -f from rfl, iteratedDeriv_neg, neg_div]

/-- The regular-part trace checks assembled over poles and orders. -/
theorem b65e_taylorJet_table (k : Fin 4) (l : Fin 5) (n : Fin 8) :
    b65e_taylorJetQ k l n = b65e_taylorFixedQ k l n - b65e_taylorMovingQ k l n := by
  fin_cases k <;> fin_cases l
  · exact b65e_taylorJet_table_0_0 n
  · exact b65e_taylorJet_table_0_1 n
  · exact b65e_taylorJet_table_0_2 n
  · exact b65e_taylorJet_table_0_3 n
  · exact b65e_taylorJet_table_0_4 n
  · exact b65e_taylorJet_table_1_0 n
  · exact b65e_taylorJet_table_1_1 n
  · exact b65e_taylorJet_table_1_2 n
  · exact b65e_taylorJet_table_1_3 n
  · exact b65e_taylorJet_table_1_4 n
  · exact b65e_taylorJet_table_2_0 n
  · exact b65e_taylorJet_table_2_1 n
  · exact b65e_taylorJet_table_2_2 n
  · exact b65e_taylorJet_table_2_3 n
  · exact b65e_taylorJet_table_2_4 n
  · exact b65e_taylorJet_table_3_0 n
  · exact b65e_taylorJet_table_3_1 n
  · exact b65e_taylorJet_table_3_2 n
  · exact b65e_taylorJet_table_3_3 n
  · exact b65e_taylorJet_table_3_4 n

/-- The regular-part coefficients have the stored Taylor coefficients through order seven. -/
theorem b65e_taylor_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) (l : ℕ) (hl : l < 5)
    (n : ℕ) (hn : n < 8) :
    b65e_TC (fun θ ↦ b65q_taylor (b65p_poles p θ) (b65q_res O.residue θ) k l) n =
      (b65e_taylorJetQ k (Fin.ofNat 5 l) (Fin.ofNat 8 n)).map ι := by
  have h5 : ((Fin.ofNat 5 l : Fin 5) : ℕ) = l := by simp [Nat.mod_eq_of_lt hl]
  have h8 : ((Fin.ofNat 8 n : Fin 8) : ℕ) = n := by simp [Nat.mod_eq_of_lt hn]
  have hA : ∀ q i j, AnalyticAt ℂ (fun θ ↦ b65q_res O.residue θ q i j) 0 :=
    fun q i j ↦ b65q_MatAn.res O q i j 0 (mem_ball_self O.radius_pos)
  have hne0 : ∀ q, q ≠ Sum.inl k →
      b65p_poles p 0 q - b65p_poles p 0 (Sum.inl k) ≠ 0 := fun q hq ↦
    sub_ne_zero.mpr fun h ↦ hq (O.poles_injective 0 (mem_ball_self O.radius_pos) h)
  have hc : ∀ q, q ≠ Sum.inl k → AnalyticAt ℂ (fun θ ↦
      -((b65p_poles p θ q - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹) 0 := fun q hq ↦
    ((((b65q_poles_an p univ q) 0 trivial).sub
      ((b65q_poles_an p univ _) 0 trivial)).pow _).inv (pow_ne_zero _ (hne0 q hq)) |>.neg
  unfold b65q_taylor
  rw [b65e_TC_finsetSum]
  swap
  · intro q _ i j
    by_cases hq : q = Sum.inl k
    · simp only [hq, ↓reduceIte, Matrix.zero_apply]
      exact analyticAt_const
    · simp only [hq, ↓reduceIte, Matrix.smul_apply, smul_eq_mul]
      exact (hc q hq).mul (hA q i j)
  rw [Fintype.sum_sum_type, b65e_taylorJet_table, Matrix.map_sub _ (map_sub ι), sub_eq_add_neg]
  congr 1
  · have hfix : ∀ r : Fin 4, b65e_TC (fun θ ↦ if (Sum.inl r : Fin 4 ⊕ Fin 12) = Sum.inl k then 0
        else (-((b65p_poles p θ (Sum.inl r) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹) •
          b65q_res O.residue θ (Sum.inl r)) n =
        (if r = k then 0 else
          (-((b65k_fixed r - b65k_fixed k) ^ (l + 1))⁻¹ : ℚ) • b65e_fixedJet (Fin.ofNat 8 n) r).map ι := by
      intro r
      by_cases hr : r = k
      · subst hr
        simp only [↓reduceIte, b65e_TC_const]
        ext i j
        simp
      · have hq : (Sum.inl r : Fin 4 ⊕ Fin 12) ≠ Sum.inl k := fun h ↦ hr (Sum.inl_injective h)
        simp only [hq, hr, ↓reduceIte, b65q_poles_inl]
        rw [b65e_TC_smul _ (hA _), b65e_res_TC_inl p O r n hn]
        ext i j
        simp [Matrix.map_apply]
    rw [Finset.sum_congr rfl fun r _ ↦ hfix r]
    unfold b65e_taylorFixedQ
    ext i j
    simp only [Matrix.sum_apply, Matrix.map_apply, h5]
    rw [map_sum]
  · have hmov : ∀ x : Fin 12, b65e_TC (fun θ ↦ if (Sum.inr x : Fin 4 ⊕ Fin 12) = Sum.inl k then 0
        else (-((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹) •
          b65q_res O.residue θ (Sum.inr x)) n =
        ∑ a ∈ Finset.range (n + 1), (-b65e_coordinateEvalQ (b65e_invPowerCoordsQ k
          (b65q_fibreIndex x) (Fin.ofNat 5 l) (Fin.ofNat 8 a)) (p x)) •
            b65e_storedResidue p (n - a) (Sum.inr x) := by
      intro x
      simp only [reduceCtorEq, ↓reduceIte]
      rw [b65e_TC_scalar _ _ (hc _ Sum.inr_ne_inl) (hA _)]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      rw [b65e_T_neg_coeff, b65e_invPower_moving_T p O k x l hl a (by omega),
        b65e_res_TC p O _ (n - a) (by omega)]
    rw [Finset.sum_congr rfl fun x _ ↦ hmov x]
    unfold b65e_taylorMovingQ
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, h8,
      Matrix.neg_apply]
    rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
    simp only [Rat.coe_castHom]
    push_cast
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have hterm : ∀ x ∈ Finset.univ.filter (fun x ↦ b65q_fibreIndex x = e),
        -b65e_coordinateEvalQ (b65e_invPowerCoordsQ k (b65q_fibreIndex x) (Fin.ofNat 5 l)
          (Fin.ofNat 8 a)) (p x) * b65e_storedResidue p (n - a) (Sum.inr x) i j =
        -((∑ c : Fin 6, (b65e_invPowerCoordsQ k e (Fin.ofNat 5 l) (Fin.ofNat 8 a) c : ℂ) *
            p x ^ (c : ℕ)) *
          (∑ d : Fin 6, (b65e_movingJet (Fin.ofNat 8 (n - a)) e d i j : ℂ) * p x ^ (d : ℕ))) := by
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
      simp only [b65e_coordinateEvalQ, b65e_storedResidue, b65e_residueJet, Matrix.sum_apply,
        Matrix.smul_apply, Matrix.map_apply, Rat.coe_castHom, smul_eq_mul,
        (Finset.mem_filter.mp hx).2]
      rw [neg_mul]
      congr 2
      apply Finset.sum_congr rfl
      intro d _
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    congr 1
    have hfs : Finset.univ.filter (fun x ↦ b65q_fibreIndex x = e) = b65q_fibreSet e := rfl
    rw [hfs, b65e_coordinateProduct_sum p O e]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring

end HodgeLean.Foundations.Program
