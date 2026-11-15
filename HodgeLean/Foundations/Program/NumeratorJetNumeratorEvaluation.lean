import HodgeLean.Foundations.Program.NumeratorJetBranchEvaluation
import HodgeLean.Foundations.Program.NumeratorJetExpansion

/-! # Taylor coefficients of the numerator array

The moving moments `Σ_x β_x w_{x,jj} t_x^m`, the coefficients of the polynomial parts of
`D_θ q_{jj}` and the numerator entries have Taylor coefficients given by the finite rational
formulas of `NumeratorJetNumeratorDefs.lean`, evaluated on the stored tables. The statements
take the table checks and the Taylor coefficients of the frames and left vectors as hypotheses;
the certificate and frame modules supply them.
-/

noncomputable section
open Set Metric Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65e_fibrePowerTrace (p : Fin 12 → ℂ) (O : b65p_Outputs p) (e : Fin 2) (v : Fin 6)
    (u : Fin 6 → ℚ) :
    ∑ x ∈ b65q_fibreSet e, p x ^ (v : ℕ) * b65e_coordinateEvalQ u (p x) =
      ∑ c : Fin 6, (u c : ℂ) * (b65e_powerMomentQ ⟨c.val + v.val, by omega⟩ e : ℂ) := by
  simp only [b65e_coordinateEvalQ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← b65e_powerMoment_sum p O ⟨c.val + v.val, by omega⟩ e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [pow_add]
  ring

theorem b65e_coordinateEval_sum {κ : Type*} (s : Finset κ) (f : κ → Fin 6 → ℚ) (z : ℂ) :
    b65e_coordinateEvalQ (fun c ↦ ∑ a ∈ s, f a c) z = ∑ a ∈ s, b65e_coordinateEvalQ (f a) z := by
  simp only [b65e_coordinateEvalQ, Rat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- The traced moving moments of a q-frame column. -/
def b65e_SqFun (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (jj : Fin 4) (b : Fin 3) (m : ℕ) (θ : ℂ) : ℂ :=
  ∑ x : Fin 12, ((∑ v : Fin 6,
    b65q_qFrame p R θ ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ b * p x ^ v.val) *
      b65q_left R θ x jj) * b65p_poles p θ (Sum.inr x) ^ m

/-- Taylor coefficients of `w_x(θ)_jj t_x(θ)^m` at a labelled root. -/
theorem b65e_leftPower_T (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hwa : ∀ x i, AnalyticAt ℂ (fun θ ↦ b65q_left O.residue θ x i) 0)
    (hwT : ∀ x i n, n < 8 → PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0) =
      b65e_coordinateEvalQ (b65e_leftCoordsQ (b65q_fibreIndex x) i (Fin.ofNat 8 n)) (p x))
    (hWT : ∀ e jj (m : Fin 13) (n : Fin 8) c, b65e_WTQ e jj m n c = b65e_WTFormulaQ e jj m n c)
    (x : Fin 12) (jj : Fin 4) (m : ℕ) (hm : m < 13) (n : ℕ) (hn : n < 8) :
    PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_left O.residue θ x jj *
      b65p_poles p θ (Sum.inr x) ^ m) 0) =
      b65e_coordinateEvalQ (b65e_WTN (b65q_fibreIndex x) jj m n) (p x) := by
  have hroot : (b65q_fibreC (b65q_fibreIndex x)).eval (p x) = 0 :=
    b65q_fibre_root O _ (by simp [b65q_fibreSet])
  rw [b65q_T_mul (hwa x jj) (b65e_movingPole_an p x m),
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hW : b65e_WTN (b65q_fibreIndex x) jj m n =
      fun c ↦ b65e_WTFormulaQ (b65q_fibreIndex x) jj m n c := by
    funext c
    simp only [b65e_WTN, hm, hn, ↓reduceDIte]
    exact hWT _ _ ⟨m, hm⟩ ⟨n, hn⟩ c
  rw [hW]
  unfold b65e_WTFormulaQ
  rw [b65e_coordinateEval_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha' := Finset.mem_range.mp ha
  rw [b65e_coordinateMulQ_eval _ _ _ _ hroot,
    b65e_movingPower_T p O x m (by omega) (n - a) (by omega)]
  congr 1
  exact hwT x jj a (by omega)

/-- Regrouping a sum over labelled moving poles and node powers by fibres. -/
theorem b65e_fibre_regroup (p : Fin 12 → ℂ) (O : b65p_Outputs p) (q : Fin 48 → ℂ)
    (W : Fin 2 → Fin 6 → ℚ) :
    ∑ xv : Fin 12 × Fin 6, q ⟨36 + 6 * (b65q_fibreIndex xv.1).val + xv.2.val, by omega⟩ *
        (p xv.1 ^ xv.2.val * b65e_coordinateEvalQ (W (b65q_fibreIndex xv.1)) (p xv.1)) =
      ∑ e : Fin 2, ∑ v : Fin 6, q ⟨36 + 6 * e.val + v.val, by omega⟩ *
        ∑ c : Fin 6, (W e c : ℂ) * (b65e_powerMomentQ ⟨c.val + v.val, by omega⟩ e : ℂ) := by
  have hfib : ∀ f : Fin 12 → ℂ, ∑ x, f x = ∑ e : Fin 2, ∑ x ∈ b65q_fibreSet e, f x :=
    fun f ↦ (Finset.sum_fiberwise Finset.univ b65q_fibreIndex f).symm
  rw [← Finset.univ_product_univ, Finset.sum_product, hfib]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have h1 : ∀ x ∈ b65q_fibreSet e,
      (∑ v : Fin 6, q ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ *
        (p x ^ v.val * b65e_coordinateEvalQ (W (b65q_fibreIndex x)) (p x))) =
      ∑ v : Fin 6, q ⟨36 + 6 * e.val + v.val, by omega⟩ *
        (p x ^ v.val * b65e_coordinateEvalQ (W e) (p x)) := by
    intro x hx
    have hx' : b65q_fibreIndex x = e := (Finset.mem_filter.mp hx).2
    subst hx'
    rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [← Finset.mul_sum, b65e_fibrePowerTrace p O e v]

/-- Taylor coefficients of the traced moving moments. -/
theorem b65e_Sq_T (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hqa : ∀ i b, AnalyticAt ℂ (fun θ ↦ b65q_qFrame p O.residue θ i b) 0)
    (hwa : ∀ x i, AnalyticAt ℂ (fun θ ↦ b65q_left O.residue θ x i) 0)
    (hqT : ∀ i b n, n < 8 → PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_qFrame p O.residue θ i b) 0) =
      (b65e_qFrameJet (Fin.ofNat 8 n) i b : ℂ))
    (hwT : ∀ x i n, n < 8 → PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0) =
      b65e_coordinateEvalQ (b65e_leftCoordsQ (b65q_fibreIndex x) i (Fin.ofNat 8 n)) (p x))
    (hWT : ∀ e jj (m : Fin 13) (n : Fin 8) c, b65e_WTQ e jj m n c = b65e_WTFormulaQ e jj m n c)
    (hSq : ∀ (m : Fin 13) jj b (n : Fin 8), b65e_SqQ m jj b n = b65e_SqFormulaQ m jj b n)
    (jj : Fin 4) (b : Fin 3) (m : ℕ) (hm : m < 13) (n : ℕ) (hn : n < 8) :
    PowerSeries.coeff n (b65q_T (b65e_SqFun p O.residue jj b m) 0) =
      (b65e_SqN m jj b n : ℂ) := by
  let F : Fin 12 × Fin 6 → ℂ → ℂ := fun xv θ ↦
    b65q_qFrame p O.residue θ ⟨36 + 6 * (b65q_fibreIndex xv.1).val + xv.2.val, by omega⟩ b
  let G : Fin 12 × Fin 6 → ℂ → ℂ := fun xv θ ↦
    p xv.1 ^ xv.2.val * (b65q_left O.residue θ xv.1 jj * b65p_poles p θ (Sum.inr xv.1) ^ m)
  have hfun : b65e_SqFun p O.residue jj b m =
      fun θ ↦ ∑ xv ∈ (Finset.univ : Finset (Fin 12 × Fin 6)), F xv θ * G xv θ := by
    funext θ
    rw [← Finset.univ_product_univ, Finset.sum_product]
    unfold b65e_SqFun
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    simp only [F, G]
    ring
  have hF : ∀ xv ∈ (Finset.univ : Finset (Fin 12 × Fin 6)), AnalyticAt ℂ (F xv) 0 :=
    fun xv _ ↦ hqa _ _
  have hG : ∀ xv ∈ (Finset.univ : Finset (Fin 12 × Fin 6)), AnalyticAt ℂ (G xv) 0 :=
    fun xv _ ↦ analyticAt_const.mul ((hwa _ _).mul (b65e_movingPole_an p _ m))
  rw [hfun, b65e_coeffT_finsum_mul _ F G hF hG]
  have hterm : ∀ r ∈ Finset.range (n + 1), ∀ xv : Fin 12 × Fin 6,
      PowerSeries.coeff r (b65q_T (F xv) 0) * PowerSeries.coeff (n - r) (b65q_T (G xv) 0) =
        (b65e_qFrameJet (Fin.ofNat 8 r)
          ⟨36 + 6 * (b65q_fibreIndex xv.1).val + xv.2.val, by omega⟩ b : ℂ) *
        (p xv.1 ^ xv.2.val * b65e_coordinateEvalQ
          (b65e_WTN (b65q_fibreIndex xv.1) jj m (n - r)) (p xv.1)) := by
    intro r hr xv
    have hr' := Finset.mem_range.mp hr
    simp only [F, G]
    rw [hqT _ _ r (by omega),
      b65q_T_const_mul (f := fun θ ↦ b65q_left O.residue θ xv.1 jj *
        b65p_poles p θ (Sum.inr xv.1) ^ m) _ ((hwa _ _).mul (b65e_movingPole_an p _ m)),
      PowerSeries.coeff_C_mul, b65e_leftPower_T p O hwa hwT hWT xv.1 jj m hm (n - r) (by omega)]
  rw [Finset.sum_congr rfl fun r hr ↦ Finset.sum_congr rfl fun xv _ ↦ hterm r hr xv]
  have hSqN : b65e_SqN m jj b n = b65e_SqFormulaQ m jj b n := by
    simp only [b65e_SqN, hm, hn, ↓reduceDIte]
    exact hSq ⟨m, hm⟩ jj b ⟨n, hn⟩
  rw [hSqN]
  unfold b65e_SqFormulaQ
  push_cast
  conv_rhs => arg 2; ext e; rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 2)))]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  exact b65e_fibre_regroup p O (fun i ↦ (b65e_qFrameJet (Fin.ofNat 8 r) i b : ℂ))
    (fun e ↦ b65e_WTN e jj m (n - r))

/-- The coefficient `k` of the polynomial part of `D_θ q_{jj}` for the q-frame column `b`. -/
def b65e_GFun (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (jj : Fin 4) (b : Fin 3) (k : ℕ) (θ : ℂ) : ℂ :=
  (∑ b' : Fin 9, b65q_qFrame p R θ ⟨4 * b'.val + jj.val, by omega⟩ b *
      ∑ i ∈ Finset.range 14, (b65q_denominator (b65p_poles p θ)).coeff i *
        ((b65e_LamQ b' i k : ℚ) : ℂ)) +
    ∑ m ∈ Finset.range (13 - k),
      (b65q_denominator (b65p_poles p θ)).coeff (k + 1 + m) * b65e_SqFun p R jj b m θ

theorem b65e_SqFun_an (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hqa : ∀ i b, AnalyticAt ℂ (fun θ ↦ b65q_qFrame p O.residue θ i b) 0)
    (hwa : ∀ x i, AnalyticAt ℂ (fun θ ↦ b65q_left O.residue θ x i) 0)
    (jj : Fin 4) (b : Fin 3) (m : ℕ) :
    AnalyticAt ℂ (b65e_SqFun p O.residue jj b m) 0 := by
  unfold b65e_SqFun
  apply b65q_anAt_sum
  intro x _
  exact ((b65q_anAt_sum _ fun v _ ↦ (hqa _ _).mul analyticAt_const).mul (hwa _ _)).mul
    (b65e_movingPole_an p x m)

theorem b65e_GFun_an (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hqa : ∀ i b, AnalyticAt ℂ (fun θ ↦ b65q_qFrame p O.residue θ i b) 0)
    (hwa : ∀ x i, AnalyticAt ℂ (fun θ ↦ b65q_left O.residue θ x i) 0)
    (jj : Fin 4) (b : Fin 3) (k : ℕ) :
    AnalyticAt ℂ (b65e_GFun p O.residue jj b k) 0 := by
  unfold b65e_GFun
  apply AnalyticAt.add
  · exact b65q_anAt_sum _ fun b' _ ↦ (hqa _ _).mul
      (b65q_anAt_sum _ fun i _ ↦ (b65e_denominator_an p i).mul analyticAt_const)
  · exact b65q_anAt_sum _ fun m _ ↦ (b65e_denominator_an p _).mul (b65e_SqFun_an p O hqa hwa jj b m)

/-- Taylor coefficients of the polynomial parts of `D_θ q_{jj}`. -/
theorem b65e_G_T (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hqa : ∀ i b, AnalyticAt ℂ (fun θ ↦ b65q_qFrame p O.residue θ i b) 0)
    (hwa : ∀ x i, AnalyticAt ℂ (fun θ ↦ b65q_left O.residue θ x i) 0)
    (hqT : ∀ i b n, n < 8 → PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_qFrame p O.residue θ i b) 0) =
      (b65e_qFrameJet (Fin.ofNat 8 n) i b : ℂ))
    (hwT : ∀ x i n, n < 8 → PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0) =
      b65e_coordinateEvalQ (b65e_leftCoordsQ (b65q_fibreIndex x) i (Fin.ofNat 8 n)) (p x))
    (hWT : ∀ e jj (m : Fin 13) (n : Fin 8) c, b65e_WTQ e jj m n c = b65e_WTFormulaQ e jj m n c)
    (hSq : ∀ (m : Fin 13) jj b (n : Fin 8), b65e_SqQ m jj b n = b65e_SqFormulaQ m jj b n)
    (hG : ∀ (k : Fin 13) jj b (n : Fin 8), b65e_GQ k jj b n = b65e_GFormulaQ k jj b n)
    (jj : Fin 4) (b : Fin 3) (k : ℕ) (hk : k < 13) (n : ℕ) (hn : n < 8) :
    PowerSeries.coeff n (b65q_T (b65e_GFun p O.residue jj b k) 0) = (b65e_GN k jj b n : ℂ) := by
  have hGN : b65e_GN k jj b n = b65e_GFormulaQ k jj b n := by
    simp only [b65e_GN, hk, hn, ↓reduceDIte]
    exact hG ⟨k, hk⟩ jj b ⟨n, hn⟩
  rw [hGN]
  unfold b65e_GFun b65e_GFormulaQ
  have hA : AnalyticAt ℂ (fun θ ↦ ∑ b' : Fin 9, b65q_qFrame p O.residue θ
      ⟨4 * b'.val + jj.val, by omega⟩ b * ∑ i ∈ Finset.range 14,
        (b65q_denominator (b65p_poles p θ)).coeff i * ((b65e_LamQ b' i k : ℚ) : ℂ)) 0 :=
    b65q_anAt_sum _ fun b' _ ↦ (hqa _ _).mul
      (b65q_anAt_sum _ fun i _ ↦ (b65e_denominator_an p i).mul analyticAt_const)
  have hB : AnalyticAt ℂ (fun θ ↦ ∑ m ∈ Finset.range (13 - k),
      (b65q_denominator (b65p_poles p θ)).coeff (k + 1 + m) *
        b65e_SqFun p O.residue jj b m θ) 0 :=
    b65q_anAt_sum _ fun m _ ↦ (b65e_denominator_an p _).mul (b65e_SqFun_an p O hqa hwa jj b m)
  rw [b65q_T_add hA hB, map_add]
  push_cast
  congr 1
  · rw [b65e_coeffT_finsum_mul (f := fun b' θ ↦ b65q_qFrame p O.residue θ
        ⟨4 * b'.val + jj.val, by omega⟩ b)
      (g := fun b' θ ↦ ∑ i ∈ Finset.range 14, (b65q_denominator (b65p_poles p θ)).coeff i *
        ((b65e_LamQ b' i k : ℚ) : ℂ)) _ (fun b' _ ↦ hqa _ _) (fun b' _ ↦ b65q_anAt_sum _
      fun i _ ↦ (b65e_denominator_an p i).mul analyticAt_const), Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ ↦ Finset.sum_congr rfl fun r hr ↦ ?_
    have hr' := Finset.mem_range.mp hr
    rw [hqT _ _ r (by omega), b65e_coeffT_finsum (f := fun i θ ↦
      (b65q_denominator (b65p_poles p θ)).coeff i * ((b65e_LamQ b' i k : ℚ) : ℂ)) _
      (fun i _ ↦ (b65e_denominator_an p i).mul analyticAt_const)]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hc : (fun θ ↦ (b65q_denominator (b65p_poles p θ)).coeff i *
        ((b65e_LamQ b' i k : ℚ) : ℂ)) = fun θ ↦ ((b65e_LamQ b' i k : ℚ) : ℂ) *
        (b65q_denominator (b65p_poles p θ)).coeff i := funext fun θ ↦ mul_comm _ _
    rw [hc, b65q_T_const_mul _ (b65e_denominator_an p i), PowerSeries.coeff_C_mul,
      b65e_denominator_T p O i _ (by omega)]
    ring
  · rw [b65e_coeffT_finsum_mul (f := fun m θ ↦ (b65q_denominator (b65p_poles p θ)).coeff
        (k + 1 + m)) (g := fun m θ ↦ b65e_SqFun p O.residue jj b m θ) _
      (fun m _ ↦ b65e_denominator_an p _)
      (fun m _ ↦ b65e_SqFun_an p O hqa hwa jj b m), Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm ↦ Finset.sum_congr rfl fun r hr ↦ ?_
    have hr' := Finset.mem_range.mp hr
    have hm' := Finset.mem_range.mp hm
    rw [b65e_denominator_T p O _ _ (by omega),
      b65e_Sq_T p O hqa hwa hqT hwT hWT hSq jj b m (by omega) (n - r) (by omega)]

/-- **Taylor coefficients of the numerator entries**, from the table checks. -/
theorem b65e_numerator_T (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hqa : ∀ i b, AnalyticAt ℂ (fun θ ↦ b65q_qFrame p O.residue θ i b) 0)
    (hwa : ∀ x i, AnalyticAt ℂ (fun θ ↦ b65q_left O.residue θ x i) 0)
    (hqT : ∀ i b n, n < 8 → PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_qFrame p O.residue θ i b) 0) =
      (b65e_qFrameJet (Fin.ofNat 8 n) i b : ℂ))
    (hwT : ∀ x i n, n < 8 → PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0) =
      b65e_coordinateEvalQ (b65e_leftCoordsQ (b65q_fibreIndex x) i (Fin.ofNat 8 n)) (p x))
    (hra : ∀ i a, AnalyticAt ℂ (fun θ ↦ b65q_rFrame p O.residue θ i a) 0)
    (hrT : ∀ i a n, n < 8 → PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_rFrame p O.residue θ i a) 0) =
      (b65e_rFrameJet (Fin.ofNat 8 n) i a : ℂ))
    (hWT : ∀ e jj (m : Fin 13) (n : Fin 8) c, b65e_WTQ e jj m n c = b65e_WTFormulaQ e jj m n c)
    (hSq : ∀ (m : Fin 13) jj b (n : Fin 8), b65e_SqQ m jj b n = b65e_SqFormulaQ m jj b n)
    (hG : ∀ (k : Fin 13) jj b (n : Fin 8), b65e_GQ k jj b n = b65e_GFormulaQ k jj b n)
    (a b : Fin 3) (j : Fin 10) (n : ℕ) (hn : n < 8) :
    PowerSeries.coeff n (b65q_T (fun θ ↦
      b65e_numerator p O.residue θ (finProdFinEquiv (a, b)) j) 0) =
      (b65e_NFormulaQ n a b j : ℂ) := by
  have hfun : (fun θ ↦ b65e_numerator p O.residue θ (finProdFinEquiv (a, b)) j) =
      fun θ ↦ ∑ jj : Fin 4, ∑ k ∈ Finset.range 13,
        (∑ a' : Fin 9, b65q_rFrame p O.residue θ ⟨4 * a'.val + jj.val, by omega⟩ a *
          ((b65e_LamQ a' k j : ℚ) : ℂ)) * b65e_GFun p O.residue jj b k θ := by
    funext θ
    simp only [b65e_numerator, Equiv.symm_apply_apply, b65q_frameProduct]
    rw [b65e_numerator_expand]
    simp only [b65e_GFun, b65e_SqFun]
  have hRa : ∀ jj : Fin 4, ∀ k ∈ Finset.range 13, AnalyticAt ℂ (fun θ ↦
      ∑ a' : Fin 9, b65q_rFrame p O.residue θ ⟨4 * a'.val + jj.val, by omega⟩ a *
        ((b65e_LamQ a' k j : ℚ) : ℂ)) 0 :=
    fun jj k _ ↦ b65q_anAt_sum _ fun a' _ ↦ (hra _ _).mul analyticAt_const
  rw [hfun, b65e_coeffT_finsum (f := fun jj θ ↦ ∑ k ∈ Finset.range 13,
      (∑ a' : Fin 9, b65q_rFrame p O.residue θ ⟨4 * a'.val + jj.val, by omega⟩ a *
        ((b65e_LamQ a' k j : ℚ) : ℂ)) * b65e_GFun p O.residue jj b k θ) _
    (fun jj _ ↦ b65q_anAt_sum _ fun k hk ↦
    (hRa jj k hk).mul (b65e_GFun_an p O hqa hwa jj b k))]
  unfold b65e_NFormulaQ
  push_cast
  refine Finset.sum_congr rfl fun jj _ ↦ ?_
  rw [b65e_coeffT_finsum_mul (f := fun k θ ↦ ∑ a' : Fin 9,
      b65q_rFrame p O.residue θ ⟨4 * a'.val + jj.val, by omega⟩ a * ((b65e_LamQ a' k j : ℚ) : ℂ))
    (g := fun k θ ↦ b65e_GFun p O.residue jj b k θ) _ (hRa jj)
    (fun k _ ↦ b65e_GFun_an p O hqa hwa jj b k), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl fun r hr ↦ ?_
  have hr' := Finset.mem_range.mp hr
  have hk' := Finset.mem_range.mp hk
  have h1 : PowerSeries.coeff (n - r) (b65q_T (b65e_GFun p O.residue jj b k) 0) =
      (b65e_GN k jj b (n - r) : ℂ) :=
    b65e_G_T p O hqa hwa hqT hwT hWT hSq hG jj b k hk' (n - r) (by omega)
  have h2 : PowerSeries.coeff r (b65q_T (fun θ ↦ ∑ a' : Fin 9,
      b65q_rFrame p O.residue θ ⟨4 * a'.val + jj.val, by omega⟩ a *
        ((b65e_LamQ a' k j : ℚ) : ℂ)) 0) =
      ∑ a' : Fin 9, ((b65e_LamQ a' k j : ℚ) : ℂ) *
        (b65e_rFrameJet (Fin.ofNat 8 r) ⟨4 * a'.val + jj.val, by omega⟩ a : ℂ) := by
    rw [b65e_coeffT_finsum (f := fun a' θ ↦ b65q_rFrame p O.residue θ
      ⟨4 * a'.val + jj.val, by omega⟩ a * ((b65e_LamQ a' k j : ℚ) : ℂ)) _
      (fun a' _ ↦ (hra ⟨4 * a'.val + jj.val, by omega⟩ a).mul analyticAt_const)]
    refine Finset.sum_congr rfl fun a' _ ↦ ?_
    have h3 := hrT ⟨4 * a'.val + jj.val, by omega⟩ a r (by omega)
    have h4 : (fun θ ↦ b65q_rFrame p O.residue θ ⟨4 * a'.val + jj.val, by omega⟩ a *
        ((b65e_LamQ a' k j : ℚ) : ℂ)) = fun θ ↦ ((b65e_LamQ a' k j : ℚ) : ℂ) *
        b65q_rFrame p O.residue θ ⟨4 * a'.val + jj.val, by omega⟩ a :=
      funext fun θ ↦ mul_comm _ _
    rw [h4, b65q_T_const_mul _ (hra ⟨4 * a'.val + jj.val, by omega⟩ a), PowerSeries.coeff_C_mul,
      h3]
  exact congrArg₂ (· * ·) h2 h1

end HodgeLean.Foundations.Program
