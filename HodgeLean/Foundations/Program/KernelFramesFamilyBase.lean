import HodgeLean.Foundations.Program.KernelFramesFamilyMirror
import HodgeLean.Foundations.Program.KernelFramesFamilySpectral

/-! # B6-5 stage 5d, family part: the systems at the base parameter

Transport of the complex definitions at `θ = 0` to their rational mirrors: residues, initial
eigenbases (`b65q_basis_zero`), left eigenvectors (`b65q_left_zero`), Taylor coefficients of the
regular parts (through the root sums), the normal-form gauge, the inverse series and the Laurent
entries; hence the two family systems at `θ = 0` are the printed systems.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Matrix Polynomial
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

theorem b65q_mat_operator (M : Matrix (Fin 4) (Fin 4) ℂ) : b65q_mat (b65r_operator M) = M := by
  ext i j
  simp [b65q_mat, b65r_operator, LinearMap.toMatrix'_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply]

theorem b65q_B0_cast : b65r_B0 = b65q_B0Q.map ι := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [b65r_B0, b65q_B0Q, diagonal]

theorem b65q_B_cast (e : Fin 2) : (![b65r_B5, b65r_Bneg7] : Fin 2 → _) e = (b65q_BQ e).map ι := by
  ext i j
  fin_cases e <;> fin_cases i <;> fin_cases j <;>
    norm_num [b65r_B5, b65r_Bneg7, b65q_BQ, b65q_uQ, b65k_left]

theorem b65q_fixedResidue_cast (k : Fin 4) :
    b65p_fixedResidue k = (b65q_fixedResQ k).map ι := by
  have h5 := b65q_B_cast 0
  have h7 := b65q_B_cast 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h5 h7
  ext i j
  fin_cases k <;>
    simp [b65p_fixedResidue, b65q_fixedResQ, b65r_Binf, b65q_BinfQ, b65q_B0_cast, h5, h7]

theorem b65q_movingResidue_cast (x : Fin 12) :
    b65p_movingResidue x = (b65q_BQ (b65q_fibreIndex x)).map ι := by
  have h5 := b65q_B_cast 0
  have h7 := b65q_B_cast 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h5 h7
  unfold b65p_movingResidue b65q_fibreIndex
  split_ifs <;> assumption

theorem b65q_res_zero_inl {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k : Fin 4) :
    b65q_res O.residue 0 (Sum.inl k) = (b65q_fixedResQ k).map ι := by
  rw [b65q_res, O.residue_zero, b65p_initialResidue, Sum.elim_inl, b65q_mat_operator,
    b65q_fixedResidue_cast]

theorem b65q_res_zero_inr {p : Fin 12 → ℂ} (O : b65p_Outputs p) (x : Fin 12) :
    b65q_res O.residue 0 (Sum.inr x) = (b65q_BQ (b65q_fibreIndex x)).map ι := by
  rw [b65q_res, O.residue_zero, b65p_initialResidue, Sum.elim_inr, b65q_mat_operator,
    b65q_movingResidue_cast]

theorem b65q_eigen0_cast (k : Fin 4) : b65q_eigen0 k = (b65q_P0Q k).map ι := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [b65q_eigen0, b65q_P0Q, b65q_E, b65q_EQ, Matrix.one_apply]

theorem b65q_P0Q_mul_inv (k : Fin 4) : b65q_P0Q k * b65q_P0invQ k = 1 := by
  fin_cases k <;> decide +kernel

theorem b65q_fixed_eig_Q (k : Fin 4) :
    b65q_fixedResQ k * b65q_P0Q k = b65q_P0Q k * diagonal (b65q_lamQ k) := by
  fin_cases k <;> decide +kernel

theorem b65q_exponents_cast (k : Fin 4) : b65p_exponents k = fun i ↦ ((b65q_lamQ k i : ℚ) : ℂ) := by
  funext i
  fin_cases k <;> fin_cases i <;> norm_num [b65p_exponents, b65q_lamQ]

theorem b65q_eigen0_inv (k : Fin 4) : (b65q_eigen0 k)⁻¹ = (b65q_P0invQ k).map ι := by
  rw [b65q_eigen0_cast]
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, b65q_P0Q_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem b65q_eigen0_isUnit (k : Fin 4) : IsUnit (b65q_eigen0 k) := by
  refine (isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (B := (b65q_P0invQ k).map ι) ?_)
  rw [b65q_eigen0_cast, ← Matrix.map_mul, b65q_P0Q_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem b65q_fixed_eig (k : Fin 4) :
    (b65q_fixedResQ k).map ι * b65q_eigen0 k = b65q_eigen0 k * diagonal (b65p_exponents k) := by
  rw [b65q_eigen0_cast, ← Matrix.map_mul, b65q_fixed_eig_Q, Matrix.map_mul, b65q_exponents_cast]
  congr 1
  ext i j
  simp [diagonal]
  split_ifs <;> simp

/-- **Base eigenbases.** -/
theorem b65q_basis_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    b65q_basis O.residue 0 = b65q_eigen0 := by
  funext k
  rw [b65q_basis, b65q_res_zero_inl]
  exact b65q_eigenbasis_base _ _ _ (b65q_eigen0_isUnit k) (b65q_fixed_eig k)

theorem b65q_leftEigen_base (e : Fin 2) :
    b65q_leftEigen ((![b65r_B5, b65r_Bneg7] : Fin 2 → _) e) (b65q_u e) =
      fun i ↦ ((b65k_left e i : ℚ) : ℂ) := by
  ext i
  fin_cases e <;> fin_cases i <;>
    simp [b65q_leftEigen, b65r_B5, b65r_Bneg7, b65q_u, b65k_left, Matrix.trace, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- **Base left eigenvectors.** -/
theorem b65q_left_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (j : Fin 12) :
    b65q_left O.residue 0 j = fun i ↦ ((b65k_left (b65q_fibreIndex j) i : ℚ) : ℂ) := by
  rw [b65q_left, b65q_res_zero_inr, ← b65q_B_cast, b65q_leftEigen_base]

theorem b65q_poles_zero (p : Fin 12 → ℂ) : b65p_poles p 0 = Sum.elim b65p_fixedPole p := by
  funext q; rcases q with k | x <;> simp [b65p_poles]

/-- **Base Taylor coefficients.** -/
theorem b65q_taylor_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k : Fin 4) (l : ℕ) (hl : l ≤ 4) :
    b65q_taylor (b65p_poles p 0) (b65q_res O.residue 0) k l = (b65q_TQ k l).map ι := by
  have hD : ∀ e : Fin 2, ∑ x ∈ b65q_fibreSet e, ((p x - b65p_fixedPole k) ^ (l + 1))⁻¹ =
      ((b65q_DQ e k (l + 1) 0 : ℚ) : ℂ) := fun e ↦ by
    simpa using b65q_DQ_sum O e k 0 (l + 1) (by norm_num) (by omega)
  ext i j
  simp only [b65q_taylor, b65q_TQ, Fintype.sum_sum_type, b65q_poles_zero, Sum.elim_inl,
    Sum.elim_inr, b65q_res_zero_inl, b65q_res_zero_inr, Sum.inl.injEq, reduceCtorEq, if_false,
    Matrix.add_apply, Matrix.sum_apply, Matrix.map_apply]
  rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
  simp only [Fin.sum_univ_two]
  have hF : ∀ e : Fin 2, (∑ x ∈ Finset.univ.filter (fun x ↦ b65q_fibreIndex x = e),
      ((-((p x - b65p_fixedPole k) ^ (l + 1))⁻¹) • (b65q_BQ (b65q_fibreIndex x)).map ι) i j) =
      -((b65q_DQ e k (l + 1) 0 : ℚ) : ℂ) * (b65q_BQ e i j : ℂ) := fun e ↦ by
    rw [← hD e, b65q_fibreSet, ← Finset.sum_neg_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [(Finset.mem_filter.mp hx).2]
    simp
  rw [hF 0, hF 1]
  simp only [apply_ite (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M i j), apply_ite
    (fun M : Matrix (Fin 4) (Fin 4) ℚ ↦ M i j), Matrix.smul_apply, Matrix.map_apply,
    Matrix.zero_apply, b65q_fixedPole_cast, smul_eq_mul, Rat.coe_castHom]
  push_cast [apply_ite (fun q : ℚ ↦ (q : ℂ))]
  ring

theorem b65q_gauge_cast (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (T : ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (PQ PiQ : Matrix (Fin 4) (Fin 4) ℚ) (lamQ : Fin 4 → ℚ) (N : ℕ)
    (hT : ∀ l < N, b65q_taylor t A k l = (T l).map ι) (hP : P = PQ.map ι) (hPi : P⁻¹ = PiQ.map ι)
    (hlam : b65p_exponents k = fun i ↦ ((lamQ i : ℚ) : ℂ)) :
    ∀ n, b65q_gaugeUpTo t A P k N n = (b65q_gaugeQ T PQ PiQ lamQ N n).map ι := by
  induction N with
  | zero =>
    intro n
    simp only [b65q_gaugeUpTo, b65q_gaugeQ]
    split_ifs <;> simp
  | succ N ih =>
    intro n
    simp only [b65q_gaugeUpTo, b65q_gaugeQ]
    by_cases hn : n = N + 1
    · subst hn
      simp only [Function.update_self]
      have hsum : (∑ l ∈ Finset.range (N + 1),
          (P⁻¹ * b65q_taylor t A k l * P) * b65q_gaugeUpTo t A P k N (N - l)) =
          (∑ l ∈ Finset.range (N + 1),
            (PiQ * T l * PQ) * b65q_gaugeQ T PQ PiQ lamQ N (N - l)).map ι := by
        rw [← RingHom.mapMatrix_apply, map_sum]
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        rw [hT l (Finset.mem_range.mp hl), ih (fun l hl' ↦ hT l (by omega)), hPi, hP]
        simp only [RingHom.mapMatrix_apply, Matrix.map_mul]
      ext i j
      simp only [Matrix.of_apply, Matrix.map_apply, hsum, hlam, Rat.coe_castHom]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd (by exact_mod_cast h1) h2
      · exact absurd (by exact_mod_cast h2) h1
      · push_cast; ring
    · rw [Function.update_of_ne hn, Function.update_of_ne hn]
      exact ih (fun l hl ↦ hT l (by omega)) n

theorem b65q_seriesInv_cast (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (HQ : ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (N : ℕ) (hH : ∀ m ≤ N, H m = (HQ m).map ι) :
    ∀ n, b65q_seriesInvUpTo H N n = (b65q_seriesInvQ HQ N n).map ι := by
  induction N with
  | zero =>
    intro n
    simp only [b65q_seriesInvUpTo, b65q_seriesInvQ]
    split_ifs <;> simp
  | succ N ih =>
    intro n
    simp only [b65q_seriesInvUpTo, b65q_seriesInvQ]
    by_cases hn : n = N + 1
    · subst hn
      simp only [Function.update_self]
      rw [← RingHom.mapMatrix_apply, map_neg, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      rw [hH (m + 1) (by have := Finset.mem_range.mp hm; omega), ih (fun m hm' ↦ hH m (by omega))]
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul]
    · rw [Function.update_of_ne hn, Function.update_of_ne hn]
      exact ih (fun m hm ↦ hH m (by omega)) n

theorem b65q_gaugeUpTo_stable (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) {n N : ℕ} (h : n ≤ N) :
    b65q_gaugeUpTo t A P k N n = b65q_gauge t A P k n := by
  induction N with
  | zero => rw [Nat.le_zero.mp h]; rfl
  | succ N ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [b65q_gaugeUpTo, Function.update_of_ne (by omega), ih (by omega)]
    · subst h; rfl

theorem b65q_gaugeQ_stable (T : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (PQ PiQ : Matrix (Fin 4) (Fin 4) ℚ)
    (lamQ : Fin 4 → ℚ) {n N : ℕ} (h : n ≤ N) :
    b65q_gaugeQ T PQ PiQ lamQ N n = b65q_gaugeQ T PQ PiQ lamQ n n := by
  induction N with
  | zero => rw [Nat.le_zero.mp h]
  | succ N ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [b65q_gaugeQ, Function.update_of_ne (by omega), ih (by omega)]
    · subst h; rfl

/-- **Base gauge coefficients.** -/
theorem b65q_gauge_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k : Fin 4) (n : ℕ) (hn : n ≤ 5) :
    b65q_gauge (b65p_poles p 0) (b65q_res O.residue 0) (b65q_eigen0 k) k n = (b65q_HQ k n).map ι := by
  rw [b65q_gauge, b65q_gauge_cast _ _ _ k (b65q_TQ k) (b65q_P0Q k) (b65q_P0invQ k) (b65q_lamQ k) n
    (fun l hl ↦ b65q_taylor_zero O k l (by omega)) (b65q_eigen0_cast k) (b65q_eigen0_inv k)
    (b65q_exponents_cast k)]
  rfl

theorem b65q_rCoeff_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k : Fin 4) (n : ℕ) (hn : n ≤ 5) :
    b65q_rCoeff (b65p_poles p 0) (b65q_res O.residue 0) b65q_eigen0 k n = (b65q_rCQ k n).map ι := by
  rw [b65q_rCoeff, b65q_seriesInv, b65q_rCQ, b65q_seriesInv_cast _ (b65q_HQ k) n
    (fun m hm ↦ b65q_gauge_zero O k m (by omega)), b65q_eigen0_inv, Matrix.map_mul]

theorem b65q_qCoeff_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k : Fin 4) (n : ℕ) (hn : n ≤ 5) :
    b65q_qCoeff (b65p_poles p 0) (b65q_res O.residue 0) b65q_eigen0 k n = (b65q_qCQ k n).map ι := by
  rw [b65q_qCoeff, b65q_qCQ, b65q_gauge_zero O k n hn, b65q_eigen0_cast, ← Matrix.map_mul,
    Matrix.transpose_map]

theorem b65q_poleOrder_le (a : Fin 9) : b65k_poleOrder a ≤ 3 := by fin_cases a <;> decide

theorem b65q_principalEntry_cast (t : Fin 4 ⊕ Fin 12 → ℂ) (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (KQ : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (ht : ∀ k', t (Sum.inl k') = ((b65k_fixed k' : ℚ) : ℂ)) (k : Fin 4)
    (hK : ∀ m ≤ 5, K k m = (KQ k m).map ι) (j : Fin 4) (n : ℤ) (hn : n ≤ 2) (c : Fin 36) :
    b65q_principalEntry t K k j n c = ((b65q_principalEntryQ KQ k j n c : ℚ) : ℂ) := by
  have ho := b65q_poleOrder_le ⟨c.val / 4, by omega⟩
  unfold b65q_principalEntry b65q_principalEntryQ
  split_ifs with h1 h2 h3
  · rw [hK _ (by omega)]; rfl
  · simp
  · push_cast
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hK _ (by omega), ht, ht]
    simp
  · simp

theorem b65q_infinityEntry_cast (i : Fin 4) (c : Fin 36) :
    b65q_infinityEntry i c = ((b65q_infinityEntryQ i c : ℚ) : ℂ) := by
  unfold b65q_infinityEntry b65q_infinityEntryQ
  split_ifs <;> simp

theorem b65q_rRow_le (x : Fin 41) : (b65q_rRow x).2.2 ≤ 2 := by revert x; decide

theorem b65q_qRow_le (x : Fin 53) : (b65q_qRow x).2.2 ≤ 2 := by revert x; decide

theorem b65q_poles_inl (p : Fin 12 → ℂ) (θ : ℂ) (k : Fin 4) :
    b65p_poles p θ (Sum.inl k) = ((b65k_fixed k : ℚ) : ℂ) := by
  simp [b65p_poles, b65q_fixedPole_cast]

/-- **The r-system at the base parameter** is the printed rational system. -/
theorem b65q_rFamily_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    b65q_rFamily p O.residue 0 = b65k_rSystem.map ι := by
  rw [← b65q_rSystemQ_eq, b65q_rFamily, b65q_basis_zero]
  ext r c
  rw [Matrix.map_apply, Rat.coe_castHom]
  unfold b65q_rSystem b65q_rSystemQ
  split_ifs with h
  · exact b65q_principalEntry_cast _ _ _ (b65q_poles_inl p 0) _
      (fun m hm ↦ b65q_rCoeff_zero O _ m hm) _ _ (b65q_rRow_le _) c
  · exact b65q_infinityEntry_cast _ c

theorem b65q_betaEntry_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k j : Fin 4) (n : ℤ)
    (hn : n ≤ 2) (e : Fin 2) (v : Fin 6) :
    b65q_betaEntry (b65p_poles p 0) (b65q_qCoeff (b65p_poles p 0) (b65q_res O.residue 0)
        b65q_eigen0) p (b65q_left O.residue 0) k j n e v =
      ((b65q_betaEntryQ b65q_qCQ k j n e v : ℚ) : ℂ) := by
  unfold b65q_betaEntry b65q_betaEntryQ
  split_ifs with h0
  · rw [← Finset.sum_filter]
    have hfs : Finset.univ.filter (fun x ↦ b65q_fibreIndex x = e) = b65q_fibreSet e := rfl
    rw [hfs]
    have hterm : ∀ x ∈ b65q_fibreSet e, p x ^ v.val * ∑ l ∈ Finset.range (n.toNat + 1),
        (b65q_qCoeff (b65p_poles p 0) (b65q_res O.residue 0) b65q_eigen0 k (n.toNat - l) *ᵥ
          b65q_left O.residue 0 x) j *
          -((b65p_poles p 0 (Sum.inr x) - b65p_poles p 0 (Sum.inl k)) ^ (l + 1))⁻¹ =
        ∑ l ∈ Finset.range (n.toNat + 1),
          (((b65q_qCQ k (n.toNat - l) *ᵥ b65k_left e) j : ℚ) : ℂ) *
            -(p x ^ v.val * ((p x - b65p_fixedPole k) ^ (l + 1))⁻¹) := by
      intro x hx
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' : n.toNat - l ≤ 5 := by omega
      rw [b65q_qCoeff_zero O k _ hl', b65q_left_zero, (Finset.mem_filter.mp hx).2,
        b65q_poles_zero]
      simp only [Sum.elim_inr, Sum.elim_inl]
      have : ((b65q_qCQ k (n.toNat - l)).map ι *ᵥ fun i ↦ ((b65k_left e i : ℚ) : ℂ)) j =
          (((b65q_qCQ k (n.toNat - l) *ᵥ b65k_left e) j : ℚ) : ℂ) := by
        simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [this]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [← Finset.mul_sum, Finset.sum_neg_distrib,
      b65q_DQ_sum O e k v.val (l + 1) (by omega) (by have := Finset.mem_range.mp hl; omega)]
  · simp

theorem b65q_betaInfinity_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (i : Fin 4) (e : Fin 2)
    (v : Fin 6) :
    b65q_betaInfinity p (b65q_left O.residue 0) i e v = ((b65q_betaInfinityQ i e v : ℚ) : ℂ) := by
  unfold b65q_betaInfinity b65q_betaInfinityQ
  rw [← Finset.sum_filter]
  have hfs : Finset.univ.filter (fun x ↦ b65q_fibreIndex x = e) = b65q_fibreSet e := rfl
  rw [hfs, Finset.sum_congr rfl fun x hx ↦ by rw [b65q_left_zero, (Finset.mem_filter.mp hx).2],
    ← Finset.sum_mul, b65q_psum O e v]
  push_cast; ring

/-- **The q-system at the base parameter** is the printed rational system. -/
theorem b65q_qFamily_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    b65q_qFamily p O.residue 0 = b65k_qSystem.map ι := by
  rw [← b65q_qSystemQ_eq, b65q_qFamily]
  ext r c
  rw [Matrix.map_apply, Rat.coe_castHom]
  unfold b65q_qSystem b65q_qSystemQ
  split_ifs with h hc hc
  · rw [b65q_basis_zero]
    exact b65q_principalEntry_cast _ _ _ (b65q_poles_inl p 0) _
      (fun m hm ↦ b65q_qCoeff_zero O _ m hm) _ _ (b65q_qRow_le _) _
  · rw [b65q_basis_zero]
    exact b65q_betaEntry_zero O _ _ _ (b65q_qRow_le _) _ _
  · exact b65q_infinityEntry_cast _ _
  · exact b65q_betaInfinity_zero O _ _ _

end HodgeLean.Foundations.Program
