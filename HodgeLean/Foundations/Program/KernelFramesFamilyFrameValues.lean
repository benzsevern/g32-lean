import HodgeLean.Foundations.Program.KernelFramesFamilyFrames

/-! # B6-5 stage 5d, family part: the frames and their rational vectors at the base parameter

Analyticity of the inverse-block frames where the selected blocks are invertible; at `θ = 0` the
frames are the printed kernel columns, the cast `b65q_castRat` commutes with the fixed-pole
principal parts, and the moving-pole parts of the q-vectors are the root sums of
`b65k_rootSum` (`b65q_rootSum_cast`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

theorem b65q_ibFrame_an {s : Set ℂ} {m n p : ℕ} {S : ℂ → Matrix (Fin m) (Fin n) ℂ}
    (rows : Fin p → Fin m) (piv : Fin p → Fin n) (free : Fin 3 → Fin n) (hS : b65q_MatAn s S)
    (hdet : ∀ θ ∈ s, ((S θ).submatrix rows piv).det ≠ 0) :
    b65q_MatAn s fun θ ↦ b65q_ibFrame (S θ) rows piv free := by
  intro i f
  simp only [b65q_ibFrame]
  refine analyticOnNhd_const.sub (b65q_an_sum _ fun a _ ↦ ?_)
  split_ifs
  · exact (((hS.submatrix rows piv).inv hdet).mul (hS.submatrix rows free)) a f
  · exact analyticOnNhd_const

theorem b65q_inv_map {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℚ) :
    (M.map ι)⁻¹ = M⁻¹.map ι := by
  by_cases h : M.det = 0
  · have h' : (M.map ι).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simpa [isUnit_iff_ne_zero] using h'),
      Matrix.nonsing_inv_apply_not_isUnit _ (by simp [h])]
    ext i j; simp
  · apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h),
      Matrix.map_one _ (map_zero _) (map_one _)]

theorem b65q_rFrame_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    b65q_rFrame p O.residue 0 = b65k_rKernel.map ι := by
  rw [b65q_rFrame_eq, b65q_rFamily_zero]
  ext i f
  simp only [b65q_ibFrame, b65k_rKernel, Matrix.map_apply, Matrix.submatrix_map, b65q_inv_map,
    ← Matrix.map_mul]
  rw [b65k_rBlock]
  simp only [map_sub, map_sum, apply_ite ι, map_one, map_zero]

theorem b65q_qFrame_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    b65q_qFrame p O.residue 0 = b65k_qKernel.map ι := by
  rw [b65q_qFrame_eq, b65q_qFamily_zero]
  ext i f
  simp only [b65q_ibFrame, b65k_qKernel, Matrix.map_apply, Matrix.submatrix_map, b65q_inv_map,
    ← Matrix.map_mul]
  rw [b65k_qBlock]
  simp only [map_sub, map_sum, apply_ite ι, map_one, map_zero]

theorem b65q_castRat_algebraMap (q : ℚ[X]) :
    b65q_castRat (algebraMap ℚ[X] (RatFunc ℚ) q) = algebraMap ℂ[X] (RatFunc ℂ) (q.map ι) := by
  have := RatFunc.map_apply_div (Polynomial.mapRingHom ι)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (Rat.castHom ℂ).injective)) q 1
  simp only [map_one, div_one] at this
  exact this

theorem b65q_castRat_C (q : ℚ) : b65q_castRat (RatFunc.C q) = RatFunc.C (q : ℂ) := by
  rw [← RatFunc.algebraMap_C, b65q_castRat_algebraMap, Polynomial.map_C, RatFunc.algebraMap_C]
  rfl

theorem b65q_castRat_X : b65q_castRat RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, b65q_castRat_algebraMap, Polynomial.map_X, RatFunc.algebraMap_X]

theorem b65q_principal_zero (p : Fin 12 → ℂ) (c : Fin 36 → ℚ) (j : Fin 4) :
    b65q_principal (b65p_poles p 0) (fun i ↦ (c i : ℂ)) j = b65q_castRat (b65k_principal c j) := by
  simp only [b65q_principal, b65k_principal, map_sum, map_div₀, map_pow, map_sub, b65q_castRat_C,
    b65q_castRat_X, b65q_poles_inl]

theorem b65q_fibreC_map (e : Fin 2) :
    (b65k_fibrePoly ((![(5 : ℚ), -7] : Fin 2 → ℚ) e)).map ι = b65q_fibreC e := by
  fin_cases e <;>
    simp [b65k_fibrePoly, b65q_fibreC, b65q_PC, b65q_fibreValue, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_pow] <;> norm_num

theorem b65q_trace_psum (e : Fin 2) (j : Fin 6) :
    Matrix.trace (b65k_companion ((![(5 : ℚ), -7] : Fin 2 → ℚ) e) ^ (j : ℕ)) = b65q_psumQ e j := by
  fin_cases e <;> fin_cases j
  · exact b65k_trace_five_0
  · exact b65k_trace_five_1
  · exact b65k_trace_five_2
  · exact b65k_trace_five_3
  · exact b65k_trace_five_4
  · exact b65k_trace_five_5
  · exact b65k_trace_seven_0
  · exact b65k_trace_seven_1
  · exact b65k_trace_seven_2
  · exact b65k_trace_seven_3
  · exact b65k_trace_seven_4
  · exact b65k_trace_seven_5

theorem b65q_X_sub_C_ne (a : ℂ) : (RatFunc.X : RatFunc ℂ) - RatFunc.C a ≠ 0 := by
  have := (map_ne_zero_iff (algebraMap ℂ[X] (RatFunc ℂ))
    (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 (Polynomial.X_sub_C_ne_zero a)
  simpa using this

theorem b65q_logDeriv_rat {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) :
    algebraMap ℂ[X] (RatFunc ℂ) (b65q_fibreC e).derivative /
        algebraMap ℂ[X] (RatFunc ℂ) (b65q_fibreC e) =
      ∑ x ∈ b65q_fibreSet e, 1 / (RatFunc.X - RatFunc.C (p x)) := by
  rw [← b65q_fibre_prod O e, derivative_prod_finset, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [derivative_X_sub_C, mul_one, ← Finset.mul_prod_erase _ _ hx]
  simp only [map_mul, map_prod, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have h1 := b65q_X_sub_C_ne (p x)
  have h2 : ∏ y ∈ (b65q_fibreSet e).erase x, (RatFunc.X - RatFunc.C (p y)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun y _ ↦ b65q_X_sub_C_ne _
  field_simp

theorem b65q_rootSum_cast {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) (k : ℕ) (hk : k ≤ 5) :
    b65q_castRat (b65k_rootSum ((![(5 : ℚ), -7] : Fin 2 → ℚ) e) k) =
      ∑ x ∈ b65q_fibreSet e, RatFunc.C (p x ^ k) / (RatFunc.X - RatFunc.C (p x)) := by
  unfold b65k_rootSum
  simp only [map_sub, map_mul, map_pow, map_div₀, map_sum, b65q_castRat_X, b65q_castRat_C,
    b65q_castRat_algebraMap, ← Polynomial.derivative_map, b65q_fibreC_map, b65q_logDeriv_rat O e]
  have htr : ∀ j ∈ Finset.range k, ((Matrix.trace (b65k_companion
      ((![(5 : ℚ), -7] : Fin 2 → ℚ) e) ^ j) : ℚ) : ℂ) = ∑ x ∈ b65q_fibreSet e, p x ^ j := by
    intro j hj
    have hj' : j < 6 := by have := Finset.mem_range.mp hj; omega
    rw [show j = ((⟨j, hj'⟩ : Fin 6) : ℕ) from rfl, b65q_trace_psum, b65q_psum O e]
  have hs : ∑ j ∈ Finset.range k, (RatFunc.X : RatFunc ℂ) ^ (k - 1 - j) *
      RatFunc.C (((Matrix.trace (b65k_companion ((![(5 : ℚ), -7] : Fin 2 → ℚ) e) ^ j)) : ℚ) : ℂ) =
      ∑ x ∈ b65q_fibreSet e, ∑ j ∈ Finset.range k,
        (RatFunc.X : RatFunc ℂ) ^ (k - 1 - j) * RatFunc.C (p x) ^ j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [htr j hj, map_sum, Finset.mul_sum]
    simp [map_pow]
  rw [hs, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have h1 := b65q_X_sub_C_ne (p x)
  have hg := geom_sum₂_mul (RatFunc.C (p x)) (RatFunc.X : RatFunc ℂ) k
  have hS : ∑ j ∈ Finset.range k, (RatFunc.X : RatFunc ℂ) ^ (k - 1 - j) * RatFunc.C (p x) ^ j =
      ∑ j ∈ Finset.range k, RatFunc.C (p x) ^ j * (RatFunc.X : RatFunc ℂ) ^ (k - 1 - j) :=
    Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [eq_div_iff h1, sub_mul, mul_assoc, one_div, inv_mul_cancel₀ h1, mul_one, hS]
  linear_combination hg

theorem b65q_qVector_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (d : Fin 48 → ℚ) (j : Fin 4) :
    b65q_qVector (b65p_poles p 0) p (b65q_left O.residue 0) (fun i ↦ (d i : ℂ)) j =
      b65q_castRat (b65k_principal (fun i ↦ d ⟨i.val, by omega⟩) j +
        ∑ e : Fin 2, ∑ k : Fin 6, RatFunc.C (b65k_left e j * d ⟨36 + 6 * e.val + k.val, by omega⟩) *
          b65k_rootSum ((![(5 : ℚ), -7] : Fin 2 → ℚ) e) k.val) := by
  unfold b65q_qVector
  rw [map_add, ← b65q_principal_zero p]
  congr 1
  simp only [map_sum, map_mul, b65q_castRat_C]
  rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hR : ∀ k : Fin 6, b65q_castRat (b65k_rootSum ((![(5 : ℚ), -7] : Fin 2 → ℚ) e) k.val) =
      ∑ x ∈ b65q_fibreSet e, RatFunc.C (p x ^ k.val) / (RatFunc.X - RatFunc.C (p x)) :=
    fun k ↦ b65q_rootSum_cast O e k.val (by omega)
  simp only [hR]
  have hfs : Finset.univ.filter (fun x ↦ b65q_fibreIndex x = e) = b65q_fibreSet e := rfl
  rw [hfs]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hxe : b65q_fibreIndex x = e := (Finset.mem_filter.mp hx).2
  subst hxe
  rw [b65q_left_zero, b65q_poles_zero, Sum.elim_inr]
  simp only [Finset.sum_mul, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

theorem b65q_qVector_frame_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (b : Fin 3) (j : Fin 4) :
    b65q_qVector (b65p_poles p 0) p (b65q_left O.residue 0)
        (fun i ↦ b65q_qFrame p O.residue 0 i b) j = b65q_castRat (b65k_qBase b j) := by
  rw [b65q_qFrame_zero]
  exact b65q_qVector_zero O (fun i ↦ b65k_qKernel i b) j

theorem b65q_principal_frame_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (a : Fin 3) (j : Fin 4) :
    b65q_principal (b65p_poles p 0) (fun i ↦ b65q_rFrame p O.residue 0 i a) j =
      b65q_castRat (b65k_rBase a j) := by
  rw [b65q_rFrame_zero]
  exact b65q_principal_zero p (fun i ↦ b65k_rKernel i a) j

end HodgeLean.Foundations.Program
