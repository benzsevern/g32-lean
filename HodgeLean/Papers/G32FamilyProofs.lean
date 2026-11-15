import HodgeLean.Papers.G32FamilyDefs
import HodgeLean.Papers.PapersG32Certificates

/-! # G32 Theorem A, stage 2: the Hurwitz family and its Prym factor, open proof obligations -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

open Polynomial

private theorem g32h_root_ne_one {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : w - 1 ≠ 0 := by
  intro h
  have : w = 1 := sub_eq_zero.mp h
  rw [this] at hw
  norm_num at hw

private theorem g32h_r1_rank {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : (g32R1 w - 1).rank = 1 := by
  have hn := g32h_root_ne_one w hw
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  let u : Fin 4 → K := fun i => (g32R1 w - 1) i 0
  let v : Fin 4 → K := fun j => 3 * (g32R1 w - 1) 0 j / (w - 1)
  have heq : g32R1 w - 1 = Matrix.vecMulVec u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, v, g32R1, Matrix.vecMulVec_apply] <;>
      field_simp [hn] <;> ring_nf <;> simp only [hp] <;> ring
  let f : Fin 1 → Fin 4 := fun _ => 0
  have hdet : ((g32R1 w - 1).submatrix f f).det ≠ 0 := by
    have hz : (w + 2) / 3 - 1 ≠ 0 := by
      intro h
      apply hn
      field_simp at h
      linear_combination h
    simpa [f, g32R1] using hz
  have hsub := Matrix.rank_submatrix_le (g32R1 w - 1) f f
  rw [Matrix.rank_of_det_ne_zero hdet] at hsub
  rw [heq]
  apply le_antisymm (Matrix.rank_vecMulVec_le u v)
  rw [heq] at hsub
  simpa using hsub

private theorem g32h_r2_rank {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : (g32R2 w - 1).rank = 1 := by
  have hn : w + 2 ≠ 0 := by
    intro h
    have : w = -2 := by linear_combination h
    rw [this] at hw
    norm_num at hw
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  let u : Fin 4 → K := fun i => (g32R2 w - 1) i 0
  let v : Fin 4 → K := fun j => -3 * (g32R2 w - 1) 0 j / (w + 2)
  have heq : g32R2 w - 1 = Matrix.vecMulVec u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, v, g32R2, Matrix.vecMulVec_apply] <;>
      field_simp [hn] <;> ring_nf <;> simp only [hp] <;> ring
  let f : Fin 1 → Fin 4 := fun _ => 0
  have hdet : ((g32R2 w - 1).submatrix f f).det ≠ 0 := by
    have hz : (1 - w) / 3 - 1 ≠ 0 := by
      intro h
      apply hn
      field_simp at h
      linear_combination -h
    simpa [f, g32R2] using hz
  have hsub := Matrix.rank_submatrix_le (g32R2 w - 1) f f
  rw [Matrix.rank_of_det_ne_zero hdet] at hsub
  rw [heq]
  apply le_antisymm (Matrix.rank_vecMulVec_le u v)
  rw [heq] at hsub
  simpa using hsub

private theorem g32h_x_sq_rank {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : (g32X w * g32X w - 1).rank = 2 := by
  classical
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  let B : Matrix (Fin 4) (Fin 4) K :=
    !![0, 0, 0, 0; 0, -1, w, 0; 0, -w - 1, -1, 0; 0, 0, 0, -2]
  have hB : g32X w * g32X w - 1 = B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, g32X, Matrix.mul_apply, Fin.sum_univ_four] <;>
      field_simp <;> ring_nf <;> simp only [hp] <;> ring
  rw [hB]
  apply le_antisymm
  · rw [Matrix.rank_eq_finrank_span_cols]
    let s : Finset (Fin 4 → K) := {B.col 1, B.col 3}
    calc
      Module.finrank K (Submodule.span K (Set.range B.col)) ≤
          Module.finrank K (Submodule.span K (s : Set (Fin 4 → K))) := by
        apply Submodule.finrank_mono
        apply Submodule.span_le.2
        rintro x ⟨j, rfl⟩
        by_cases h0 : j = 0
        · subst j
          have hz : B.col 0 = 0 := by
            funext i
            fin_cases i <;> simp [B, Matrix.col]
          rw [hz]
          exact Submodule.zero_mem _
        by_cases h1 : j = 1
        · subst j
          exact Submodule.subset_span (by simp [s])
        by_cases h2 : j = 2
        · subst j
          have hc : B.col 2 = (-w) • B.col 1 := by
            funext i
            fin_cases i <;> simp [B, Matrix.col] <;> try ring
            linear_combination hw
          rw [hc]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [s]))
        · have h3 : j = 3 := Fin.eq_of_val_eq (by omega)
          subst j
          exact Submodule.subset_span (by simp [s])
      _ ≤ s.card := finrank_span_finset_le_card s
      _ ≤ 2 := by simpa [s] using Finset.card_le_two (a := B.col 1) (b := B.col 3)
  · let f : Fin 2 → Fin 4 := ![1, 3]
    have hdet : (B.submatrix f f).det ≠ 0 := by
      simp [B, f, Matrix.det_fin_two, Matrix.submatrix]
    have hsub := Matrix.rank_submatrix_le B f f
    rw [Matrix.rank_of_det_ne_zero hdet] at hsub
    simpa using hsub

theorem g32h_multCW_classRep_aux {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : g32h_multCW (g32h_classRep w) = 6 := by
  simp only [g32h_multCW, Fin.sum_univ_succ]
  norm_num [g32h_classRep, g32h_r1_rank w hw, g32h_r2_rank w hw,
    g32h_x_sq_rank w hw]

theorem g32h_multCW_without_involution_aux {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) :
    g32h_multCW (fun j : Fin 12 => g32h_classRep w j.castSucc) = 4 := by
  simp only [g32h_multCW, Fin.sum_univ_succ]
  norm_num [g32h_classRep, g32h_r1_rank w hw, g32h_r2_rank w hw]

private theorem g32h_r1_cube {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    g32R1 w ^ 3 = 1 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R1, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow w hw

private theorem g32h_r2_cube {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    g32R2 w ^ 3 = 1 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R2, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow w hw

private theorem g32h_classRep_orders {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    orderOf (g32R1 w) = 3 ∧ orderOf (g32R2 w) = 3 ∧ orderOf (g32X w * g32X w) = 2 := by
  have hn : w - 1 ≠ 0 := by
    intro h
    have : w = 1 := sub_eq_zero.mp h
    rw [this] at hw
    norm_num at hw
  refine ⟨orderOf_eq_prime (g32h_r1_cube w hw) ?_, orderOf_eq_prime (g32h_r2_cube w hw) ?_,
    orderOf_eq_prime ?_ ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [g32R1] at this
    apply hn
    field_simp at this
    linear_combination this
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [g32R2] at this
    have h2 : w = -2 := by linear_combination -3 * this
    rw [h2] at hw
    norm_num at hw
  · rw [sq, show g32X w * g32X w * (g32X w * g32X w) = g32X w ^ 4 by noncomm_ring]
    exact (papers_g32_x_sq w hw).2
  · intro h
    have := congrFun (congrFun h 3) 3
    rw [papers3b_x_sq w hw] at this
    norm_num at this

private theorem g32h_roots_four (a b c d : ℂ) :
    ((X - C a) * (X - C b) * (X - C c) * (X - C d)).roots = {a, b, c, d} := by
  have : (X - C a) * (X - C b) * (X - C c) * (X - C d) =
      (Multiset.map (fun x => X - C x) ({a, b, c, d} : Multiset ℂ)).prod := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.map_singleton, Multiset.prod_singleton]
    ring
  rw [this, Polynomial.roots_multiset_prod_X_sub_C]

private theorem g32h_r1_inv {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    (g32R1 w)⁻¹ = (g32R1 (w ^ 2)).transpose := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R1, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow w hw

private theorem g32h_r2_inv {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    (g32R2 w)⁻¹ = (g32R2 (w ^ 2)).transpose := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R2, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow w hw

private theorem g32h_sq_root {K : Type*} [Field K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    (w ^ 2) ^ 2 + w ^ 2 + 1 = 0 := by
  linear_combination (w ^ 2 - w + 1) * hw

private theorem g32h_angle_neg_one : g32h_angle (-1) = 1 / 2 := by
  have hpi := Real.pi_pos
  rw [g32h_angle, Complex.arg_neg_one, (toIcoMod_eq_self _).2]
  · field_simp
  · constructor <;> linarith

private theorem g32h_sqrt_three_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private theorem g32h_angle_omega :
    g32h_angle ((-1 / 2 : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) = 1 / 3 := by
  have hpi := Real.pi_pos
  have h : ((-1 / 2 : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.cos ((2 * Real.pi / 3 : ℝ) : ℂ) + Complex.sin ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast
    ring
  rw [g32h_angle, h, Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩,
    (toIcoMod_eq_self _).2]
  · field_simp
  · constructor <;> linarith

private theorem g32h_angle_omega_sq :
    g32h_angle ((-1 / 2 : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) = 2 / 3 := by
  have hpi := Real.pi_pos
  have h : ((-1 / 2 : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.cos ((-(2 * Real.pi / 3) : ℝ) : ℂ) +
        Complex.sin ((-(2 * Real.pi / 3) : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast
    ring
  rw [g32h_angle, h, Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩,
    ← toIcoMod_add_right, (toIcoMod_eq_self _).2]
  · field_simp
    ring
  · constructor <;> linarith

private theorem g32h_angle_add_angle_sq (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32h_angle w + g32h_angle (w ^ 2) = 1 := by
  set a : ℂ := (-1 / 2 : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I
  set b : ℂ := (-1 / 2 : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I
  have h3 := g32h_sqrt_three_sq
  have hab : (w - a) * (w - b) = 0 := by
    simp only [a, b]
    push_cast
    linear_combination hw - (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq + (1 / 4 : ℂ) * h3
  rcases mul_eq_zero.mp hab with h | h
  · have hw' : w = a := sub_eq_zero.mp h
    have h2 : w ^ 2 = b := by
      rw [hw']
      simp only [a, b]
      push_cast
      linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4 : ℂ) * h3
    rw [h2, hw', g32h_angle_omega, g32h_angle_omega_sq]
    norm_num
  · have hw' : w = b := sub_eq_zero.mp h
    have h2 : w ^ 2 = a := by
      rw [hw']
      simp only [a, b]
      push_cast
      linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4 : ℂ) * h3
    rw [h2, hw', g32h_angle_omega, g32h_angle_omega_sq]
    norm_num

theorem g32h_holoCW_classRep_aux (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32h_holoCW (g32h_classRep w) = 3 := by
  have h1 : g32h_age (g32R1 w)⁻¹ = g32h_angle (w ^ 2) := by
    rw [g32h_age, g32h_r1_inv w hw, Matrix.charpoly_transpose,
      papers_g32_r1_charpoly (w ^ 2) (g32h_sq_root w hw),
      show (X - C (w ^ 2)) * (X - 1) ^ 3 = (X - C (w ^ 2)) * (X - C 1) * (X - C 1) * (X - C 1) by
        simp only [map_one]; ring, g32h_roots_four]
    simp [g32h_angle]
  have h2 : g32h_age (g32R2 w)⁻¹ = g32h_angle w := by
    rw [g32h_age, g32h_r2_inv w hw, Matrix.charpoly_transpose,
      papers_g32_r2_charpoly (w ^ 2) (g32h_sq_root w hw),
      show (w ^ 2) ^ 2 = w by linear_combination (w ^ 2 - w) * hw,
      show (X - C w) * (X - 1) ^ 3 = (X - C w) * (X - C 1) * (X - C 1) * (X - C 1) by
        simp only [map_one]; ring, g32h_roots_four]
    simp [g32h_angle]
  have h3 : g32h_age (g32X w * g32X w)⁻¹ = 1 := by
    have hx := papers_g32_x_sq w hw
    have hinv : (g32X w * g32X w)⁻¹ = g32X w * g32X w := by
      apply Matrix.inv_eq_right_inv
      rw [show g32X w * g32X w * (g32X w * g32X w) = g32X w ^ 4 by noncomm_ring, hx.2]
    rw [g32h_age, hinv, hx.1,
      show ((X - 1) ^ 2 * (X + 1) ^ 2 : ℂ[X]) =
        (X - C 1) * (X - C 1) * (X - C (-1)) * (X - C (-1)) by
        simp only [map_one, map_neg]; ring, g32h_roots_four]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, g32h_angle_neg_one]
    simp [g32h_angle]
    norm_num
  have hs := g32h_angle_add_angle_sq w hw
  simp only [g32h_holoCW, Fin.sum_univ_succ]
  norm_num [g32h_classRep, h1, h2, h3]
  linear_combination 6 * hs

theorem g32h_riemannHurwitz_aux {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) :
    (155520 : ℚ) * (-2 + ∑ j, (1 - 1 / (orderOf (g32h_classRep w j) : ℚ))) =
      2 * 505441 - 2 := by
  obtain ⟨h1, h2, h3⟩ := g32h_classRep_orders w hw
  simp only [Fin.sum_univ_succ]
  norm_num [g32h_classRep, h1, h2, h3]

private theorem g32h_centralizerDim_of_diagonal (M P Q : Matrix (Fin 4) (Fin 4) ℂ) (d : Fin 4 → ℂ) (c : Fin 4 → Fin 4)
    (hPQ : P * Q = 1) (hMP : M * P = P * Matrix.diagonal d)
    (hc : ∀ i j, d i = d j ↔ c i = c j) :
    g32h_centralizerDim M =
      (Finset.univ.filter fun p : Fin 4 × Fin 4 => c p.1 = c p.2).card := by
  classical
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
  have hM : M = P * Matrix.diagonal d * Q := by
    rw [← hMP, mul_assoc, hPQ, mul_one]
  let D := Matrix.diagonal d
  let T := {p : Fin 4 × Fin 4 // c p.1 = c p.2}
  let L := LinearMap.mulRight ℂ M - LinearMap.mulLeft ℂ M
  have hL : ∀ A, A ∈ LinearMap.ker L ↔ A * M = M * A := by
    intro A
    simp [L, sub_eq_zero]
  -- commuting with `D` forces zeros off the blocks
  have hD : ∀ B : Matrix (Fin 4) (Fin 4) ℂ, B * D = D * B → ∀ i j, c i ≠ c j → B i j = 0 := by
    intro B hB i j hij
    have := congrFun (congrFun hB i) j
    simp only [D, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have hne : d j - d i ≠ 0 := fun h => hij ((hc i j).1 (sub_eq_zero.mp h).symm)
    have : B i j * (d j - d i) = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_right hne
  let mk : (T → ℂ) → Matrix (Fin 4) (Fin 4) ℂ := fun f => Matrix.of fun i j =>
    if h : c i = c j then f ⟨(i, j), h⟩ else 0
  have hmk : ∀ f, mk f * D = D * mk f := by
    intro f
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [mk, Matrix.of_apply]
    split_ifs with h
    · rw [(hc i j).2 h]; ring
    · simp
  have hconj : ∀ A, A * M = M * A → Q * A * P * D = D * (Q * A * P) := by
    intro A hA
    calc Q * A * P * D = Q * (A * M) * P := by
          rw [hM]; simp only [D, Matrix.mul_assoc, hQP, Matrix.mul_one]
      _ = Q * (M * A) * P := by rw [hA]
      _ = D * (Q * A * P) := by
          rw [hM]; simp only [D, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hmem : ∀ f, P * mk f * Q ∈ LinearMap.ker L := by
    intro f
    rw [hL, hM]
    calc P * mk f * Q * (P * D * Q) = P * (mk f * D) * Q := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
      _ = P * (D * mk f) * Q := by rw [hmk]
      _ = P * D * Q * (P * mk f * Q) := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  let e : LinearMap.ker L ≃ₗ[ℂ] (T → ℂ) :=
    { toFun := fun A p => (Q * A.1 * P) p.1.1 p.1.2
      map_add' := fun A B => by
        funext p
        show (Q * (A.1 + B.1) * P) p.1.1 p.1.2 = (Q * A.1 * P) p.1.1 p.1.2 + (Q * B.1 * P) p.1.1 p.1.2
        rw [Matrix.mul_add, Matrix.add_mul]
        rfl
      map_smul' := fun r A => by
        funext p
        show (Q * (r • A.1) * P) p.1.1 p.1.2 = r * (Q * A.1 * P) p.1.1 p.1.2
        rw [Matrix.mul_smul, Matrix.smul_mul]
        rfl
      invFun := fun f => ⟨P * mk f * Q, hmem f⟩
      left_inv := fun A => by
        have hz := hD _ (hconj A.1 ((hL A.1).1 A.2))
        have h1 : mk (fun p : T => (Q * A.1 * P) p.1.1 p.1.2) = Q * A.1 * P := by
          ext i j
          simp only [mk, Matrix.of_apply]
          split_ifs with h
          · rfl
          · exact (hz i j h).symm
        apply Subtype.ext
        change P * mk (fun p : T => (Q * A.1 * P) p.1.1 p.1.2) * Q = A.1
        rw [h1, show P * (Q * A.1 * P) * Q = (P * Q) * A.1 * (P * Q) by
          simp only [Matrix.mul_assoc], hPQ, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun f => by
        funext p
        show (Q * (P * mk f * Q) * P) p.1.1 p.1.2 = f p
        rw [show Q * (P * mk f * Q) * P = (Q * P) * mk f * (Q * P) by
          simp only [Matrix.mul_assoc], hQP, Matrix.one_mul, Matrix.mul_one]
        show (if h : c p.1.1 = c p.1.2 then f ⟨(p.1.1, p.1.2), h⟩ else 0) = f p
        split_ifs with h
        · rfl
        · exact absurd p.2 h }
  rw [g32h_centralizerDim, e.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype]

/-- Reduce a polynomial identity in `ω` and `i` modulo `ω² + ω + 1` and `i² + 1`. -/
macro "g32h_ring " h:term : tactic =>
  `(tactic| (ring_nf; all_goals (try simp only [($h).1, ($h).2.1, ($h).2.2.1, ($h).2.2.2.1, ($h).2.2.2.2, Complex.I_sq, Complex.I_pow_four]); all_goals ring_nf; all_goals (try simp only [($h).1, ($h).2.1, ($h).2.2.1, ($h).2.2.2.1, ($h).2.2.2.2, Complex.I_sq, Complex.I_pow_four]); all_goals ring_nf))

private theorem g32h_r1_centralizerDim (w : ℂ) (hw : w ^ 2 + w + 1 = 0) : g32h_centralizerDim (g32R1 w) = 10 := by
  have h1 : w ≠ 1 := by rintro rfl; norm_num at hw
  rw [g32h_centralizerDim_of_diagonal (g32R1 w) (P := !![w, w, 0, -w; -1, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1])
    (Q := !![(-1/3) + (-1/3) * w, (-1/3), 0, (1/3); (-1/3) + (-1/3) * w, (2/3), 0, (1/3);
      0, 0, 1, 0; (1/3) + (1/3) * w, (1/3), 0, (2/3)])
    (d := ![w, 1, 1, 1]) (c := ![0, 1, 1, 1])]
  · decide
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
      g32h_ring papers3b_omega_pow w hw
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g32R1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;>
      g32h_ring papers3b_omega_pow w hw
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [h1, h1.symm]

private theorem g32h_r2_centralizerDim (w : ℂ) (hw : w ^ 2 + w + 1 = 0) : g32h_centralizerDim (g32R2 w) = 10 := by
  have h1 : w ^ 2 ≠ 1 := by
    intro h
    have : w = -2 := by linear_combination hw - h
    rw [this] at hw; norm_num at hw
  rw [g32h_centralizerDim_of_diagonal (g32R2 w) (P := !![-1 - w, 1 + w, 1 + w, 0; 1, 1, 0, 0; 1, 0, 1, 0; 0, 0, 0, 1])
    (Q := !![(1/3) * w, (1/3), (1/3), 0; (-1/3) * w, (2/3), (-1/3), 0;
      (-1/3) * w, (-1/3), (2/3), 0; 0, 0, 0, 1])
    (d := ![w ^ 2, 1, 1, 1]) (c := ![0, 1, 1, 1])]
  · decide
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
      g32h_ring papers3b_omega_pow w hw
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g32R2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;>
      g32h_ring papers3b_omega_pow w hw
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [h1, h1.symm]

private theorem g32h_y_centralizerDim (w : ℂ) (hw : w ^ 2 + w + 1 = 0) : g32h_centralizerDim (g32Y w) = 8 := by
  have h1 : w ≠ w ^ 2 := by
    intro h
    have h0 : w * (w - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rw [h0] at hw; norm_num at hw
    · rw [sub_eq_zero.mp h0] at hw; norm_num at hw
  rw [g32h_centralizerDim_of_diagonal (g32Y w) (P := !![w, w, (-1/2) * w, (-1/2) * w; -1 - w, 1 + w, (1/2) + (1/2) * w,
      (-1/2) + (-1/2) * w; 1, 0, 1, 0; 0, 1, 0, 1])
    (Q := !![(-1/3) + (-1/3) * w, (1/3) * w, (1/3), 0; (-1/3) + (-1/3) * w, (-1/3) * w, 0, (1/3);
      (1/3) + (1/3) * w, (-1/3) * w, (2/3), 0; (1/3) + (1/3) * w, (1/3) * w, 0, (2/3)])
    (d := ![w, w, w ^ 2, w ^ 2]) (c := ![0, 0, 1, 1])]
  · decide
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
      g32h_ring papers3b_omega_pow w hw
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g32Y, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;>
      g32h_ring papers3b_omega_pow w hw
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [h1, h1.symm]

private theorem g32h_x_centralizerDim (w : ℂ) (hw : w ^ 2 + w + 1 = 0) : g32h_centralizerDim (g32X w) = 6 := by
  have h1 : Complex.I ≠ -1 := by
    intro h; have := congrArg Complex.im h; simp at this
  have h2 : Complex.I ≠ -Complex.I := by
    intro h; have := congrArg Complex.im h; norm_num at this
  have h3 : (-1 : ℂ) ≠ -Complex.I := by
    intro h; have := congrArg Complex.im h; simp at this
  rw [g32h_centralizerDim_of_diagonal (g32X w) (P := !![0, 1, 0, 0;
      (1/2) + (1/2) * w + (-1/2) * Complex.I + (1/2) * Complex.I * w, 0, w,
        (1/2) + (1/2) * w + (1/2) * Complex.I + (-1/2) * Complex.I * w;
      (1/2) * w + (-1) * Complex.I + (-1/2) * Complex.I * w, 0, 1,
        (1/2) * w + Complex.I + (1/2) * Complex.I * w;
      1, 0, 0, 1])
    (Q := !![0, (1/3) * Complex.I + (1/6) * Complex.I * w,
        (1/6) * Complex.I + (-1/6) * Complex.I * w,
        (1/2) + (-1/6) * Complex.I + (-1/3) * Complex.I * w;
      1, 0, 0, 0;
      0, (-1/2) + (-1/2) * w, (1/2), 0;
      0, (-1/3) * Complex.I + (-1/6) * Complex.I * w, (-1/6) * Complex.I + (1/6) * Complex.I * w,
        (1/2) + (1/6) * Complex.I + (1/3) * Complex.I * w])
    (d := ![Complex.I, -1, -1, -Complex.I]) (c := ![0, 1, 1, 2])]
  · decide
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
      g32h_ring papers3b_omega_pow w hw
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g32X, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;>
      g32h_ring papers3b_omega_pow w hw
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [h1, h1.symm, h2, h2.symm, h3, h3.symm]

theorem g32h_rigidity_count_aux (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    ((16 : ℤ) - g32h_centralizerDim (g32R1 w)) + (16 - g32h_centralizerDim (g32R2 w)) +
      (16 - g32h_centralizerDim (g32X w)) + (16 - g32h_centralizerDim (g32Y w)) =
      2 * (4 ^ 2 - 1) := by
  rw [g32h_r1_centralizerDim w hw, g32h_r2_centralizerDim w hw, g32h_x_centralizerDim w hw,
    g32h_y_centralizerDim w hw]
  norm_num

theorem g32h_nielsen_conj_aux (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ) (hg : g32h_Nielsen g)
    (h h' : Matrix (Fin 4) (Fin 4) ℂ) (hh : h ∈ g32h_G) (hh' : h' ∈ g32h_G) (hinv : h * h' = 1) :
    g32h_Nielsen (fun j => h * g j * h') := by
  obtain ⟨⟨σ, hσ⟩, hprod, hgen⟩ := hg
  have hinv' : h' * h = 1 := mul_eq_one_comm.mp hinv
  let f : Matrix (Fin 4) (Fin 4) ℂ →* Matrix (Fin 4) (Fin 4) ℂ :=
    { toFun := fun x => h * x * h'
      map_one' := by simp [hinv]
      map_mul' := fun x y => by
        rw [show h * x * h' * (h * y * h') = h * x * (h' * h) * y * h' by noncomm_ring, hinv',
          mul_one, mul_assoc h x y] }
  have hf : ∀ x, f x = h * x * h' := fun x => rfl
  refine ⟨⟨σ, fun j => ?_⟩, ?_, ?_⟩
  · obtain ⟨k, hk, k', hk', hkk, hj⟩ := hσ j
    refine ⟨h * k, mul_mem hh hk, k' * h', mul_mem hk' hh', ?_, ?_⟩
    · rw [show h * k * (k' * h') = h * (k * k') * h' by noncomm_ring, hkk, mul_one, hinv]
    · show h * g j * h' = _
      rw [hj]; noncomm_ring
  · have : (List.ofFn fun j => h * g j * h') = (List.ofFn g).map f := by
      rw [List.map_ofFn]; rfl
    rw [this, ← map_list_prod, hprod, map_one]
  · have : Set.range (fun j => h * g j * h') = f '' Set.range g := by
      rw [← Set.range_comp]; rfl
    rw [this, ← MonoidHom.map_mclosure, hgen]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hf]
      exact mul_mem (mul_mem hh hx) hh'
    · intro x hx
      refine ⟨h' * x * h, mul_mem (mul_mem hh' hx) hh, ?_⟩
      show h * (h' * x * h) * h' = x
      rw [show h * (h' * x * h) * h' = (h * h') * x * (h * h') by noncomm_ring, hinv]
      simp

theorem g32h_multCW_of_nielsen_aux (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : g32h_Nielsen g) : g32h_multCW g = 6 := by
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := hg
  have hr : ∀ j, (g j - 1).rank = (g32h_classRep g32h_omega (σ j) - 1).rank := by
    intro j
    obtain ⟨k, -, k', -, hkk, hj⟩ := hσ j
    have hdet : k.det * k'.det = 1 := by rw [← Matrix.det_mul, hkk, Matrix.det_one]
    rw [hj, show k * g32h_classRep g32h_omega (σ j) * k' - 1 =
        k * (g32h_classRep g32h_omega (σ j) - 1) * k' by
      rw [mul_sub, sub_mul, mul_one, hkk]]
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_exists_inv.mpr ⟨k.det, by rw [mul_comm]; exact hdet⟩),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_iff_exists_inv.mpr ⟨_, hdet⟩)]
  rw [← g32h_multCW_classRep_aux g32h_omega g32h_omega_sq_add]
  unfold g32h_multCW
  simp only [hr]
  rw [Equiv.sum_comp σ (fun j => ((g32h_classRep g32h_omega j - 1).rank : ℤ))]

theorem g32h_holoCW_of_nielsen_aux (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : g32h_Nielsen g) : g32h_holoCW g = 3 := by
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := hg
  have ha : ∀ j, g32h_age (g j)⁻¹ = g32h_age (g32h_classRep g32h_omega (σ j))⁻¹ := by
    intro j
    obtain ⟨k, -, k', -, hkk, hj⟩ := hσ j
    have hkk' : k' * k = 1 := mul_eq_one_comm.mp hkk
    let u : (Matrix (Fin 4) (Fin 4) ℂ)ˣ := ⟨k, k', hkk, hkk'⟩
    have hinv : (g j)⁻¹ = (u : Matrix (Fin 4) (Fin 4) ℂ) *
        (g32h_classRep g32h_omega (σ j))⁻¹ * (u : Matrix (Fin 4) (Fin 4) ℂ)⁻¹ := by
      show (g j)⁻¹ = k * (g32h_classRep g32h_omega (σ j))⁻¹ * k⁻¹
      rw [hj, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hkk, mul_assoc]
    rw [g32h_age, g32h_age, hinv, Matrix.charpoly_units_conj]
  rw [← g32h_holoCW_classRep_aux g32h_omega g32h_omega_sq_add]
  unfold g32h_holoCW
  simp only [ha]
  rw [Equiv.sum_comp σ (fun j => g32h_age (g32h_classRep g32h_omega j)⁻¹)]

theorem g32h_fiber_polarized_aux (P : g32h_PrymFamily) :
    ∀ s, g32t_PolarizedWeil (P.fiber s) := by
  intro s
  have hm := g32h_multCW_of_nielsen_aux (P.tuple s) (P.tuple_nielsen s)
  have hdim : dim (P.fiber s).X.left = 6 := by
    have h := P.dim_eq s
    rw [hm] at h
    exact_mod_cast h
  have hp := g32h_holoCW_of_nielsen_aux (P.tuple s) (P.tuple_nielsen s)
  have hh : g32h_h10 (P.fiber s) = 3 ∧ g32h_h01 (P.fiber s) = 3 := by
    rcases P.hodge s with h | h
    · rw [hm, hp] at h
      norm_num at h ⊢
      constructor
      · exact_mod_cast h.1
      · exact_mod_cast h.2
    · rw [hm, hp] at h
      norm_num at h ⊢
      constructor
      · exact_mod_cast h.2
      · exact_mod_cast h.1
  have hweil :
      letI := (torusCohomology_cupProductOf (P.fiber s).X).finite
      (P.fiber s).W.IsWeilType :=
    (isWeilType_iff_finrank_eq _ _ _ _ (P.fiber s).W).2 (hh.1.trans hh.2.symm)
  exact ⟨hdim, hweil, P.nondegenerate s, P.rosati s, P.positive s⟩

theorem g32h_h10_eq_three_aux (P : g32h_PrymFamily) (s : P.S) :
    g32h_h10 (P.fiber s) = 3 ∧ g32h_h01 (P.fiber s) = 3 := by
  have hm := g32h_multCW_of_nielsen_aux (P.tuple s) (P.tuple_nielsen s)
  have hp := g32h_holoCW_of_nielsen_aux (P.tuple s) (P.tuple_nielsen s)
  rcases P.hodge s with h | h
  · rw [hm, hp] at h
    norm_num at h ⊢
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  · rw [hm, hp] at h
    norm_num at h ⊢
    constructor
    · exact_mod_cast h.2
    · exact_mod_cast h.1

theorem g32h_exists_nielsen_aux (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (R : g32h_RemainingFields F P) : ∃ g, g32h_Nielsen g := by
  obtain ⟨U, _, ⟨m, hm⟩, hU⟩ := R.dominant
  obtain ⟨s, _⟩ := hU m hm
  exact ⟨P.tuple s, P.tuple_nielsen s⟩

end HodgeLean.Papers
