import HodgeLean.Papers.PapersG32CertificatesDefs
import HodgeLean.Papers.PapersArithmetic

/-! # Proofs for the compact paper results, batch 3: G32 certificates

The `_aux` theorems behind the frozen spec `HodgeLean/Papers/PapersG32Certificates.lean`
(`docs/specs/PapersG32Certificates.md`). Every theorem here is still open.
-/

namespace HodgeLean.Papers

open Polynomial Matrix
open scoped Kronecker

theorem papers_g32_vectors_index_aux :
    g32VectorTable.map (fun r => (r.i, r.n)) = g32WitnessTable.map (fun r => (r.i, r.n)) := by
  decide +kernel

theorem papers_g32_vectors_abs_sum_aux :
    (g32VectorTable.map fun r => r.n.natAbs).sum = 56 := by
  decide +kernel

theorem papers_g32_vectors_wellFormed_aux :
    ∀ r ∈ g32VectorTable, (r.coords.map Prod.fst).Pairwise (· < ·) ∧
      ∀ p ∈ r.coords, 1 ≤ p.1 ∧ p.1 ≤ 48 ∧ p.2 ≠ 0 ∧ (45 ≤ p.1 → Odd p.2) := by
  decide +kernel

theorem papers_g32_vectors_support_aux :
    ∀ r ∈ g32VectorTable,
      g32LatticeSupport (g32SparseVec r.coords) = (r.coords.map Prod.fst).toFinset := by
  decide +kernel

theorem papers_g32_character_identity_aux :
    g32CharSum g32VectorTable = g32ERho := by
  decide +kernel

theorem papers_g32_character_identity_int_aux :
    ∀ c : Fin 48, (c.val < 44 → g32IntCharSum g32VectorTable c = if c.val = 2 then 1 else 0) ∧
      (44 ≤ c.val → Even (g32IntCharSum g32VectorTable c)) := by
  decide +kernel

theorem papers_g32_character_identity_perturbed_aux :
    g32CharSum (g32PerturbCoeff 1 1 g32VectorTable) ≠ g32ERho := by
  decide +kernel

/-- Perturbing the coefficient of the rows of index `k` by `δ` adds `δ` times their vectors. -/
private theorem g32CharSum_perturbCoeff (k : ℕ) (δ : ℤ) (rows : List G32VectorRow) :
    g32CharSum (g32PerturbCoeff k δ rows) = g32CharSum rows +
      δ • ((rows.filter fun r => r.i = k).map fun r => g32SparseVec r.coords).sum := by
  induction rows with
  | nil => simp [g32CharSum, g32PerturbCoeff]
  | cons r rs ih =>
    simp only [g32CharSum, g32PerturbCoeff] at ih ⊢
    by_cases h : r.i = k
    · simp only [List.map_cons, h, ite_true, List.sum_cons, List.filter_cons, decide_true,
        ih, add_smul, smul_add]
      abel
    · simp only [List.map_cons, h, ite_false, List.sum_cons, List.filter_cons, decide_false,
        ih, Bool.false_eq_true]
      abel

/-- For every index `k ∈ 1..51`, the vectors of the rows of index `k` sum to a vector with a
nonzero free coordinate. -/
private theorem g32_row_free_nonzero :
    ∀ k < 52, 1 ≤ k → ∃ j : Fin 44,
      (((g32VectorTable.filter fun r => r.i = k).map fun r => g32SparseVec r.coords).sum).1 j ≠ 0 := by
  decide +kernel

theorem papers_g32_character_identity_perturbed_any_aux (k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k ≤ 51) (δ : ℤ) (hδ : δ ≠ 0) :
    g32CharSum (g32PerturbCoeff k δ g32VectorTable) ≠ g32ERho := by
  intro h
  rw [g32CharSum_perturbCoeff, papers_g32_character_identity_aux] at h
  obtain ⟨j, hj⟩ := g32_row_free_nonzero k (by omega) hk₁
  have h2 := congrArg (fun v : G32CharLattice => v.1 j) (add_eq_left.mp h)
  simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Prod.fst_zero, Pi.zero_apply] at h2
  exact hj ((mul_eq_zero.mp h2).resolve_left hδ)

/-- Powers of `ω` modulo `ω² + ω + 1`. -/
theorem papers3b_omega_pow {K : Type*} [Field K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 2 = -ω - 1 ∧ ω ^ 3 = 1 ∧ ω ^ 4 = ω ∧ ω ^ 5 = -ω - 1 ∧ ω ^ 6 = 1 := by
  refine ⟨by linear_combination hω, by linear_combination (ω - 1) * hω,
    by linear_combination (ω ^ 2 - ω) * hω, by linear_combination (ω ^ 3 - ω ^ 2 + 1) * hω,
    by linear_combination (ω ^ 4 - ω ^ 3 + ω - 1) * hω⟩

/-- Reduce a polynomial identity in `ω` modulo `ω² + ω + 1`. -/
macro "papers3b_omega_ring " h:term : tactic =>
  `(tactic| (ring_nf; all_goals (try simp only [($h).1, ($h).2.1, ($h).2.2.1, ($h).2.2.2.1, ($h).2.2.2.2]); all_goals ring_nf))

theorem papers_g32_r1_unitary_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32R1 ω ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hc := conj_omega ω hω
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g32R1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, hc, map_ofNat] <;>
    papers3b_omega_ring papers3b_omega_pow ω hω

theorem papers_g32_r2_unitary_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32R2 ω ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hc := conj_omega ω hω
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g32R2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, hc, map_ofNat] <;>
    papers3b_omega_ring papers3b_omega_pow ω hω

theorem papers_g32_x_unitary_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32X ω ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hc := conj_omega ω hω
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g32X, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, hc, map_ofNat] <;>
    papers3b_omega_ring papers3b_omega_pow ω hω

theorem papers_g32_y_unitary_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32Y ω ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hc := conj_omega ω hω
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g32Y, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, hc, map_ofNat] <;>
    papers3b_omega_ring papers3b_omega_pow ω hω

/-- The square of `y`, reduced modulo `ω² + ω + 1`. -/
theorem papers3b_y_sq {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    g32Y ω * g32Y ω =
      !![-(ω + 2) / 3, 0, (ω + 2) / 3, (ω + 2) / 3;
         0, -(ω + 2) / 3, (ω - 1) / 3, (1 - ω) / 3;
         (ω - 1) / 3, (ω + 2) / 3, (ω - 1) / 3, 0;
         (ω - 1) / 3, -(ω + 2) / 3, 0, (ω - 1) / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32Y, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow ω hω

/-- `r₁ r₂ x = y²`. -/
theorem papers3b_r1r2x {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    g32R1 ω * g32R2 ω * g32X ω = g32Y ω * g32Y ω := by
  rw [papers3b_y_sq ω hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R1, g32R2, g32X, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow ω hω

/-- `y³ = 1`. -/
theorem papers3b_y_cube {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    g32Y ω * g32Y ω * g32Y ω = 1 := by
  rw [papers3b_y_sq ω hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32Y, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow ω hω

theorem papers_g32_tuple_prod_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    g32R1 ω * g32R2 ω * g32X ω * g32Y ω = 1 := by
  rw [papers3b_r1r2x ω hω, papers3b_y_cube ω hω]

theorem papers_g32_r1_charpoly_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32R1 ω).charpoly = (X - C ω) * (X - 1) ^ 3 := by
  have : Infinite K := CharZero.infinite K
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, g32R1, Fin.succAbove]
  papers3b_omega_ring papers3b_omega_pow ω hω

theorem papers_g32_r2_charpoly_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32R2 ω).charpoly = (X - C (ω ^ 2)) * (X - 1) ^ 3 := by
  have : Infinite K := CharZero.infinite K
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, g32R2, Fin.succAbove]
  papers3b_omega_ring papers3b_omega_pow ω hω

theorem papers_g32_x_charpoly_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (ι : K) (hι : ι ^ 2 = -1) :
    (g32X ω).charpoly = (X - C ι) * (X + 1) ^ 2 * (X + C ι) := by
  have : Infinite K := CharZero.infinite K
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, g32X, Fin.succAbove]
  ring_nf
  simp only [hι]
  papers3b_omega_ring papers3b_omega_pow ω hω

/-- The square of `x`, reduced modulo `ω² + ω + 1`. -/
theorem papers3b_x_sq {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    g32X ω * g32X ω = !![1, 0, 0, 0; 0, 0, ω, 0; 0, -ω - 1, 0, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32X, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow ω hω

theorem papers_g32_x_sq_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32X ω * g32X ω).charpoly = (X - 1) ^ 2 * (X + 1) ^ 2 ∧ g32X ω ^ 4 = 1 := by
  have : Infinite K := CharZero.infinite K
  constructor
  · rw [papers3b_x_sq ω hω]
    apply Polynomial.funext
    intro x
    rw [Matrix.eval_charpoly]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    papers3b_omega_ring papers3b_omega_pow ω hω
  · rw [show g32X ω ^ 4 = (g32X ω * g32X ω) * (g32X ω * g32X ω) by noncomm_ring, papers3b_x_sq ω hω]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
      papers3b_omega_ring papers3b_omega_pow ω hω

theorem papers_g32_y_charpoly_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32Y ω).charpoly = (X - C ω) ^ 2 * (X - C (ω ^ 2)) ^ 2 ∧ g32Y ω ^ 3 = 1 ∧ g32Y ω ≠ 1 := by
  have : Infinite K := CharZero.infinite K
  refine ⟨?_, by rw [pow_three', papers3b_y_cube ω hω], ?_⟩
  · apply Polynomial.funext
    intro x
    rw [Matrix.eval_charpoly]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, g32Y, Fin.succAbove]
    papers3b_omega_ring papers3b_omega_pow ω hω
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [g32Y] at h00
    have h4 : ω = 4 := by linear_combination 3 * h00
    rw [h4] at hω
    norm_num at hω

theorem papers_g32_r1_det_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32R1 ω).det = ω := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, g32R1, Fin.succAbove]
  papers3b_omega_ring papers3b_omega_pow ω hω


theorem papers_g32_residue_traces_aux :
    g32B5.trace = 1/3 ∧ g32B7.trace = 2/3 := by
  constructor <;> simp [Matrix.trace, Fin.sum_univ_four, g32B5, g32B7, g32U1, g32V1, g32U2, g32V2] <;> norm_num

theorem papers_g32_residue_inf_aux :
    g32BInf.charpoly = (X - C (2/3)) ^ 2 * (X + C (2/3)) ^ 2 ∧
      (g32BInf - (2/3 : ℚ) • 1) * (g32BInf + (2/3 : ℚ) • 1) = 0 := by
  constructor
  · apply Polynomial.funext
    intro x
    rw [Matrix.eval_charpoly]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, g32BInf, g32B0, g32B5, g32B7,
      g32U1, g32V1, g32U2, g32V2]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, g32BInf, g32B0, g32B5, g32B7, g32U1, g32V1, g32U2,
        g32V2, Matrix.one_apply] <;> norm_num


theorem papers_g32_tuple_prod_perturbed_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    g32R1 ω * g32R2 ω * g32X ω * (g32Y ω + Matrix.single 0 0 1) ≠ 1 := by
  intro h
  have hp := papers_g32_tuple_prod_aux ω hω
  rw [mul_add, hp, add_eq_left] at h
  have hyA : g32Y ω * (g32R1 ω * g32R2 ω * g32X ω) = 1 := mul_eq_one_comm.mp hp
  have hE : (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) K) = 0 := by
    rw [← one_mul (Matrix.single 0 0 1), ← hyA, mul_assoc, h, mul_zero]
  have := congrFun (congrFun hE 0) 0
  simp at this

theorem papers_g32_pi_prod_aux :
    ∀ k : Fin 4, g32Pi k 0 * g32Pi k 1 * g32Pi k 2 * g32Pi k 3 = 1 := by
  decide

theorem papers_g32_pi_cycleType_aux :
    ∀ k : Fin 4, (g32Pi k 0).partition.parts = {4, 2} ∧
      (g32Pi k 1).partition.parts = {2, 1, 1, 1, 1} ∧
      (g32Pi k 2).partition.parts = {2, 1, 1, 1, 1} ∧ (g32Pi k 3).partition.parts = {3, 3} := by
  decide

/-- Words in the four permutations of each printed tuple carrying the point `0` to each point:
`g32PiOrbitWord k x` lists indices `j₁, …, j_m` with `π_{j₁} ⋯ π_{j_m} 0 = x` (found by a
breadth-first search; checked by `g32PiOrbitWord_spec`).
Source: G32 v0.16, proof of Proposition 6.3 ("generating a transitive group"). -/
def g32PiOrbitWord : Fin 4 → Fin 6 → List (Fin 4) :=
  ![![[], [0, 0], [0, 1], [3], [0], [1]], ![[], [0, 0], [0, 1], [3], [0], [1]],
    ![[], [0, 0], [0, 1], [3, 0], [0], [1]], ![[], [0, 0], [0, 2], [1], [0], [2]]]

example : g32PiOrbitWord 0 3 = [3] := rfl

/-- The words `g32PiOrbitWord k x` carry `0` to `x`. -/
theorem g32PiOrbitWord_spec :
    ∀ k : Fin 4, ∀ x : Fin 6, ((g32PiOrbitWord k x).map (g32Pi k)).prod 0 = x := by
  decide

theorem papers_g32_pi_transitive_aux (k : Fin 4) :
    MulAction.IsPretransitive (Subgroup.closure (Set.range (g32Pi k))) (Fin 6) := by
  have hmem : ∀ x : Fin 6,
      ((g32PiOrbitWord k x).map (g32Pi k)).prod ∈ Subgroup.closure (Set.range (g32Pi k)) := by
    intro x
    apply Subgroup.list_prod_mem
    intro σ hσ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hσ
    exact Subgroup.subset_closure (Set.mem_range_self j)
  refine ⟨fun x y => ⟨⟨_, hmem y⟩ * (⟨_, hmem x⟩)⁻¹, ?_⟩⟩
  show (((g32PiOrbitWord k y).map (g32Pi k)).prod *
      (((g32PiOrbitWord k x).map (g32Pi k)).prod)⁻¹) x = y
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.mpr (g32PiOrbitWord_spec k x).symm,
    g32PiOrbitWord_spec]

/-- Cycle types of products of two permutations of a tuple are invariant under simultaneous
conjugation. -/
theorem g32Pi_cycleType_mul_of_conj {k l : Fin 4} {g : Equiv.Perm (Fin 6)}
    (h : ∀ j, g * g32Pi k j * g⁻¹ = g32Pi l j) (a b : Fin 4) :
    (g32Pi k a * g32Pi k b).cycleType = (g32Pi l a * g32Pi l b).cycleType := by
  rw [← h a, ← h b, show g * g32Pi k a * g⁻¹ * (g * g32Pi k b * g⁻¹) =
    g * (g32Pi k a * g32Pi k b) * g⁻¹ by group, Equiv.Perm.cycleType_conj]

/-- The cycle types of `π₀π₁, π₀π₂, π₀π_∞, π₁π_∞` separate the four printed tuples. -/
theorem g32Pi_cycleType_invariant_injective :
    ∀ k l : Fin 4, ((g32Pi k 0 * g32Pi k 1).cycleType = (g32Pi l 0 * g32Pi l 1).cycleType ∧
      (g32Pi k 0 * g32Pi k 2).cycleType = (g32Pi l 0 * g32Pi l 2).cycleType ∧
      (g32Pi k 0 * g32Pi k 3).cycleType = (g32Pi l 0 * g32Pi l 3).cycleType ∧
      (g32Pi k 1 * g32Pi k 3).cycleType = (g32Pi l 1 * g32Pi l 3).cycleType) → k = l := by
  decide

theorem papers_g32_pi_not_conj_aux (k l : Fin 4) (hkl : k ≠ l) :
    ¬ ∃ g : Equiv.Perm (Fin 6), ∀ j, g * g32Pi k j * g⁻¹ = g32Pi l j := by
  rintro ⟨g, h⟩
  exact hkl (g32Pi_cycleType_invariant_injective k l
    ⟨g32Pi_cycleType_mul_of_conj h 0 1, g32Pi_cycleType_mul_of_conj h 0 2,
      g32Pi_cycleType_mul_of_conj h 0 3, g32Pi_cycleType_mul_of_conj h 1 3⟩)

/-- `g32PermMatrix` is multiplicative. -/
theorem g32PermMatrix_mul {K : Type*} [Field K] (σ τ : Equiv.Perm (Fin 6)) :
    g32PermMatrix (K := K) σ * g32PermMatrix τ = g32PermMatrix (σ * τ) := by
  ext i j
  simp [g32PermMatrix, Matrix.mul_apply, Finset.sum_ite_eq', eq_comm]

theorem papers_g32_cocycleTuple_prod_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    g32CocycleTuple ω k 0 * g32CocycleTuple ω k 1 * g32CocycleTuple ω k 2 *
      g32CocycleTuple ω k 3 * g32CocycleTuple ω k 4 * g32CocycleTuple ω k 5 = 1 := by
  simp only [g32CocycleTuple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    ← Matrix.mul_kronecker_mul, mul_one, one_mul, g32PermMatrix_mul]
  have h1 : g32PermMatrix (K := K) 1 = 1 := by
    ext i j; simp [g32PermMatrix, Matrix.one_apply, eq_comm]
  rw [papers_g32_tuple_prod_aux ω hω, papers_g32_pi_prod_aux k, h1, Matrix.one_kronecker_one]

/-! ### Statement 28: the Gram matrix `h_0` of the cocycle form

The six witnesses are supported on the first three punctures, where the tuple
`(r₁ ⊗ 1, r₂ ⊗ 1, x ⊗ π₀)` is the same for all four printed `S₆` tuples. A vector of
`ℂ^{Fin 4 × Fin 6}` is handled as a `4 × 6` matrix, on which `A ⊗ B` acts by `V ↦ A V Bᵀ`; the
cocycle condition and the 36 values of `S` then reduce to `4 × 6` matrix identities over `ℚ(ω)`.
The witnesses were found by exact computation over `ℚ(ω)` and are checked here entry by entry.
-/

private theorem g32Gram_star_omega (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : star ω = -1 - ω := by
  have hc : (starRingEnd ℂ ω) ^ 2 + starRingEnd ℂ ω + 1 = 0 := by
    have := congrArg (starRingEnd ℂ) hω; simpa using this
  have hfac : (ω - starRingEnd ℂ ω) * (ω + starRingEnd ℂ ω + 1) = 0 := by
    linear_combination hω - hc
  rcases mul_eq_zero.1 hfac with h | h
  · exfalso
    have hre : ω = (ω.re : ℂ) := by
      apply Complex.ext <;> simp
      have := congrArg Complex.im h; simp at this; linarith
    rw [hre] at hω
    have : (ω.re ^ 2 + ω.re + 1 : ℝ) = 0 := by exact_mod_cast hω
    nlinarith [sq_nonneg (ω.re + 1/2)]
  · show starRingEnd ℂ ω = _; linear_combination h

private def g32GramVec (V : Matrix (Fin 4) (Fin 6) ℂ) : Fin 4 × Fin 6 → ℂ := fun x => V x.1 x.2

private theorem g32GramVec_sub (V W : Matrix (Fin 4) (Fin 6) ℂ) : g32GramVec V - g32GramVec W = g32GramVec (V - W) := rfl
private theorem g32GramVec_add (V W : Matrix (Fin 4) (Fin 6) ℂ) : g32GramVec V + g32GramVec W = g32GramVec (V + W) := rfl
private theorem g32GramVec_zero : g32GramVec 0 = 0 := rfl

private theorem g32Gram_kron_mulVec (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 6) (Fin 6) ℂ)
    (V : Matrix (Fin 4) (Fin 6) ℂ) : (A ⊗ₖ B) *ᵥ g32GramVec V = g32GramVec (A * V * Bᵀ) := by
  ext ⟨i, j⟩
  simp only [g32GramVec, mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, mul_apply,
    transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

private theorem g32Gram_kron_one_mulVec (A : Matrix (Fin 4) (Fin 4) ℂ) (V : Matrix (Fin 4) (Fin 6) ℂ) :
    (A ⊗ₖ (1 : Matrix (Fin 6) (Fin 6) ℂ)) *ᵥ g32GramVec V = g32GramVec (A * V) := by
  rw [g32Gram_kron_mulVec, transpose_one, Matrix.mul_one]

private def g32GramTup (V0 V1 V2 : Matrix (Fin 4) (Fin 6) ℂ) : G32CocycleParam :=
  ![g32GramVec V0, g32GramVec V1, g32GramVec V2, 0, 0, 0]

private def g32GramPair (U C : Matrix (Fin 4) (Fin 6) ℂ) : ℂ := ∑ p, ∑ q, star (U p q) * C p q

private theorem g32Gram_star_dot (U C : Matrix (Fin 4) (Fin 6) ℂ) :
    star (g32GramVec U) ⬝ᵥ g32GramVec C = g32GramPair U C := by
  simp only [dotProduct, Fintype.sum_prod_type, g32GramPair, g32GramVec, Pi.star_apply]

private theorem g32Gram_Q0 (ω : ℂ) (k : Fin 4) : g32CocycleQ ω k 0 = 1 := by simp [g32CocycleQ]
private theorem g32Gram_Q1 (ω : ℂ) (k : Fin 4) : g32CocycleQ ω k 1 = g32R1 ω ⊗ₖ 1 := by
  simp [g32CocycleQ, List.finRange_succ, g32CocycleTuple]
private theorem g32Gram_Q2 (ω : ℂ) (k : Fin 4) :
    g32CocycleQ ω k 2 = (g32R1 ω ⊗ₖ 1) * (g32R2 ω ⊗ₖ 1) := by
  simp [g32CocycleQ, List.finRange_succ, g32CocycleTuple]

private theorem g32Gram_pi0 (k : Fin 4) : g32Pi k 0 = g32Pi 0 0 := by
  fin_cases k <;> rfl

private theorem g32Gram_C_tup (ω : ℂ) (k : Fin 4) (V0 V1 V2 : Matrix (Fin 4) (Fin 6) ℂ) :
    g32CocycleC ω k (g32GramTup V0 V1 V2) =
      ![g32GramVec (V0 - g32R1 ω * V0), g32GramVec (V1 - g32R2 ω * V1),
        g32GramVec (V2 - g32X ω * V2 * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ), 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [g32CocycleC, g32GramTup, sub_mulVec, g32CocycleTuple, g32Gram_kron_mulVec, g32GramVec_sub,
      g32Gram_pi0 k]

private theorem g32Gram_mem_of (ω : ℂ) (k : Fin 4) (V0 V1 V2 C0 C1 C2 : Matrix (Fin 4) (Fin 6) ℂ)
    (h0 : V0 - g32R1 ω * V0 = C0) (h1 : V1 - g32R2 ω * V1 = C1)
    (h2 : V2 - g32X ω * V2 * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = C2)
    (hm : C0 + g32R1 ω * C1 + g32R1 ω * (g32R2 ω * C2) = 0) :
    G32InCocycleSpace ω k (g32GramTup V0 V1 V2) := by
  rw [G32InCocycleSpace, g32Gram_C_tup, h0, h1, h2, Fin.sum_univ_six]
  simp [g32Gram_Q0, g32Gram_Q1, g32Gram_Q2, ← mulVec_mulVec, g32Gram_kron_one_mulVec, g32GramVec_add, hm, g32GramVec_zero]

private theorem g32Gram_F_tup (ω : ℂ) (k : Fin 4) (a : G32CocycleParam) :
    g32CocycleF ω k a 0 = 0 ∧ g32CocycleF ω k a 1 = g32CocycleC ω k a 0 ∧
      g32CocycleF ω k a 2 = g32CocycleC ω k a 0 + g32CocycleQ ω k 1 *ᵥ g32CocycleC ω k a 1 := by
  have e0 : (Finset.univ.filter fun j : Fin 6 => j < 0) = ∅ := by decide
  have e1 : (Finset.univ.filter fun j : Fin 6 => j < 1) = {0} := by decide
  have e2 : (Finset.univ.filter fun j : Fin 6 => j < 2) = {0, 1} := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp only [g32CocycleF, e0, e1, e2] <;> simp [g32Gram_Q0]

private theorem g32Gram_Q1_inv (ω : ℂ) (k : Fin 4) (R1H : Matrix (Fin 4) (Fin 4) ℂ)
    (hr1 : g32R1 ω * R1H = 1) : (g32CocycleQ ω k 1)⁻¹ = R1H ⊗ₖ 1 := by
  rw [g32Gram_Q1]
  apply Matrix.inv_eq_right_inv
  rw [← mul_kronecker_mul, hr1, Matrix.mul_one, one_kronecker_one]

private theorem g32Gram_Q2_inv (ω : ℂ) (k : Fin 4) (R1H R2H : Matrix (Fin 4) (Fin 4) ℂ)
    (hr1 : g32R1 ω * R1H = 1) (hr2 : g32R2 ω * R2H = 1) :
    (g32CocycleQ ω k 2)⁻¹ = (R2H ⊗ₖ 1) * (R1H ⊗ₖ 1) := by
  rw [g32Gram_Q2]
  apply Matrix.inv_eq_right_inv
  simp only [← mul_kronecker_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g32R2 ω), hr2, Matrix.one_mul, hr1, one_kronecker_one]

private theorem g32Gram_S_of (ω : ℂ) (k : Fin 4) (R1H R2H : Matrix (Fin 4) (Fin 4) ℂ)
    (hr1 : g32R1 ω * R1H = 1) (hr2 : g32R2 ω * R2H = 1)
    (V0 V1 V2 C0 C1 C2 U1 U2 W0 W1 W2 D0 D1 D2 : Matrix (Fin 4) (Fin 6) ℂ)
    (h0 : V0 - g32R1 ω * V0 = C0) (h1 : V1 - g32R2 ω * V1 = C1)
    (h2 : V2 - g32X ω * V2 * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = C2)
    (hU1 : R1H * C0 + V1 = U1) (hU2 : R2H * (R1H * (C0 + g32R1 ω * C1)) + V2 = U2)
    (k0 : W0 - g32R1 ω * W0 = D0) (k1 : W1 - g32R2 ω * W1 = D1)
    (k2 : W2 - g32X ω * W2 * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = D2) :
    g32CocycleS ω k (g32GramTup V0 V1 V2) (g32GramTup W0 W1 W2) =
      g32GramPair V0 D0 + g32GramPair U1 D1 + g32GramPair U2 D2 := by
  obtain ⟨f0, f1, f2⟩ := g32Gram_F_tup ω k (g32GramTup V0 V1 V2)
  rw [g32CocycleS, Fin.sum_univ_six, f0, f1, f2, g32Gram_C_tup, g32Gram_C_tup, h0, h1, h2, k0, k1, k2,
    g32Gram_Q2_inv ω k R1H R2H hr1 hr2, g32Gram_Q1_inv ω k R1H hr1, g32Gram_Q1, g32Gram_Q0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val,
    dotProduct_zero, add_zero, mulVec_zero, inv_one, zero_add, g32GramTup, Matrix.vecHead,
    Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one]
  simp only [← mulVec_mulVec, g32Gram_kron_one_mulVec, g32GramVec_add, hU1, hU2, g32Gram_star_dot]

private noncomputable def g32GramR1H (ω : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![((1/3) + (-1/3) * ω), ((-1/3) + (1/3) * ω), 0, ((1/3) + (-1/3) * ω);
    ((-1/3) + (-2/3) * ω), ((1/3) + (-1/3) * ω), 0, ((2/3) + (1/3) * ω);
    0, 0, (1), 0;
    ((1/3) + (2/3) * ω), ((2/3) + (1/3) * ω), 0, ((1/3) + (-1/3) * ω)]

private noncomputable def g32GramR2H (ω : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![((2/3) + (1/3) * ω), ((2/3) + (1/3) * ω), ((2/3) + (1/3) * ω), 0;
    ((-1/3) + (-2/3) * ω), ((2/3) + (1/3) * ω), ((-1/3) + (1/3) * ω), 0;
    ((-1/3) + (-2/3) * ω), ((-1/3) + (1/3) * ω), ((2/3) + (1/3) * ω), 0;
    0, 0, 0, (1)]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_r1 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : g32R1 ω * g32GramR1H ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g32R1, g32GramR1H, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_r2 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : g32R2 ω * g32GramR2H ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g32R2, g32GramR2H, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> grind

private theorem g32Gram_mulPT (M : Matrix (Fin 4) (Fin 6) ℂ) :
    M * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = Matrix.of fun i j => M i (![3, 4, 5, 1, 0, 2] j) := by
  have h : ∀ x, g32Pi 0 0 x = ![4, 3, 5, 0, 1, 2] x := by decide
  ext i j
  simp only [mul_apply, transpose_apply, g32PermMatrix, h, of_apply]
  fin_cases j <;> simp [Fin.sum_univ_succ]


private noncomputable def g32GramV00 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-5/3) + (-1/3) * ω), (-1) * ω, 0, 0, 0, 0;
    0, 0, 0, ((-2/3) + (-7/3) * ω), 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, ((-1/3) + (-2/3) * ω), 0]

private noncomputable def g32GramV01 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![(-2), ((1/3) + (-1/3) * ω), 0, (-1), 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, ((1/3) + (-1/3) * ω), 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramV02 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1) + (1/3) * ω), 0, 0, (-2/3) * ω, (2/3), 0;
    ((-1/3) + (-1/3) * ω), 0, 0, 0, 0, 0;
    ((-1/3) + (-1/3) * ω), ((-1/3) + (1/3) * ω), 0, ((-2/3) + (1/3) * ω), (-2/3) * ω, 0;
    0, ((-1/3) + (1/3) * ω), 0, ((-2/3) + (1/3) * ω), (1/3), 0]

private noncomputable def g32GramC00 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-2/3) + (1/3) * ω), ((-1/3) + (-2/3) * ω), 0, ((-4/3) + (-1/3) * ω), (1/3), 0;
    ((-1) + (-2/3) * ω), ((1/3) + (-1/3) * ω), 0, ((-1) + (-4/3) * ω), ((1/3) + (1/3) * ω), 0;
    0, 0, 0, 0, 0, 0;
    ((1) + (2/3) * ω), ((-1/3) + (1/3) * ω), 0, ((1) + (4/3) * ω), ((-1/3) + (-1/3) * ω), 0]

private noncomputable def g32GramC01 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-4/3) + (-2/3) * ω), (1/3), 0, ((-2/3) + (-1/3) * ω), ((-1/3) + (-1/3) * ω), 0;
    ((2/3) + (-2/3) * ω), (1/3) * ω, 0, ((1/3) + (-1/3) * ω), (1/3), 0;
    ((2/3) + (-2/3) * ω), (1/3) * ω, 0, ((1/3) + (-1/3) * ω), (1/3), 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramC02 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1) + (-1/3) * ω), (2/3), 0, (-2/3) * ω, ((-1/3) + (1/3) * ω), 0;
    ((-2/3) + (-4/3) * ω), ((1/3) + (1/3) * ω), 0, ((-1/3) + (-2/3) * ω), (-1/3) * ω, 0;
    ((-1/3) + (-1/3) * ω), (-1/3), 0, ((-2/3) + (1/3) * ω), (-2/3) * ω, 0;
    ((1/3) + (1) * ω), ((-2/3) + (-1/3) * ω), 0, ((-1/3) + (1) * ω), (-1/3) * ω, 0]

private noncomputable def g32GramU01 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1) + (2/3) * ω), 0, 0, (4/3) * ω, ((-1/3) + (-1/3) * ω), 0;
    ((1/3) + (1) * ω), ((-2/3) + (-1/3) * ω), 0, ((-1/3) + (1) * ω), (-1/3) * ω, 0;
    0, 0, 0, 0, ((1/3) + (-1/3) * ω), 0;
    ((-1/3) + (-1) * ω), ((2/3) + (1/3) * ω), 0, ((1/3) + (-1) * ω), (1/3) * ω, 0]

private noncomputable def g32GramU02 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![(2/3) * ω, (-2/3), 0, 0, ((1) + (-1/3) * ω), 0;
    ((1/3) + (1) * ω), ((-1/3) + (-1/3) * ω), 0, ((1/3) + (2/3) * ω), (1/3) * ω, 0;
    0, (1/3) * ω, 0, 0, 0, 0;
    ((-1/3) + (-1) * ω), ((1/3) + (2/3) * ω), 0, ((-1/3) + (-2/3) * ω), ((1/3) + (1/3) * ω), 0]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c00 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV00 ω - g32R1 ω * g32GramV00 ω = g32GramC00 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV00, g32GramC00, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c01 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV01 ω - g32R2 ω * g32GramV01 ω = g32GramC01 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV01, g32GramC01, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c02 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV02 ω - g32X ω * g32GramV02 ω * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = g32GramC02 ω := by
  rw [g32Gram_mulPT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV02, g32GramC02, g32X, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_m0 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramC00 ω + g32R1 ω * g32GramC01 ω + g32R1 ω * (g32R2 ω * g32GramC02 ω) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC00, g32GramC01, g32GramC02, g32R1, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u01 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR1H ω * g32GramC00 ω + g32GramV01 ω = g32GramU01 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC00, g32GramV01, g32GramU01, g32GramR1H, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u02 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR2H ω * (g32GramR1H ω * (g32GramC00 ω + g32R1 ω * g32GramC01 ω)) + g32GramV02 ω = g32GramU02 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC00, g32GramC01, g32GramV02, g32GramU02, g32GramR1H, g32GramR2H, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

private noncomputable def g32GramV10 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((1/3) + (-4/3) * ω), 0, 0, ((2/3) + (-2/3) * ω), ((-1/3) + (-2/3) * ω), 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramV11 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1/3) + (-5/3) * ω), 0, 0, ((-1/3) + (-2/3) * ω), (-1) * ω, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramV12 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![(-2/3) * ω, 0, 0, ((1/3) + (1/3) * ω), 0, 0;
    0, 0, 0, (1/3), 0, 0;
    (-1/3) * ω, 0, 0, ((-1/3) + (-2/3) * ω), 0, 0;
    ((-2/3) + (-2/3) * ω), 0, 0, ((-2/3) + (-2/3) * ω), 0, 0]

private noncomputable def g32GramC10 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1/3) + (-1) * ω), 0, 0, (-2/3) * ω, ((-1/3) + (-1/3) * ω), 0;
    ((2/3) + (-1/3) * ω), 0, 0, (2/3), (-1/3) * ω, 0;
    0, 0, 0, 0, 0, 0;
    ((-2/3) + (1/3) * ω), 0, 0, (-2/3), (1/3) * ω, 0]

private noncomputable def g32GramC11 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((1/3) + (-2/3) * ω), 0, 0, (-1/3) * ω, ((1/3) + (-1/3) * ω), 0;
    ((2/3) + (1) * ω), 0, 0, ((1/3) + (1/3) * ω), ((1/3) + (2/3) * ω), 0;
    ((2/3) + (1) * ω), 0, 0, ((1/3) + (1/3) * ω), ((1/3) + (2/3) * ω), 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramC12 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((1/3) + (-1/3) * ω), 0, 0, ((1/3) + (1/3) * ω), (-2/3) * ω, 0;
    ((1) + (1/3) * ω), 0, 0, (1/3), ((2/3) + (1/3) * ω), 0;
    (-1/3) * ω, 0, 0, ((-1/3) + (-2/3) * ω), ((1/3) + (1/3) * ω), 0;
    ((-1) + (-2/3) * ω), 0, 0, ((-2/3) + (-2/3) * ω), (-1/3), 0]

private noncomputable def g32GramU11 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1) + (-4/3) * ω), 0, 0, ((-1) + (-2/3) * ω), (-2/3) * ω, 0;
    ((-1) + (-2/3) * ω), 0, 0, ((-2/3) + (-2/3) * ω), (-1/3), 0;
    0, 0, 0, 0, 0, 0;
    ((1) + (2/3) * ω), 0, 0, ((2/3) + (2/3) * ω), (1/3), 0]

private noncomputable def g32GramU12 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1/3) + (-1/3) * ω), 0, 0, 0, (2/3) * ω, 0;
    ((-1) + (-1/3) * ω), 0, 0, 0, ((-2/3) + (-1/3) * ω), 0;
    0, 0, 0, 0, ((-1/3) + (-1/3) * ω), 0;
    (1/3), 0, 0, 0, (1/3), 0]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c10 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV10 ω - g32R1 ω * g32GramV10 ω = g32GramC10 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV10, g32GramC10, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c11 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV11 ω - g32R2 ω * g32GramV11 ω = g32GramC11 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV11, g32GramC11, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c12 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV12 ω - g32X ω * g32GramV12 ω * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = g32GramC12 ω := by
  rw [g32Gram_mulPT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV12, g32GramC12, g32X, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_m1 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramC10 ω + g32R1 ω * g32GramC11 ω + g32R1 ω * (g32R2 ω * g32GramC12 ω) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC10, g32GramC11, g32GramC12, g32R1, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u11 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR1H ω * g32GramC10 ω + g32GramV11 ω = g32GramU11 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC10, g32GramV11, g32GramU11, g32GramR1H, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u12 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR2H ω * (g32GramR1H ω * (g32GramC10 ω + g32R1 ω * g32GramC11 ω)) + g32GramV12 ω = g32GramU12 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC10, g32GramC11, g32GramV12, g32GramU12, g32GramR1H, g32GramR2H, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

private noncomputable def g32GramV20 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, ((-2/3) + (-1/3) * ω), 0, 0, ((-2/3) + (-1/3) * ω)]

private noncomputable def g32GramV21 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, ((1/3) + (1/3) * ω), 0, 0, ((1/3) + (1/3) * ω);
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramV22 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, ((2/9) + (1/9) * ω);
    0, 0, 0, 0, 0, 0;
    0, 0, ((-1/9) + (-2/9) * ω), 0, 0, ((-1/9) + (-2/9) * ω);
    0, 0, ((-1/9) + (-2/9) * ω), 0, 0, ((-1/9) + (-2/9) * ω)]

private noncomputable def g32GramC20 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, (-1/3) * ω, 0, 0, (-1/3) * ω;
    0, 0, (1/3), 0, 0, (1/3);
    0, 0, 0, 0, 0, 0;
    0, 0, (-1/3), 0, 0, (-1/3)]

private noncomputable def g32GramC21 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, ((1/9) + (-1/9) * ω), 0, 0, ((1/9) + (-1/9) * ω);
    0, 0, ((1/9) + (2/9) * ω), 0, 0, ((1/9) + (2/9) * ω);
    0, 0, ((1/9) + (2/9) * ω), 0, 0, ((1/9) + (2/9) * ω);
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramC22 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, ((2/9) + (1/9) * ω), 0, 0, ((2/9) + (1/9) * ω);
    0, 0, ((2/9) + (1/9) * ω), 0, 0, ((2/9) + (1/9) * ω);
    0, 0, ((-1/9) + (-2/9) * ω), 0, 0, ((-1/9) + (-2/9) * ω);
    0, 0, ((-1/3) + (-1/3) * ω), 0, 0, ((-1/3) + (-1/3) * ω)]

private noncomputable def g32GramU21 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, (-1/3), 0, 0, (-1/3);
    0, 0, ((-1/3) + (-1/3) * ω), 0, 0, ((-1/3) + (-1/3) * ω);
    0, 0, ((1/3) + (1/3) * ω), 0, 0, ((1/3) + (1/3) * ω);
    0, 0, ((1/3) + (1/3) * ω), 0, 0, ((1/3) + (1/3) * ω)]

private noncomputable def g32GramU22 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, ((-2/9) + (-1/9) * ω), 0, 0, 0;
    0, 0, ((-2/9) + (-1/9) * ω), 0, 0, ((-2/9) + (-1/9) * ω);
    0, 0, 0, 0, 0, 0;
    0, 0, ((2/9) + (1/9) * ω), 0, 0, ((2/9) + (1/9) * ω)]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c20 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV20 ω - g32R1 ω * g32GramV20 ω = g32GramC20 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV20, g32GramC20, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c21 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV21 ω - g32R2 ω * g32GramV21 ω = g32GramC21 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV21, g32GramC21, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c22 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV22 ω - g32X ω * g32GramV22 ω * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = g32GramC22 ω := by
  rw [g32Gram_mulPT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV22, g32GramC22, g32X, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_m2 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramC20 ω + g32R1 ω * g32GramC21 ω + g32R1 ω * (g32R2 ω * g32GramC22 ω) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC20, g32GramC21, g32GramC22, g32R1, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u21 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR1H ω * g32GramC20 ω + g32GramV21 ω = g32GramU21 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC20, g32GramV21, g32GramU21, g32GramR1H, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u22 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR2H ω * (g32GramR1H ω * (g32GramC20 ω + g32R1 ω * g32GramC21 ω)) + g32GramV22 ω = g32GramU22 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC20, g32GramC21, g32GramV22, g32GramU22, g32GramR1H, g32GramR2H, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

private noncomputable def g32GramV30 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, ((5/3) + (4/3) * ω), 0;
    0, 0, 0, 0, 0, 0;
    ((-1) + (-1) * ω), ((-1/3) + (1/3) * ω), 0, ((1/3) + (2/3) * ω), 0, 0]

private noncomputable def g32GramV31 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1/3) + (-2/3) * ω), 0, 0, 0, 0, 0;
    0, 0, 0, 0, ((1) + (2) * ω), 0;
    0, (1) * ω, 0, ((-1/3) + (-2/3) * ω), 0, 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramV32 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![(1/3) * ω, 0, 0, 0, ((2/3) + (-1/3) * ω), 0;
    (1/3), 0, 0, 0, (1/3) * ω, 0;
    (-2/3) * ω, ((-1/3) + (1/3) * ω), 0, 0, (1/3), 0;
    ((-1/3) + (-2/3) * ω), 0, 0, 0, ((-1/3) + (-2/3) * ω), 0]

private noncomputable def g32GramC30 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((1/3) + (-1/3) * ω), ((-1/3) + (-1/3) * ω), 0, (-1/3), ((1/3) + (-2/3) * ω), 0;
    ((2/3) + (1/3) * ω), (-1/3) * ω, 0, ((-1/3) + (-1/3) * ω), ((1) + (1/3) * ω), 0;
    0, 0, 0, 0, 0, 0;
    ((-2/3) + (-1/3) * ω), (1/3) * ω, 0, ((1/3) + (1/3) * ω), ((-1) + (-1/3) * ω), 0]

private noncomputable def g32GramC31 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![(-1/3) * ω, ((2/3) + (1/3) * ω), 0, (-1/3), (1), 0;
    ((1/3) + (1/3) * ω), ((-1/3) + (1/3) * ω), 0, (-1/3) * ω, (1) * ω, 0;
    ((1/3) + (1/3) * ω), ((-1/3) + (1/3) * ω), 0, (-1/3) * ω, (1) * ω, 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramC32 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![(1/3) * ω, ((2/3) + (-1/3) * ω), 0, 0, (2/3), 0;
    (1/3), ((1/3) + (2/3) * ω), 0, ((-1/3) + (-1/3) * ω), ((1) + (1) * ω), 0;
    (-2/3) * ω, (2/3) * ω, 0, (-1/3), (1/3), 0;
    ((-1/3) + (-2/3) * ω), (-1/3), 0, (1/3) * ω, ((-2/3) + (-1) * ω), 0]

private noncomputable def g32GramU31 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1) + (-1) * ω), (1/3) * ω, 0, ((1/3) + (1/3) * ω), ((-1) + (-1/3) * ω), 0;
    ((-1/3) + (-2/3) * ω), (-1/3), 0, (1/3) * ω, ((1/3) + (1) * ω), 0;
    0, (1) * ω, 0, ((-1/3) + (-2/3) * ω), 0, 0;
    ((1/3) + (2/3) * ω), (1/3), 0, (-1/3) * ω, ((2/3) + (1) * ω), 0]

private noncomputable def g32GramU32 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, ((-2/3) + (1/3) * ω), 0, 0, (-1/3) * ω, 0;
    0, ((-1/3) + (-2/3) * ω), 0, ((1/3) + (1/3) * ω), ((-1) + (-2/3) * ω), 0;
    0, ((-1/3) + (-1/3) * ω), 0, (1/3), 0, 0;
    0, (1/3), 0, (-1/3) * ω, ((1/3) + (1/3) * ω), 0]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c30 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV30 ω - g32R1 ω * g32GramV30 ω = g32GramC30 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV30, g32GramC30, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c31 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV31 ω - g32R2 ω * g32GramV31 ω = g32GramC31 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV31, g32GramC31, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c32 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV32 ω - g32X ω * g32GramV32 ω * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = g32GramC32 ω := by
  rw [g32Gram_mulPT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV32, g32GramC32, g32X, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_m3 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramC30 ω + g32R1 ω * g32GramC31 ω + g32R1 ω * (g32R2 ω * g32GramC32 ω) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC30, g32GramC31, g32GramC32, g32R1, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u31 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR1H ω * g32GramC30 ω + g32GramV31 ω = g32GramU31 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC30, g32GramV31, g32GramU31, g32GramR1H, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u32 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR2H ω * (g32GramR1H ω * (g32GramC30 ω + g32R1 ω * g32GramC31 ω)) + g32GramV32 ω = g32GramU32 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC30, g32GramC31, g32GramV32, g32GramU32, g32GramR1H, g32GramR2H, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

private noncomputable def g32GramV40 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, ((1/3) + (2/3) * ω), 0;
    0, 0, 0, 0, 0, 0;
    ((-2/3) + (-1/3) * ω), ((-1/3) + (1/3) * ω), 0, ((-2/3) + (2/3) * ω), 0, 0]

private noncomputable def g32GramV41 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-2/3) + (-4/3) * ω), 0, 0, 0, 0, 0;
    0, 0, 0, 0, (1) * ω, 0;
    0, ((-2/3) + (-1/3) * ω), 0, ((2/3) + (-2/3) * ω), 0, 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramV42 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1/3) + (-1/3) * ω), 0, 0, 0, ((2/3) + (1/3) * ω), 0;
    (2/3), 0, 0, 0, (-2/3), 0;
    ((1/3) + (-1/3) * ω), ((-4/3) + (-2/3) * ω), 0, 0, ((1/3) + (1/3) * ω), 0;
    ((-1/3) + (-1/3) * ω), 0, 0, 0, ((-1/3) + (-1/3) * ω), 0]

private noncomputable def g32GramC40 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![(-1/3) * ω, ((-1/3) + (-1/3) * ω), 0, ((-2/3) + (-2/3) * ω), (1/3), 0;
    (1/3), (-1/3) * ω, 0, (-2/3) * ω, ((1/3) + (1/3) * ω), 0;
    0, 0, 0, 0, 0, 0;
    (-1/3), (1/3) * ω, 0, (2/3) * ω, ((-1/3) + (-1/3) * ω), 0]

private noncomputable def g32GramC41 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![(-2/3) * ω, (1/3) * ω, 0, ((-2/3) + (-2/3) * ω), ((2/3) + (1/3) * ω), 0;
    ((2/3) + (2/3) * ω), ((-1/3) + (-1/3) * ω), 0, (2/3), ((-1/3) + (1/3) * ω), 0;
    ((2/3) + (2/3) * ω), ((-1/3) + (-1/3) * ω), 0, (2/3), ((-1/3) + (1/3) * ω), 0;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramC42 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1/3) + (-1/3) * ω), ((2/3) + (1/3) * ω), 0, 0, (1/3), 0;
    (2/3), (-1/3), 0, (-2/3) * ω, ((1/3) + (2/3) * ω), 0;
    ((1/3) + (-1/3) * ω), (-2/3), 0, ((-2/3) + (-2/3) * ω), ((1/3) + (1/3) * ω), 0;
    ((-1/3) + (-1/3) * ω), (-1/3), 0, (-2/3), (-1/3) * ω, 0]

private noncomputable def g32GramU41 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![((-1) + (-4/3) * ω), (1/3) * ω, 0, (2/3) * ω, ((-1/3) + (-1/3) * ω), 0;
    ((-1/3) + (-1/3) * ω), (-1/3), 0, (-2/3), (2/3) * ω, 0;
    0, ((-2/3) + (-1/3) * ω), 0, ((2/3) + (-2/3) * ω), 0, 0;
    ((1/3) + (1/3) * ω), (1/3), 0, (2/3), (1/3) * ω, 0]

private noncomputable def g32GramU42 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, ((-2/3) + (-1/3) * ω), 0, 0, ((1/3) + (1/3) * ω), 0;
    0, (1/3), 0, (2/3) * ω, ((-1) + (-2/3) * ω), 0;
    0, ((-2/3) + (-2/3) * ω), 0, ((2/3) + (2/3) * ω), 0, 0;
    0, (1/3), 0, (2/3), (-1/3), 0]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c40 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV40 ω - g32R1 ω * g32GramV40 ω = g32GramC40 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV40, g32GramC40, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c41 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV41 ω - g32R2 ω * g32GramV41 ω = g32GramC41 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV41, g32GramC41, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c42 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV42 ω - g32X ω * g32GramV42 ω * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = g32GramC42 ω := by
  rw [g32Gram_mulPT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV42, g32GramC42, g32X, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_m4 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramC40 ω + g32R1 ω * g32GramC41 ω + g32R1 ω * (g32R2 ω * g32GramC42 ω) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC40, g32GramC41, g32GramC42, g32R1, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u41 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR1H ω * g32GramC40 ω + g32GramV41 ω = g32GramU41 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC40, g32GramV41, g32GramU41, g32GramR1H, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u42 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR2H ω * (g32GramR1H ω * (g32GramC40 ω + g32R1 ω * g32GramC41 ω)) + g32GramV42 ω = g32GramU42 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC40, g32GramC41, g32GramV42, g32GramU42, g32GramR1H, g32GramR2H, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

private noncomputable def g32GramV50 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, ((-1/3) + (-1/3) * ω), 0, 0, ((-1/3) + (-1/3) * ω)]

private noncomputable def g32GramV51 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, ((1/3) + (2/3) * ω), 0, 0, ((1/3) + (2/3) * ω);
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramV52 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, ((1/9) + (-1/9) * ω);
    0, 0, 0, 0, 0, ((2/9) + (1/9) * ω);
    0, 0, ((2/9) + (1/9) * ω), 0, 0, ((1/9) + (-1/9) * ω);
    0, 0, ((-1/9) + (-2/9) * ω), 0, 0, ((-1/9) + (-2/9) * ω)]

private noncomputable def g32GramC50 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, ((1/9) + (-1/9) * ω), 0, 0, ((1/9) + (-1/9) * ω);
    0, 0, ((2/9) + (1/9) * ω), 0, 0, ((2/9) + (1/9) * ω);
    0, 0, 0, 0, 0, 0;
    0, 0, ((-2/9) + (-1/9) * ω), 0, 0, ((-2/9) + (-1/9) * ω)]

private noncomputable def g32GramC51 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, (1/3), 0, 0, (1/3);
    0, 0, (1/3) * ω, 0, 0, (1/3) * ω;
    0, 0, (1/3) * ω, 0, 0, (1/3) * ω;
    0, 0, 0, 0, 0, 0]

private noncomputable def g32GramC52 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, ((1/9) + (-1/9) * ω), 0, 0, ((1/9) + (-1/9) * ω);
    0, 0, ((1/3) + (1/3) * ω), 0, 0, ((1/3) + (1/3) * ω);
    0, 0, ((2/9) + (1/9) * ω), 0, 0, ((2/9) + (1/9) * ω);
    0, 0, ((-1/9) + (-2/9) * ω), 0, 0, ((-1/9) + (-2/9) * ω)]

private noncomputable def g32GramU51 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, ((-2/9) + (-1/9) * ω), 0, 0, ((-2/9) + (-1/9) * ω);
    0, 0, ((-1/9) + (-2/9) * ω), 0, 0, ((-1/9) + (-2/9) * ω);
    0, 0, ((1/3) + (2/3) * ω), 0, 0, ((1/3) + (2/3) * ω);
    0, 0, ((1/9) + (2/9) * ω), 0, 0, ((1/9) + (2/9) * ω)]

private noncomputable def g32GramU52 (ω : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![0, 0, ((-1/9) + (1/9) * ω), 0, 0, 0;
    0, 0, ((-1/3) + (-1/3) * ω), 0, 0, ((-1/9) + (-2/9) * ω);
    0, 0, 0, 0, 0, ((-1/9) + (-2/9) * ω);
    0, 0, 0, 0, 0, 0]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c50 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV50 ω - g32R1 ω * g32GramV50 ω = g32GramC50 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV50, g32GramC50, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c51 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV51 ω - g32R2 ω * g32GramV51 ω = g32GramC51 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV51, g32GramC51, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_c52 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramV52 ω - g32X ω * g32GramV52 ω * (g32PermMatrix (K := ℂ) (g32Pi 0 0))ᵀ = g32GramC52 ω := by
  rw [g32Gram_mulPT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramV52, g32GramC52, g32X, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_m5 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramC50 ω + g32R1 ω * g32GramC51 ω + g32R1 ω * (g32R2 ω * g32GramC52 ω) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC50, g32GramC51, g32GramC52, g32R1, g32R2, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u51 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR1H ω * g32GramC50 ω + g32GramV51 ω = g32GramU51 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC50, g32GramV51, g32GramU51, g32GramR1H, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_u52 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    g32GramR2H ω * (g32GramR1H ω * (g32GramC50 ω + g32R1 ω * g32GramC51 ω)) + g32GramV52 ω = g32GramU52 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [g32GramC50, g32GramC51, g32GramV52, g32GramU52, g32GramR1H, g32GramR2H, g32R1, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk,
      Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;> grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g00 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω))
      (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω)) = g32H0 ω 0 0 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω) (g32Gram_u01 ω hω) (g32Gram_u02 ω hω)
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV00, g32GramU01, g32GramU02, g32GramC00, g32GramC01, g32GramC02, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g01 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω))
      (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω)) = g32H0 ω 0 1 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω) (g32Gram_u01 ω hω) (g32Gram_u02 ω hω)
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV00, g32GramU01, g32GramU02, g32GramC10, g32GramC11, g32GramC12, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g02 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω))
      (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω)) = g32H0 ω 0 2 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω) (g32Gram_u01 ω hω) (g32Gram_u02 ω hω)
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV00, g32GramU01, g32GramU02, g32GramC20, g32GramC21, g32GramC22, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g03 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω))
      (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω)) = g32H0 ω 0 3 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω) (g32Gram_u01 ω hω) (g32Gram_u02 ω hω)
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV00, g32GramU01, g32GramU02, g32GramC30, g32GramC31, g32GramC32, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g04 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω))
      (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω)) = g32H0 ω 0 4 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω) (g32Gram_u01 ω hω) (g32Gram_u02 ω hω)
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV00, g32GramU01, g32GramU02, g32GramC40, g32GramC41, g32GramC42, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g05 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω))
      (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω)) = g32H0 ω 0 5 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω) (g32Gram_u01 ω hω) (g32Gram_u02 ω hω)
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV00, g32GramU01, g32GramU02, g32GramC50, g32GramC51, g32GramC52, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g10 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω))
      (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω)) = g32H0 ω 1 0 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω) (g32Gram_u11 ω hω) (g32Gram_u12 ω hω)
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV10, g32GramU11, g32GramU12, g32GramC00, g32GramC01, g32GramC02, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g11 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω))
      (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω)) = g32H0 ω 1 1 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω) (g32Gram_u11 ω hω) (g32Gram_u12 ω hω)
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV10, g32GramU11, g32GramU12, g32GramC10, g32GramC11, g32GramC12, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g12 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω))
      (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω)) = g32H0 ω 1 2 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω) (g32Gram_u11 ω hω) (g32Gram_u12 ω hω)
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV10, g32GramU11, g32GramU12, g32GramC20, g32GramC21, g32GramC22, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g13 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω))
      (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω)) = g32H0 ω 1 3 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω) (g32Gram_u11 ω hω) (g32Gram_u12 ω hω)
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV10, g32GramU11, g32GramU12, g32GramC30, g32GramC31, g32GramC32, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g14 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω))
      (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω)) = g32H0 ω 1 4 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω) (g32Gram_u11 ω hω) (g32Gram_u12 ω hω)
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV10, g32GramU11, g32GramU12, g32GramC40, g32GramC41, g32GramC42, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g15 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω))
      (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω)) = g32H0 ω 1 5 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω) (g32Gram_u11 ω hω) (g32Gram_u12 ω hω)
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV10, g32GramU11, g32GramU12, g32GramC50, g32GramC51, g32GramC52, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g20 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω))
      (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω)) = g32H0 ω 2 0 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω) (g32Gram_u21 ω hω) (g32Gram_u22 ω hω)
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV20, g32GramU21, g32GramU22, g32GramC00, g32GramC01, g32GramC02, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g21 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω))
      (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω)) = g32H0 ω 2 1 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω) (g32Gram_u21 ω hω) (g32Gram_u22 ω hω)
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV20, g32GramU21, g32GramU22, g32GramC10, g32GramC11, g32GramC12, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g22 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω))
      (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω)) = g32H0 ω 2 2 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω) (g32Gram_u21 ω hω) (g32Gram_u22 ω hω)
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV20, g32GramU21, g32GramU22, g32GramC20, g32GramC21, g32GramC22, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g23 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω))
      (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω)) = g32H0 ω 2 3 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω) (g32Gram_u21 ω hω) (g32Gram_u22 ω hω)
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV20, g32GramU21, g32GramU22, g32GramC30, g32GramC31, g32GramC32, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g24 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω))
      (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω)) = g32H0 ω 2 4 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω) (g32Gram_u21 ω hω) (g32Gram_u22 ω hω)
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV20, g32GramU21, g32GramU22, g32GramC40, g32GramC41, g32GramC42, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g25 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω))
      (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω)) = g32H0 ω 2 5 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω) (g32Gram_u21 ω hω) (g32Gram_u22 ω hω)
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV20, g32GramU21, g32GramU22, g32GramC50, g32GramC51, g32GramC52, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g30 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω))
      (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω)) = g32H0 ω 3 0 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω) (g32Gram_u31 ω hω) (g32Gram_u32 ω hω)
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV30, g32GramU31, g32GramU32, g32GramC00, g32GramC01, g32GramC02, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g31 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω))
      (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω)) = g32H0 ω 3 1 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω) (g32Gram_u31 ω hω) (g32Gram_u32 ω hω)
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV30, g32GramU31, g32GramU32, g32GramC10, g32GramC11, g32GramC12, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g32 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω))
      (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω)) = g32H0 ω 3 2 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω) (g32Gram_u31 ω hω) (g32Gram_u32 ω hω)
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV30, g32GramU31, g32GramU32, g32GramC20, g32GramC21, g32GramC22, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g33 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω))
      (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω)) = g32H0 ω 3 3 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω) (g32Gram_u31 ω hω) (g32Gram_u32 ω hω)
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV30, g32GramU31, g32GramU32, g32GramC30, g32GramC31, g32GramC32, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g34 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω))
      (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω)) = g32H0 ω 3 4 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω) (g32Gram_u31 ω hω) (g32Gram_u32 ω hω)
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV30, g32GramU31, g32GramU32, g32GramC40, g32GramC41, g32GramC42, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g35 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω))
      (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω)) = g32H0 ω 3 5 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω) (g32Gram_u31 ω hω) (g32Gram_u32 ω hω)
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV30, g32GramU31, g32GramU32, g32GramC50, g32GramC51, g32GramC52, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g40 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω))
      (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω)) = g32H0 ω 4 0 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω) (g32Gram_u41 ω hω) (g32Gram_u42 ω hω)
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV40, g32GramU41, g32GramU42, g32GramC00, g32GramC01, g32GramC02, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g41 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω))
      (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω)) = g32H0 ω 4 1 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω) (g32Gram_u41 ω hω) (g32Gram_u42 ω hω)
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV40, g32GramU41, g32GramU42, g32GramC10, g32GramC11, g32GramC12, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g42 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω))
      (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω)) = g32H0 ω 4 2 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω) (g32Gram_u41 ω hω) (g32Gram_u42 ω hω)
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV40, g32GramU41, g32GramU42, g32GramC20, g32GramC21, g32GramC22, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g43 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω))
      (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω)) = g32H0 ω 4 3 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω) (g32Gram_u41 ω hω) (g32Gram_u42 ω hω)
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV40, g32GramU41, g32GramU42, g32GramC30, g32GramC31, g32GramC32, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g44 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω))
      (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω)) = g32H0 ω 4 4 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω) (g32Gram_u41 ω hω) (g32Gram_u42 ω hω)
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV40, g32GramU41, g32GramU42, g32GramC40, g32GramC41, g32GramC42, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g45 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω))
      (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω)) = g32H0 ω 4 5 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω) (g32Gram_u41 ω hω) (g32Gram_u42 ω hω)
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV40, g32GramU41, g32GramU42, g32GramC50, g32GramC51, g32GramC52, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g50 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω))
      (g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω)) = g32H0 ω 5 0 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω) (g32Gram_u51 ω hω) (g32Gram_u52 ω hω)
    (g32Gram_c00 ω hω) (g32Gram_c01 ω hω) (g32Gram_c02 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV50, g32GramU51, g32GramU52, g32GramC00, g32GramC01, g32GramC02, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g51 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω))
      (g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω)) = g32H0 ω 5 1 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω) (g32Gram_u51 ω hω) (g32Gram_u52 ω hω)
    (g32Gram_c10 ω hω) (g32Gram_c11 ω hω) (g32Gram_c12 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV50, g32GramU51, g32GramU52, g32GramC10, g32GramC11, g32GramC12, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g52 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω))
      (g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω)) = g32H0 ω 5 2 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω) (g32Gram_u51 ω hω) (g32Gram_u52 ω hω)
    (g32Gram_c20 ω hω) (g32Gram_c21 ω hω) (g32Gram_c22 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV50, g32GramU51, g32GramU52, g32GramC20, g32GramC21, g32GramC22, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g53 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω))
      (g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω)) = g32H0 ω 5 3 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω) (g32Gram_u51 ω hω) (g32Gram_u52 ω hω)
    (g32Gram_c30 ω hω) (g32Gram_c31 ω hω) (g32Gram_c32 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV50, g32GramU51, g32GramU52, g32GramC30, g32GramC31, g32GramC32, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g54 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω))
      (g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω)) = g32H0 ω 5 4 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω) (g32Gram_u51 ω hω) (g32Gram_u52 ω hω)
    (g32Gram_c40 ω hω) (g32Gram_c41 ω hω) (g32Gram_c42 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV50, g32GramU51, g32GramU52, g32GramC40, g32GramC41, g32GramC42, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

set_option linter.unusedSimpArgs false in
private theorem g32Gram_g55 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    (1 + 2 * ω) * g32CocycleS ω k (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω))
      (g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω)) = g32H0 ω 5 5 := by
  rw [g32Gram_S_of ω k _ _ (g32Gram_r1 ω hω) (g32Gram_r2 ω hω) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω) (g32Gram_u51 ω hω) (g32Gram_u52 ω hω)
    (g32Gram_c50 ω hω) (g32Gram_c51 ω hω) (g32Gram_c52 ω hω)]
  have hs := g32Gram_star_omega ω hω
  simp only [g32GramPair, Fin.sum_univ_succ, Fin.sum_univ_zero, g32GramV50, g32GramU51, g32GramU52, g32GramC50, g32GramC51, g32GramC52, g32H0, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Matrix.empty_val', Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    star_add, star_sub, star_neg, star_mul', star_zero, star_one, star_div₀, star_ofNat, hs,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  grind

theorem papers_g32_cocycle_gram_h0_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    ∃ z : Fin 6 → G32CocycleParam, (∀ a, G32InCocycleSpace ω k (z a)) ∧
      ∀ a b, (1 + 2 * ω) * g32CocycleS ω k (z a) (z b) = g32H0 ω a b := by
  refine ⟨![g32GramTup (g32GramV00 ω) (g32GramV01 ω) (g32GramV02 ω),
    g32GramTup (g32GramV10 ω) (g32GramV11 ω) (g32GramV12 ω),
    g32GramTup (g32GramV20 ω) (g32GramV21 ω) (g32GramV22 ω),
    g32GramTup (g32GramV30 ω) (g32GramV31 ω) (g32GramV32 ω),
    g32GramTup (g32GramV40 ω) (g32GramV41 ω) (g32GramV42 ω),
    g32GramTup (g32GramV50 ω) (g32GramV51 ω) (g32GramV52 ω)], ?_, ?_⟩
  · intro a
    fin_cases a
    · exact g32Gram_mem_of ω k _ _ _ _ _ _ (g32Gram_c00 ω hω) (g32Gram_c01 ω hω)
        (g32Gram_c02 ω hω) (g32Gram_m0 ω hω)
    · exact g32Gram_mem_of ω k _ _ _ _ _ _ (g32Gram_c10 ω hω) (g32Gram_c11 ω hω)
        (g32Gram_c12 ω hω) (g32Gram_m1 ω hω)
    · exact g32Gram_mem_of ω k _ _ _ _ _ _ (g32Gram_c20 ω hω) (g32Gram_c21 ω hω)
        (g32Gram_c22 ω hω) (g32Gram_m2 ω hω)
    · exact g32Gram_mem_of ω k _ _ _ _ _ _ (g32Gram_c30 ω hω) (g32Gram_c31 ω hω)
        (g32Gram_c32 ω hω) (g32Gram_m3 ω hω)
    · exact g32Gram_mem_of ω k _ _ _ _ _ _ (g32Gram_c40 ω hω) (g32Gram_c41 ω hω)
        (g32Gram_c42 ω hω) (g32Gram_m4 ω hω)
    · exact g32Gram_mem_of ω k _ _ _ _ _ _ (g32Gram_c50 ω hω) (g32Gram_c51 ω hω)
        (g32Gram_c52 ω hω) (g32Gram_m5 ω hω)
  · intro a b
    fin_cases a <;> fin_cases b
    · exact g32Gram_g00 ω hω k
    · exact g32Gram_g01 ω hω k
    · exact g32Gram_g02 ω hω k
    · exact g32Gram_g03 ω hω k
    · exact g32Gram_g04 ω hω k
    · exact g32Gram_g05 ω hω k
    · exact g32Gram_g10 ω hω k
    · exact g32Gram_g11 ω hω k
    · exact g32Gram_g12 ω hω k
    · exact g32Gram_g13 ω hω k
    · exact g32Gram_g14 ω hω k
    · exact g32Gram_g15 ω hω k
    · exact g32Gram_g20 ω hω k
    · exact g32Gram_g21 ω hω k
    · exact g32Gram_g22 ω hω k
    · exact g32Gram_g23 ω hω k
    · exact g32Gram_g24 ω hω k
    · exact g32Gram_g25 ω hω k
    · exact g32Gram_g30 ω hω k
    · exact g32Gram_g31 ω hω k
    · exact g32Gram_g32 ω hω k
    · exact g32Gram_g33 ω hω k
    · exact g32Gram_g34 ω hω k
    · exact g32Gram_g35 ω hω k
    · exact g32Gram_g40 ω hω k
    · exact g32Gram_g41 ω hω k
    · exact g32Gram_g42 ω hω k
    · exact g32Gram_g43 ω hω k
    · exact g32Gram_g44 ω hω k
    · exact g32Gram_g45 ω hω k
    · exact g32Gram_g50 ω hω k
    · exact g32Gram_g51 ω hω k
    · exact g32Gram_g52 ω hω k
    · exact g32Gram_g53 ω hω k
    · exact g32Gram_g54 ω hω k
    · exact g32Gram_g55 ω hω k

end HodgeLean.Papers
