import HodgeLean.Papers.G34BoundaryDefs
import HodgeLean.Papers.WeilTransfer

/-! # Proof obligations for the G34 boundary certificate -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set Filter
open Matrix
open scoped Topology Matrix QuadraticAlgebra
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

local notation "𝕂" => QuadraticAlgebra ℚ (-3) 0

section Certificate

/-- The cube root of unity in the coordinates `re + im • √-3`. -/
theorem g34b_ω_eq_aux : g34b_ω = ⟨-1/2, 1/2⟩ := by
  rw [g34b_ω, div_eq_iff (by norm_num)]
  ext <;> simp [QuadraticAlgebra.omega]

/-- A block matrix with vanishing upper-left block: `det (0 A; C B) = (-1)ⁿ det A det C`. -/
theorem g34b_det_fromBlocks_zero₁₁_aux {R : Type*} [CommRing R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) R) :
    (fromBlocks 0 A C B).det = (-1) ^ n * (A.det * C.det) := by
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) =
      fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 := by
    simp [fromBlocks_multiply]
  have hJdet : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).det = 1 := by
    rw [hJ, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]
    simp
  have hM : fromBlocks 0 A C B = fromBlocks A 0 B (-C) * fromBlocks 0 1 (-1) 0 := by
    simp [fromBlocks_multiply]
  rw [hM, det_mul, hJdet, mul_one, det_fromBlocks_zero₁₂, det_neg]
  simp only [Fintype.card_fin]
  ring

/-- The lower-right block of `S` is skew-Hermitian, entry by entry. -/
theorem g34b_S_skew₂₂_aux : g34b_S.toBlocks₂₂ᴴ = -g34b_S.toBlocks₂₂ := by
  simp only [g34b_S, toBlocks_fromBlocks₂₂]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g34b_ω_eq_aux] <;> norm_num

theorem g34b_S_skew_aux : g34b_Sᴴ = -g34b_S := by
  have h22 := g34b_S_skew₂₂_aux
  simp only [g34b_S, toBlocks_fromBlocks₂₂] at h22
  rw [g34b_S, fromBlocks_conjTranspose, fromBlocks_neg, h22, g34b_D]
  congr 1
  · simp
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem g34b_S_det_aux : g34b_S.det = 81 := by
  rw [g34b_S, g34b_det_fromBlocks_zero₁₁_aux, g34b_D, det_diagonal, det_diagonal]
  simp [Fin.prod_univ_four]
  norm_num

theorem g34b_h1_aux : g34b_H1 g34b_N := by
  intro j k
  simp [g34b_N, Matrix.fromBlocks_multiply]

/-- An explicit inverse of `X₁`. -/
def g34b_X₀inv : Matrix (Fin 4) (Fin 4) 𝕂 :=
  !![⟨4/3, 0⟩, ⟨-1/3, 0⟩, ⟨-1/6, -1/6⟩, ⟨-1/3, 1/3⟩;
    ⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1/2, -1/2⟩;
    ⟨-1/2, 1/2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1/2, -1/2⟩;
    ⟨-1/3, -1/3⟩, ⟨-1/6, 1/6⟩, ⟨1/6, 1/6⟩, ⟨4/3, 0⟩]

theorem g34b_X₀_mul_inv_aux : g34b_X 0 * g34b_X₀inv = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [g34b_X, g34b_X₀inv, g34b_ω_eq_aux, Matrix.mul_apply, Fin.sum_univ_four,
      QuadraticAlgebra.norm_def] <;> norm_num

/-- The span of `b₁, …, b₄` lies in the kernel of the projection to the last four coordinates. -/
theorem g34b_inr_eq_zero_aux {x : Fin 4 ⊕ Fin 4 → 𝕂}
    (hx : x ∈ Submodule.span 𝕂
      (Set.range fun i : Fin 4 => (Pi.single (Sum.inl i) 1 : Fin 4 ⊕ Fin 4 → 𝕂))) :
    ∀ i, x (Sum.inr i) = 0 := by
  have hle : Submodule.span 𝕂
      (Set.range fun i : Fin 4 => (Pi.single (Sum.inl i) 1 : Fin 4 ⊕ Fin 4 → 𝕂)) ≤
      LinearMap.ker (LinearMap.funLeft 𝕂 𝕂 (Sum.inr : Fin 4 → Fin 4 ⊕ Fin 4)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    funext k
    simp [LinearMap.funLeft]
  intro i
  exact congrFun (LinearMap.mem_ker.mp (hle hx)) i

theorem g34b_sumElim_mem_aux (u : Fin 4 → 𝕂) :
    (Sum.elim u 0 : Fin 4 ⊕ Fin 4 → 𝕂) ∈ Submodule.span 𝕂
      (Set.range fun i : Fin 4 => (Pi.single (Sum.inl i) 1 : Fin 4 ⊕ Fin 4 → 𝕂)) := by
  have h : (Sum.elim u 0 : Fin 4 ⊕ Fin 4 → 𝕂) =
      ∑ i, u i • (Pi.single (Sum.inl i) 1 : Fin 4 ⊕ Fin 4 → 𝕂) := by
    funext k
    rcases k with k | k <;> simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem g34b_N_mulVec_aux (j : Fin 17) (x : Fin 4 ⊕ Fin 4 → 𝕂) :
    g34b_N j *ᵥ x = Sum.elim (g34b_X j *ᵥ (x ∘ Sum.inr)) 0 := by
  funext k
  rcases k with k | k <;>
    simp [g34b_N, fromBlocks, mulVec, dotProduct, Fintype.sum_sum_type]

theorem g34b_I_eq_aux :
    g34b_I g34b_N = Submodule.span 𝕂
      (Set.range fun i : Fin 4 => (Pi.single (Sum.inl i) 1 : Fin 4 ⊕ Fin 4 → 𝕂)) := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    rintro _ ⟨x, rfl⟩
    rw [Matrix.toLin'_apply, g34b_N_mulVec_aux]
    exact g34b_sumElim_mem_aux _
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.mem_iSup_of_mem 0 ⟨Sum.elim 0 (g34b_X₀inv *ᵥ Pi.single i 1), ?_⟩
    rw [Matrix.toLin'_apply, g34b_N_mulVec_aux]
    funext k
    rcases k with k | k
    · show (g34b_X 0 *ᵥ (g34b_X₀inv *ᵥ Pi.single i 1)) k =
        (Pi.single (Sum.inl i) 1 : Fin 4 ⊕ Fin 4 → 𝕂) (Sum.inl k)
      rw [Matrix.mulVec_mulVec, g34b_X₀_mul_inv_aux, Matrix.one_mulVec]
      simp [Pi.single_apply]
    · simp


theorem g34b_h2_aux : g34b_H2 g34b_S g34b_N 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [g34b_I_eq_aux, finrank_span_eq_card]
    · simp
    · have h := (Pi.basisFun 𝕂 (Fin 4 ⊕ Fin 4)).linearIndependent.comp Sum.inl Sum.inl_injective
      convert h using 1
      funext i
      simp
  · intro x hx y hy
    rw [g34b_I_eq_aux] at hx hy
    have hx' := g34b_inr_eq_zero_aux hx
    have hy' := g34b_inr_eq_zero_aux hy
    simp [dotProduct, mulVec, Fintype.sum_sum_type, g34b_S, fromBlocks, hx', hy']
  · intro j x hx
    rw [g34b_I_eq_aux] at hx
    have hx' : x ∘ Sum.inr = 0 := funext (g34b_inr_eq_zero_aux hx)
    rw [g34b_N_mulVec_aux, hx']
    funext k
    rcases k with k | k <;> simp

theorem g34b_S_mul_N_aux (j : Fin 17) :
    g34b_S * g34b_N j = fromBlocks 0 0 0 (g34b_D * g34b_X j) := by
  simp [g34b_S, g34b_N, fromBlocks_multiply]

theorem g34b_beta_eq_aux (j : Fin 17) (x y : Fin 4 ⊕ Fin 4 → 𝕂) :
    g34b_beta g34b_S (g34b_N j) x y =
      star (x ∘ Sum.inr) ⬝ᵥ ((g34b_D * g34b_X j) *ᵥ (y ∘ Sum.inr)) := by
  rw [g34b_beta, g34b_S_mul_N_aux]
  simp [dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks]

theorem g34b_re_sum_aux {ι : Type*} (s : Finset ι) (f : ι → 𝕂) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum (QuadraticAlgebra.reₗ (R := ℚ) (a := -3) (b := 0)) f s

theorem g34b_reForm_aux (H : Matrix (Fin 4) (Fin 4) 𝕂) (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ H *ᵥ v).re = ∑ k, ∑ l,
      ((((v k).re * (H k l).re + 3 * (v k).im * (H k l).im) * (v l).re -
        3 * ((v k).re * (H k l).im - (v k).im * (H k l).re) * (v l).im)) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
  rw [g34b_re_sum_aux]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [g34b_re_sum_aux]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  ring


theorem g34b_DX_herm_0_aux : (g34b_D * g34b_X 0)ᴴ = g34b_D * g34b_X 0 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_1_aux : (g34b_D * g34b_X 1)ᴴ = g34b_D * g34b_X 1 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_2_aux : (g34b_D * g34b_X 2)ᴴ = g34b_D * g34b_X 2 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux] <;> norm_num

theorem g34b_DX_herm_3_aux : (g34b_D * g34b_X 3)ᴴ = g34b_D * g34b_X 3 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_4_aux : (g34b_D * g34b_X 4)ᴴ = g34b_D * g34b_X 4 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_5_aux : (g34b_D * g34b_X 5)ᴴ = g34b_D * g34b_X 5 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux]

theorem g34b_DX_herm_6_aux : (g34b_D * g34b_X 6)ᴴ = g34b_D * g34b_X 6 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_7_aux : (g34b_D * g34b_X 7)ᴴ = g34b_D * g34b_X 7 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux]

theorem g34b_DX_herm_8_aux : (g34b_D * g34b_X 8)ᴴ = g34b_D * g34b_X 8 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_9_aux : (g34b_D * g34b_X 9)ᴴ = g34b_D * g34b_X 9 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux] <;> norm_num

theorem g34b_DX_herm_10_aux : (g34b_D * g34b_X 10)ᴴ = g34b_D * g34b_X 10 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_11_aux : (g34b_D * g34b_X 11)ᴴ = g34b_D * g34b_X 11 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_12_aux : (g34b_D * g34b_X 12)ᴴ = g34b_D * g34b_X 12 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_13_aux : (g34b_D * g34b_X 13)ᴴ = g34b_D * g34b_X 13 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_14_aux : (g34b_D * g34b_X 14)ᴴ = g34b_D * g34b_X 14 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_15_aux : (g34b_D * g34b_X 15)ᴴ = g34b_D * g34b_X 15 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_herm_16_aux : (g34b_D * g34b_X 16)ᴴ = g34b_D * g34b_X 16 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_DX_nonpos_0_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 0) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (1/4:ℚ) * (v 1).re + (1/4:ℚ) * (v 3).re + (1/4:ℚ) * (v 1).im
      + (-1/2:ℚ) * (v 2).im + (3/4:ℚ) * (v 3).im), mul_self_nonneg ((v 1).re + (9/13:ℚ) * (v 3).re
      + (-12/13:ℚ) * (v 0).im + (-3/13:ℚ) * (v 1).im + (6/13:ℚ) * (v 2).im + (-21/13:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).re + (-3/4:ℚ) * (v 3).re + (3/2:ℚ) * (v 0).im + (-3/4:ℚ) * (v 3).im),
      mul_self_nonneg ((v 3).re + (-14/43:ℚ) * (v 0).im + (16/43:ℚ) * (v 1).im
      + (20/43:ℚ) * (v 2).im + (-5/43:ℚ) * (v 3).im), mul_self_nonneg ((v 0).im
      + (11/28:ℚ) * (v 1).im + (3/28:ℚ) * (v 2).im + (5/14:ℚ) * (v 3).im), mul_self_nonneg ((v 1).im
      + (-1/15:ℚ) * (v 2).im + (2/5:ℚ) * (v 3).im), mul_self_nonneg ((v 2).im
      + (-3/8:ℚ) * (v 3).im), mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_1_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 1) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (1/2:ℚ) * (v 1).re + (-1/2:ℚ) * (v 2).re
      + (3/2:ℚ) * (v 3).re + (3/2:ℚ) * (v 1).im + (-1/2:ℚ) * (v 2).im + (3/2:ℚ) * (v 3).im),
      mul_self_nonneg ((v 1).re + (-1/3:ℚ) * (v 2).re + (v 3).re + (-2:ℚ) * (v 0).im
      + (-1:ℚ) * (v 1).im + (v 2).im + (-3:ℚ) * (v 3).im)]

theorem g34b_DX_nonpos_2_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 2) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux]
  linarith [mul_self_nonneg ((v 1).re + (1/6:ℚ) * (v 2).re + (1/2:ℚ) * (v 3).re + (1/2:ℚ) * (v 2).im
      + (-3/2:ℚ) * (v 3).im), mul_self_nonneg ((v 2).re + (-3/5:ℚ) * (v 3).re
      + (-18/35:ℚ) * (v 1).im + (-3/35:ℚ) * (v 2).im + (-9/7:ℚ) * (v 3).im),
      mul_self_nonneg ((v 3).re + (1/2:ℚ) * (v 1).im + (1/2:ℚ) * (v 2).im),
      mul_self_nonneg ((v 1).im + (-1/15:ℚ) * (v 2).im + (2/5:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).im + (-3/8:ℚ) * (v 3).im), mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_3_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 3) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 1).re + (3/4:ℚ) * (v 3).re + (-3/4:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).re + (-3/4:ℚ) * (v 3).re + (-3/4:ℚ) * (v 3).im),
      mul_self_nonneg ((v 3).re + (2/5:ℚ) * (v 1).im + (2/5:ℚ) * (v 2).im),
      mul_self_nonneg ((v 1).im + (-1/9:ℚ) * (v 2).im + (5/6:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).im + (-3/4:ℚ) * (v 3).im), mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_4_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 4) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 2).re + (-3/4:ℚ) * (v 3).re + (-3/4:ℚ) * (v 3).im),
      mul_self_nonneg ((v 3).re + (4/9:ℚ) * (v 2).im + (-1/3:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).im + (-3/4:ℚ) * (v 3).im), mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_5_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 5) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux]
  linarith [mul_self_nonneg ((v 2).re), mul_self_nonneg ((v 2).im)]

theorem g34b_DX_nonpos_6_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 6) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 2).re + (-3/4:ℚ) * (v 3).re + (-3/4:ℚ) * (v 3).im),
      mul_self_nonneg ((v 3).re + (4/13:ℚ) * (v 2).im + (-3/13:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).im + (-3/4:ℚ) * (v 3).im), mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_7_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 7) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux]
  linarith [mul_self_nonneg ((v 3).re), mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_8_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 8) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (v 1).re + (-1/2:ℚ) * (v 2).re + (v 3).re
      + (1/2:ℚ) * (v 2).im), mul_self_nonneg ((v 2).re + (-6:ℚ) * (v 0).im + (-6:ℚ) * (v 1).im
      + (3:ℚ) * (v 2).im + (-6:ℚ) * (v 3).im)]

theorem g34b_DX_nonpos_9_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 9) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux]
  linarith [mul_self_nonneg ((v 0).re + (5/6:ℚ) * (v 1).re + (-1/2:ℚ) * (v 2).re + (v 3).re
      + (1/2:ℚ) * (v 1).im + (1/2:ℚ) * (v 2).im), mul_self_nonneg ((v 1).re + (3/7:ℚ) * (v 2).re
      + (-18/7:ℚ) * (v 0).im + (-15/7:ℚ) * (v 1).im + (9/7:ℚ) * (v 2).im + (-18/7:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).re + (-6:ℚ) * (v 0).im + (-5:ℚ) * (v 1).im + (3:ℚ) * (v 2).im
      + (-6:ℚ) * (v 3).im), mul_self_nonneg ((v 1).im)]

theorem g34b_DX_nonpos_10_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 10) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (1/2:ℚ) * (v 1).re + (-3/10:ℚ) * (v 2).re
      + (4/5:ℚ) * (v 3).re + (7/10:ℚ) * (v 1).im + (-1/10:ℚ) * (v 2).im + (3/5:ℚ) * (v 3).im),
      mul_self_nonneg ((v 1).re + (-5/17:ℚ) * (v 2).re + (12/17:ℚ) * (v 3).re
      + (-42/17:ℚ) * (v 0).im + (-21/17:ℚ) * (v 1).im + (21/17:ℚ) * (v 2).im
      + (-42/17:ℚ) * (v 3).im), mul_self_nonneg ((v 2).re + (-129/194:ℚ) * (v 3).re
      + (-135/194:ℚ) * (v 0).im + (-123/97:ℚ) * (v 1).im + (93/194:ℚ) * (v 2).im
      + (-144/97:ℚ) * (v 3).im), mul_self_nonneg ((v 3).re + (-57/49:ℚ) * (v 0).im
      + (-40/147:ℚ) * (v 1).im + (79/147:ℚ) * (v 2).im + (-44/49:ℚ) * (v 3).im),
      mul_self_nonneg ((v 0).im + (37/81:ℚ) * (v 1).im + (1/9:ℚ) * (v 2).im + (29/81:ℚ) * (v 3).im),
      mul_self_nonneg ((v 1).im + (-18/29:ℚ) * (v 2).im + (4/29:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).im + (-5/8:ℚ) * (v 3).im), mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_11_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 11) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (5/14:ℚ) * (v 1).re + (-3/14:ℚ) * (v 2).re
      + (5/7:ℚ) * (v 3).re + (11/14:ℚ) * (v 1).im + (-5/14:ℚ) * (v 2).im + (6/7:ℚ) * (v 3).im),
      mul_self_nonneg ((v 1).re + (-67/177:ℚ) * (v 2).re + (48/59:ℚ) * (v 3).re
      + (-154/59:ℚ) * (v 0).im + (-55/59:ℚ) * (v 1).im + (53/59:ℚ) * (v 2).im
      + (-130/59:ℚ) * (v 3).im), mul_self_nonneg ((v 2).re + (-207/277:ℚ) * (v 3).re
      + (111/277:ℚ) * (v 0).im + (-150/277:ℚ) * (v 1).im + (48/277:ℚ) * (v 2).im
      + (-258/277:ℚ) * (v 3).im), mul_self_nonneg ((v 3).re + (-56/67:ℚ) * (v 0).im
      + (-35/201:ℚ) * (v 1).im + (122/201:ℚ) * (v 2).im + (-57/67:ℚ) * (v 3).im),
      mul_self_nonneg ((v 0).im + (80/183:ℚ) * (v 1).im + (37/183:ℚ) * (v 2).im
      + (25/61:ℚ) * (v 3).im), mul_self_nonneg ((v 1).im + (-46/133:ℚ) * (v 2).im
      + (-24/133:ℚ) * (v 3).im), mul_self_nonneg ((v 2).im + (-9/16:ℚ) * (v 3).im),
      mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_12_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 12) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (1/2:ℚ) * (v 1).re + (-1/5:ℚ) * (v 2).re
      + (4/5:ℚ) * (v 3).re + (7/10:ℚ) * (v 1).im + (-2/5:ℚ) * (v 2).im + (3/5:ℚ) * (v 3).im),
      mul_self_nonneg ((v 1).re + (-6/17:ℚ) * (v 2).re + (12/17:ℚ) * (v 3).re
      + (-42/17:ℚ) * (v 0).im + (-21/17:ℚ) * (v 1).im + (12/17:ℚ) * (v 2).im
      + (-42/17:ℚ) * (v 3).im), mul_self_nonneg ((v 2).re + (-59/106:ℚ) * (v 3).re
      + (65/53:ℚ) * (v 0).im + (7/53:ℚ) * (v 1).im + (-4/53:ℚ) * (v 2).im + (-23/106:ℚ) * (v 3).im),
      mul_self_nonneg ((v 3).re + (-22/191:ℚ) * (v 0).im + (102/191:ℚ) * (v 1).im
      + (78/191:ℚ) * (v 2).im + (-1/191:ℚ) * (v 3).im), mul_self_nonneg ((v 0).im
      + (299/516:ℚ) * (v 1).im + (-41/516:ℚ) * (v 2).im + (28/43:ℚ) * (v 3).im),
      mul_self_nonneg ((v 1).im + (-79/337:ℚ) * (v 2).im + (144/337:ℚ) * (v 3).im),
      mul_self_nonneg ((v 2).im + (-9/26:ℚ) * (v 3).im), mul_self_nonneg ((v 3).im)]

theorem g34b_DX_nonpos_13_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 13) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (v 1).re + (-1/2:ℚ) * (v 2).re + (v 3).re + (v 1).im
      + (1/2:ℚ) * (v 2).im), mul_self_nonneg ((v 1).re + (1/2:ℚ) * (v 2).re + (-3:ℚ) * (v 0).im
      + (-3:ℚ) * (v 1).im + (3/2:ℚ) * (v 2).im + (-3:ℚ) * (v 3).im)]

theorem g34b_DX_nonpos_14_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 14) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 1).re + (-1/2:ℚ) * (v 2).re + (3/2:ℚ) * (v 3).re
      + (3/2:ℚ) * (v 2).im + (-3/2:ℚ) * (v 3).im), mul_self_nonneg ((v 2).re + (-1:ℚ) * (v 3).re
      + (-2:ℚ) * (v 1).im + (v 2).im + (-3:ℚ) * (v 3).im)]

theorem g34b_DX_nonpos_15_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 15) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (1/4:ℚ) * (v 1).re + (3/4:ℚ) * (v 3).re + (3/4:ℚ) * (v 1).im
      + (-1/2:ℚ) * (v 2).im + (3/4:ℚ) * (v 3).im), mul_self_nonneg ((v 1).re + (-4/7:ℚ) * (v 2).re
      + (9/7:ℚ) * (v 3).re + (-12/7:ℚ) * (v 0).im + (-3/7:ℚ) * (v 1).im + (6/7:ℚ) * (v 2).im
      + (-15/7:ℚ) * (v 3).im), mul_self_nonneg ((v 2).re + (-15/16:ℚ) * (v 3).re
      + (3/8:ℚ) * (v 0).im + (-15/8:ℚ) * (v 1).im + (9/8:ℚ) * (v 2).im + (-45/16:ℚ) * (v 3).im),
      mul_self_nonneg ((v 3).re + (6:ℚ) * (v 0).im + (2:ℚ) * (v 1).im + (2:ℚ) * (v 2).im
      + (3:ℚ) * (v 3).im)]

theorem g34b_DX_nonpos_16_aux (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X 16) *ᵥ v).re ≤ 0 := by
  rw [g34b_reForm_aux]
  simp [Fin.sum_univ_four, g34b_D, g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def]
  linarith [mul_self_nonneg ((v 0).re + (1/2:ℚ) * (v 1).re + (v 3).re + (1/2:ℚ) * (v 1).im),
      mul_self_nonneg ((v 1).re + (-6:ℚ) * (v 0).im + (-3:ℚ) * (v 1).im + (-6:ℚ) * (v 3).im)]

theorem g34b_DX_herm_aux (j : Fin 17) : (g34b_D * g34b_X j)ᴴ = g34b_D * g34b_X j := by
  fin_cases j
  · exact g34b_DX_herm_0_aux
  · exact g34b_DX_herm_1_aux
  · exact g34b_DX_herm_2_aux
  · exact g34b_DX_herm_3_aux
  · exact g34b_DX_herm_4_aux
  · exact g34b_DX_herm_5_aux
  · exact g34b_DX_herm_6_aux
  · exact g34b_DX_herm_7_aux
  · exact g34b_DX_herm_8_aux
  · exact g34b_DX_herm_9_aux
  · exact g34b_DX_herm_10_aux
  · exact g34b_DX_herm_11_aux
  · exact g34b_DX_herm_12_aux
  · exact g34b_DX_herm_13_aux
  · exact g34b_DX_herm_14_aux
  · exact g34b_DX_herm_15_aux
  · exact g34b_DX_herm_16_aux

theorem g34b_DX_nonpos_aux (j : Fin 17) (v : Fin 4 → 𝕂) :
    (star v ⬝ᵥ (g34b_D * g34b_X j) *ᵥ v).re ≤ 0 := by
  fin_cases j
  · exact g34b_DX_nonpos_0_aux v
  · exact g34b_DX_nonpos_1_aux v
  · exact g34b_DX_nonpos_2_aux v
  · exact g34b_DX_nonpos_3_aux v
  · exact g34b_DX_nonpos_4_aux v
  · exact g34b_DX_nonpos_5_aux v
  · exact g34b_DX_nonpos_6_aux v
  · exact g34b_DX_nonpos_7_aux v
  · exact g34b_DX_nonpos_8_aux v
  · exact g34b_DX_nonpos_9_aux v
  · exact g34b_DX_nonpos_10_aux v
  · exact g34b_DX_nonpos_11_aux v
  · exact g34b_DX_nonpos_12_aux v
  · exact g34b_DX_nonpos_13_aux v
  · exact g34b_DX_nonpos_14_aux v
  · exact g34b_DX_nonpos_15_aux v
  · exact g34b_DX_nonpos_16_aux v

/-- The sum `Σ_j X_j`, as printed entries. -/
def g34b_Xsum : Matrix (Fin 4) (Fin 4) 𝕂 :=
  !![⟨32, 0⟩, ⟨17, -22/3⟩, ⟨-17/2, 3/2⟩, ⟨27, -6⟩;
    ⟨51, 22⟩, ⟨67, 0⟩, ⟨-47/2, -21/2⟩, ⟨72, 19⟩;
    ⟨-51/2, -9/2⟩, ⟨-47/2, 21/2⟩, ⟨40, 0⟩, ⟨-99/2, 19/2⟩;
    ⟨27, 6⟩, ⟨24, -19/3⟩, ⟨-33/2, -19/6⟩, ⟨51, 0⟩]

theorem g34b_Xsum_00_aux : (∑ j, g34b_X j) 0 0 = g34b_Xsum 0 0 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux]
  norm_num

theorem g34b_Xsum_01_aux : (∑ j, g34b_X j) 0 1 = g34b_Xsum 0 1 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_Xsum_02_aux : (∑ j, g34b_X j) 0 2 = g34b_Xsum 0 2 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_Xsum_03_aux : (∑ j, g34b_X j) 0 3 = g34b_Xsum 0 3 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_Xsum_10_aux : (∑ j, g34b_X j) 1 0 = g34b_Xsum 1 0 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_Xsum_11_aux : (∑ j, g34b_X j) 1 1 = g34b_Xsum 1 1 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux]
  norm_num

theorem g34b_Xsum_12_aux : (∑ j, g34b_X j) 1 2 = g34b_Xsum 1 2 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_Xsum_13_aux : (∑ j, g34b_X j) 1 3 = g34b_Xsum 1 3 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_Xsum_20_aux : (∑ j, g34b_X j) 2 0 = g34b_Xsum 2 0 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_Xsum_21_aux : (∑ j, g34b_X j) 2 1 = g34b_Xsum 2 1 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_Xsum_22_aux : (∑ j, g34b_X j) 2 2 = g34b_Xsum 2 2 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux]
  norm_num

theorem g34b_Xsum_23_aux : (∑ j, g34b_X j) 2 3 = g34b_Xsum 2 3 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_Xsum_30_aux : (∑ j, g34b_X j) 3 0 = g34b_Xsum 3 0 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_Xsum_31_aux : (∑ j, g34b_X j) 3 1 = g34b_Xsum 3 1 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_Xsum_32_aux : (∑ j, g34b_X j) 3 2 = g34b_Xsum 3 2 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_Xsum_33_aux : (∑ j, g34b_X j) 3 3 = g34b_Xsum 3 3 := by
  rw [Matrix.sum_apply]
  ext <;> simp [Fin.sum_univ_succ, g34b_X, g34b_Xsum, g34b_ω_eq_aux]
  norm_num

theorem g34b_DX_sum_aux : ∑ j, g34b_D * g34b_X j = g34b_D * g34b_Xsum := by
  rw [← Finset.mul_sum]
  congr 1
  refine Matrix.ext fun i k => ?_
  fin_cases i <;> fin_cases k
  all_goals first
    | exact g34b_Xsum_00_aux
    | exact g34b_Xsum_01_aux
    | exact g34b_Xsum_02_aux
    | exact g34b_Xsum_03_aux
    | exact g34b_Xsum_10_aux
    | exact g34b_Xsum_11_aux
    | exact g34b_Xsum_12_aux
    | exact g34b_Xsum_13_aux
    | exact g34b_Xsum_20_aux
    | exact g34b_Xsum_21_aux
    | exact g34b_Xsum_22_aux
    | exact g34b_Xsum_23_aux
    | exact g34b_Xsum_30_aux
    | exact g34b_Xsum_31_aux
    | exact g34b_Xsum_32_aux
    | exact g34b_Xsum_33_aux

theorem g34b_DX_sum_neg_aux (v : Fin 4 → 𝕂) (hv : v ≠ 0) :
    (star v ⬝ᵥ (∑ j, g34b_D * g34b_X j) *ᵥ v).re < 0 := by
  have hpos : 0 < ∑ k, ((v k).re * (v k).re + (v k).im * (v k).im) := by
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have hk' : (v k).re ≠ 0 ∨ (v k).im ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (QuadraticAlgebra.ext h.1 h.2)
    refine Finset.sum_pos' (fun i _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      ⟨k, Finset.mem_univ _, ?_⟩
    rcases hk' with h | h
    · exact add_pos_of_pos_of_nonneg (mul_self_pos.mpr h) (mul_self_nonneg _)
    · exact add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.mpr h)
  rw [g34b_DX_sum_aux, g34b_reForm_aux]
  simp only [Fin.sum_univ_four] at hpos
  simp [Fin.sum_univ_four, g34b_D, g34b_Xsum]
  linarith [mul_self_nonneg ((v 0).re + (51/95:ℚ) * (v 1).re + (-51/190:ℚ) * (v 2).re
      + (81/95:ℚ) * (v 3).re + (66/95:ℚ) * (v 1).im + (-27/190:ℚ) * (v 2).im
      + (54/95:ℚ) * (v 3).im), mul_self_nonneg ((v 1).re + (-932/3669:ℚ) * (v 2).re
      + (903/1223:ℚ) * (v 3).re + (-2090/1223:ℚ) * (v 0).im + (-1122/1223:ℚ) * (v 1).im
      + (1227/1223:ℚ) * (v 2).im + (-2723/1223:ℚ) * (v 3).im), mul_self_nonneg ((v 2).re
      + (-301068/435337:ℚ) * (v 3).re + (-6846/62191:ℚ) * (v 0).im + (-334386/435337:ℚ) * (v 1).im
      + (91269/435337:ℚ) * (v 2).im + (-526110/435337:ℚ) * (v 3).im), mul_self_nonneg ((v 3).re
      + (-1638441/10381717:ℚ) * (v 0).im + (4845279/20763434:ℚ) * (v 1).im
      + (6835803/20763434:ℚ) * (v 2).im + (-3196989/20763434:ℚ) * (v 3).im),
      mul_self_nonneg ((v 0).im + (951992343/1792552724:ℚ) * (v 1).im
      + (-73932543/1792552724:ℚ) * (v 2).im + (944179137/1792552724:ℚ) * (v 3).im),
      mul_self_nonneg ((v 1).im + (-37068124353/94725611197:ℚ) * (v 2).im
      + (45664246503/94725611197:ℚ) * (v 3).im), mul_self_nonneg ((v 2).im
      + (-1463630873949/3000352103251:ℚ) * (v 3).im), mul_self_nonneg ((v 3).im)]

theorem g34b_dot_herm_aux (H : Matrix (Fin 4) (Fin 4) 𝕂) (hH : Hᴴ = H) (u w : Fin 4 → 𝕂) :
    star w ⬝ᵥ H *ᵥ u = star (star u ⬝ᵥ H *ᵥ w) := by
  have he : ∀ i j, star (H i j) = H j i := fun i j => by
    rw [← conjTranspose_apply, hH]
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum, he]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem g34b_h3_aux : g34b_H3 g34b_S g34b_N := by
  refine ⟨fun j x y => ?_, -1, Or.inr rfl, fun j x => ?_, fun x hx => ?_⟩
  · rw [g34b_beta_eq_aux, g34b_beta_eq_aux]
    exact g34b_dot_herm_aux _ (g34b_DX_herm_aux j) _ _
  · rw [g34b_beta_eq_aux]
    have := g34b_DX_nonpos_aux j (x ∘ Sum.inr)
    linarith
  · have hv : x ∘ Sum.inr ≠ 0 := by
      intro h
      apply hx
      rw [g34b_I_eq_aux]
      have hx' : x = Sum.elim (x ∘ Sum.inl) 0 := by
        funext k
        rcases k with k | k
        · rfl
        · exact congrFun h k
      rw [hx']
      exact g34b_sumElim_mem_aux _
    have h := g34b_DX_sum_neg_aux _ hv
    have hsum : ∑ j, g34b_beta g34b_S (g34b_N j) x x =
        star (x ∘ Sum.inr) ⬝ᵥ (∑ j, g34b_D * g34b_X j) *ᵥ (x ∘ Sum.inr) := by
      simp only [g34b_beta_eq_aux, Matrix.sum_mulVec, dotProduct_sum]
    rw [hsum]
    linarith

/-- Sixteen rational coordinates of the upper-right block: the real parts of the diagonal and
the real and imaginary parts above it. -/
def g34b_coord : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) 𝕂 →ₗ[ℚ] (Fin 16 → ℚ) where
  toFun M := ![
    (M (Sum.inl 0) (Sum.inr 0)).re, (M (Sum.inl 1) (Sum.inr 1)).re, (M (Sum.inl 2) (Sum.inr 2)).re,
    (M (Sum.inl 3) (Sum.inr 3)).re, (M (Sum.inl 0) (Sum.inr 1)).re, (M (Sum.inl 0) (Sum.inr 1)).im,
    (M (Sum.inl 0) (Sum.inr 2)).re, (M (Sum.inl 0) (Sum.inr 2)).im, (M (Sum.inl 0) (Sum.inr 3)).re,
    (M (Sum.inl 0) (Sum.inr 3)).im, (M (Sum.inl 1) (Sum.inr 2)).re, (M (Sum.inl 1) (Sum.inr 2)).im,
    (M (Sum.inl 1) (Sum.inr 3)).re, (M (Sum.inl 1) (Sum.inr 3)).im, (M (Sum.inl 2) (Sum.inr 3)).re,
    (M (Sum.inl 2) (Sum.inr 3)).im]
  map_add' M M' := by
    funext k
    fin_cases k <;> simp
  map_smul' c M := by
    funext k
    fin_cases k <;> simp

/-- The coordinates of `N_j` for the sixteen indices `j ≠ 7`. -/
def g34b_Rlit : Matrix (Fin 16) (Fin 16) ℚ :=
  !![2, 2, 2, 2, 1/2, -1/6, 0, 1/3, 1/2, -1/2, 0, 0, 3/2, 1/2, -3/2, 1/2;
    2, 6, 2, 6, 1, -1, -1, 1/3, 3, -1, -3, -1, 9, 3, -6, 0;
    0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 1/2, -1/2, 3/2, 3/2, -3/2, 3/2;
    0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3/2, 1/2, -3/2, 1/2;
    0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 1;
    0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3/2, 1/2;
    2, 6, 2, 2, 2, 0, -1, -1/3, 2, 0, -3, -1, 6, 0, -3, 1;
    3, 8, 3, 3, 5/2, -1/2, -3/2, -1/2, 3, 0, -3, -2, 15/2, 3/2, -9/2, 3/2;
    5, 8, 4, 5, 5/2, -7/6, -3/2, 1/6, 4, -1, -7/2, -3/2, 9, 2, -6, 1;
    7, 9, 5, 7, 5/2, -11/6, -3/2, 5/6, 5, -2, -4, -1, 21/2, 5/2, -15/2, 1/2;
    5, 8, 3, 5, 5/2, -7/6, -1, 2/3, 4, -1, -3, 0, 9, 2, -9/2, -1/2;
    2, 8, 2, 2, 2, -2/3, -1, -1/3, 2, 0, -2, -2, 6, 2, -3, 1;
    0, 2, 2, 2, 0, 0, 0, 0, 0, 0, -1, -1, 3, 1, -3, 1;
    2, 3, 2, 3, 1/2, -1/2, 0, 1/3, 3/2, -1/2, -3/2, -1/2, 9/2, 3/2, -3, 0;
    2, 2, 0, 2, 1, -1/3, 0, 0, 2, 0, 0, 0, 3, 1, 0, 0]

/-- An inverse of `g34b_Rlitᵀ`. -/
def g34b_Blit : Matrix (Fin 16) (Fin 16) ℚ :=
  !![0, 0, 0, 0, 1, 3, 0, 0, 0, -2, 1, -1, 0, 0, -1/3, -1;
    -1/2, 0, 0, 0, 1/2, 3/2, 0, 0, 1/2, -3/2, 1/2, -1/2, 0, 0, -1/6, -1/2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1/3, 1, 1/3, 1;
    1, 0, 0, 0, -1, -3, 0, -6, -2, 0, 0, 2, 2/3, 0, 0, 0;
    -1, 0, 0, -1, 2, 0, 3, -3, 1, -3, 0, 2, -1/3, 1, -1, 1;
    -1/2, 0, 1/2, 0, -1/2, 3/2, -1, 3, 1, 0, 1, -2, 1/3, -1, 1/3, -1;
    1, 0, 0, 2, -2, 0, -4, 6, -1, 5, 0, -4, 0, -2, 4/3, -2;
    -1/2, 0, 0, 0, 1, 0, 3/2, -3/2, 0, -2, -1/2, 1/2, 0, 0, 1/6, 1/2;
    0, 1, 0, 0, -4, 6, -3, 9, 4, 4, 2, -4, -2/3, -2, -2/3, -2;
    2, -2, 0, 0, 5, -9, 2, -18, -8, -4, -4, 8, 1, 5, 1, 3;
    -1, 1, 0, 0, -3, 3, -1, 9, 4, 2, 2, -4, -1/3, -3, -1/3, -1;
    0, 0, 0, 0, 0, 0, -1, 3, 0, 2, 0, 0, 0, 0, 0, 0;
    -1/2, 0, 0, 0, 3/2, -3/2, 3/2, -3/2, -1/2, -3/2, 0, 0, 0, 0, 0, 0;
    -1/2, 0, 0, 0, -1, 0, -3/2, 15/2, 1, 3, 3/2, -5/2, 2/3, -2, 0, 0;
    1, 0, 0, 0, 0, 0, 2, -6, -1, -1, -2, 2, -2/3, 2, 0, 0;
    -1/2, 0, 0, 0, 0, 0, 1/2, 3/2, 1, 0, 1, -1, 1/3, -1, 0, 0]

theorem g34b_Rlit_mul_aux : g34b_Rlitᵀ * g34b_Blit = 1 := by
  decide +kernel

theorem g34b_coord_N_0_aux : g34b_coord (g34b_N 0) = g34b_Rlit 0 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_1_aux : g34b_coord (g34b_N 1) = g34b_Rlit 1 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_2_aux : g34b_coord (g34b_N 2) = g34b_Rlit 2 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_coord_N_3_aux : g34b_coord (g34b_N 3) = g34b_Rlit 3 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_coord_N_4_aux : g34b_coord (g34b_N 4) = g34b_Rlit 4 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux]
  norm_num

theorem g34b_coord_N_5_aux : g34b_coord (g34b_N 5) = g34b_Rlit 5 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux]

theorem g34b_coord_N_6_aux : g34b_coord (g34b_N 6) = g34b_Rlit 6 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux]
  norm_num

theorem g34b_coord_N_8_aux : g34b_coord (g34b_N 8) = g34b_Rlit 7 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_9_aux : g34b_coord (g34b_N 9) = g34b_Rlit 8 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_coord_N_10_aux : g34b_coord (g34b_N 10) = g34b_Rlit 9 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_11_aux : g34b_coord (g34b_N 11) = g34b_Rlit 10 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_12_aux : g34b_coord (g34b_N 12) = g34b_Rlit 11 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_13_aux : g34b_coord (g34b_N 13) = g34b_Rlit 12 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_14_aux : g34b_coord (g34b_N 14) = g34b_Rlit 13 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux] <;>
    norm_num

theorem g34b_coord_N_15_aux : g34b_coord (g34b_N 15) = g34b_Rlit 14 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_16_aux : g34b_coord (g34b_N 16) = g34b_Rlit 15 := by
  funext k
  fin_cases k <;>
    simp [g34b_coord, g34b_N, g34b_X, g34b_Rlit, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem g34b_coord_N_aux (i : Fin 16) : g34b_coord (g34b_N (Fin.succAbove 7 i)) = g34b_Rlit i := by
  fin_cases i
  · exact g34b_coord_N_0_aux
  · exact g34b_coord_N_1_aux
  · exact g34b_coord_N_2_aux
  · exact g34b_coord_N_3_aux
  · exact g34b_coord_N_4_aux
  · exact g34b_coord_N_5_aux
  · exact g34b_coord_N_6_aux
  · exact g34b_coord_N_8_aux
  · exact g34b_coord_N_9_aux
  · exact g34b_coord_N_10_aux
  · exact g34b_coord_N_11_aux
  · exact g34b_coord_N_12_aux
  · exact g34b_coord_N_13_aux
  · exact g34b_coord_N_14_aux
  · exact g34b_coord_N_15_aux
  · exact g34b_coord_N_16_aux


theorem g34b_X_rel_aux : g34b_X 7 = (4 : ℚ) • g34b_X 6 - (2 : ℚ) • g34b_X 4 := by
  ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [g34b_X, g34b_ω_eq_aux, QuadraticAlgebra.norm_def] <;> norm_num

theorem g34b_N_rel_aux : g34b_N 7 = (4 : ℚ) • g34b_N 6 - (2 : ℚ) • g34b_N 4 := by
  simp only [g34b_N, g34b_X_rel_aux]
  refine Matrix.ext fun i k => ?_
  rcases i with i | i <;> rcases k with k | k <;> simp

theorem g34b_h4_aux : g34b_H4 g34b_N 4 := by
  unfold g34b_H4
  apply le_antisymm
  · have hle : Submodule.span ℚ (Set.range g34b_N) ≤
        Submodule.span ℚ (Set.range fun i : Fin 16 => g34b_N (Fin.succAbove 7 i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hj : j = 7
      · subst hj
        rw [g34b_N_rel_aux]
        exact Submodule.sub_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨6, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
        exact Submodule.subset_span ⟨i, rfl⟩
    calc _ ≤ Module.finrank ℚ
          (Submodule.span ℚ (Set.range fun i : Fin 16 => g34b_N (Fin.succAbove 7 i))) :=
          Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin 16) := finrank_range_le_card _
      _ = 4 ^ 2 := by simp
  · have htop : Submodule.span ℚ (Set.range g34b_Rlit) = ⊤ := by
      change Submodule.span ℚ (Set.range g34b_Rlitᵀ.col) = ⊤
      rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
      intro v
      refine ⟨g34b_Blit *ᵥ v, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, g34b_Rlit_mul_aux, Matrix.one_mulVec]
    have hmap : Submodule.span ℚ (Set.range g34b_Rlit) ≤
        (Submodule.span ℚ (Set.range g34b_N)).map g34b_coord := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [← g34b_coord_N_aux i]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, rfl⟩)
    calc 4 ^ 2 = Module.finrank ℚ (⊤ : Submodule ℚ (Fin 16 → ℚ)) := by simp
      _ ≤ Module.finrank ℚ ((Submodule.span ℚ (Set.range g34b_N)).map g34b_coord) := by
          rw [← htop]
          exact Submodule.finrank_mono hmap
      _ ≤ _ := Submodule.finrank_map_le _ _

end Certificate

section Generic

variable {m : Type*} [Fintype m] [DecidableEq m] {r n : ℕ}

theorem g34b_h1_of_h2_aux (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂)
    (h2 : g34b_H2 S N n) : g34b_H1 N := by
  intro j k
  apply Matrix.ext
  intro i l
  have hmem : N k *ᵥ (Pi.single l 1) ∈ g34b_I N :=
    Submodule.mem_iSup_of_mem k ⟨Pi.single l 1, rfl⟩
  have hz := congrFun (h2.kill j _ hmem) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hz
  simpa using hz

omit [DecidableEq m] in
theorem g34b_cone_mulVec_aux (N : Fin r → Matrix m m 𝕂) (a : Fin r → ℚ) (x : m → 𝕂) :
    (∑ j, (a j : 𝕂) • N j) *ᵥ x = ∑ j, (a j : 𝕂) • (N j *ᵥ x) := by
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]

theorem g34b_cone_ker_aux (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂)
    (h2 : g34b_H2 S N n) (h3 : g34b_H3 S N) (a : Fin r → ℚ) (ha : ∀ j, 0 < a j) :
    LinearMap.ker (Matrix.toLin' (∑ j, (a j : 𝕂) • N j)) = g34b_I N := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    by_contra hxI
    obtain ⟨σ, -, hpos, hdef⟩ := h3.sign
    have hsum : star x ⬝ᵥ (S *ᵥ ((∑ j, (a j : 𝕂) • N j) *ᵥ x)) =
        ∑ j, (a j : 𝕂) * g34b_beta S (N j) x x := by
      rw [g34b_cone_mulVec_aux, Matrix.mulVec_sum, dotProduct_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, dotProduct_smul, g34b_beta, ← Matrix.mulVec_mulVec, smul_eq_mul]
    rw [hx, mulVec_zero, dotProduct_zero] at hsum
    have hre : ∑ j, a j * (σ * (g34b_beta S (N j) x x).re) = 0 := by
      have h : σ * (∑ j, (a j : 𝕂) * g34b_beta S (N j) x x).re = 0 := by
        rw [← hsum]
        simp
      refine Eq.trans ?_ h
      rw [g34b_re_sum_aux, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Rat.smul_def, QuadraticAlgebra.re_smul, smul_eq_mul]
      ring
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (ha j).le (hpos j x))).1 hre
    have hz : ∑ j, σ * (g34b_beta S (N j) x x).re = 0 :=
      Finset.sum_eq_zero fun j hj =>
        (mul_eq_zero.1 (hzero j hj)).resolve_left (ha j).ne'
    have h := hdef x hxI
    rw [g34b_re_sum_aux, Finset.mul_sum, hz] at h
    exact lt_irrefl _ h
  · intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, g34b_cone_mulVec_aux]
    exact Finset.sum_eq_zero fun j _ => by rw [h2.kill j x hx, smul_zero]

theorem g34b_cone_range_aux (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂)
    (h2 : g34b_H2 S N n) (h3 : g34b_H3 S N) (hm : Fintype.card m = 2 * n)
    (a : Fin r → ℚ) (ha : ∀ j, 0 < a j) :
    LinearMap.range (Matrix.toLin' (∑ j, (a j : 𝕂) • N j)) = g34b_I N := by
  have hle : LinearMap.range (Matrix.toLin' (∑ j, (a j : 𝕂) • N j)) ≤ g34b_I N := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.toLin'_apply, g34b_cone_mulVec_aux]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j ⟨x, rfl⟩)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (∑ j, (a j : 𝕂) • N j))
  rw [g34b_cone_ker_aux S N h2 h3 a ha, h2.finrank_eq, Module.finrank_fintype_fun_eq_card,
    hm] at hrn
  rw [h2.finrank_eq]
  omega

theorem g34b_range_map_aux (ι : 𝕂 →+* ℂ) (A : Matrix m m 𝕂) :
    LinearMap.range (Matrix.toLin' (A.map ι)) =
      g34b_complexify ι (LinearMap.range (Matrix.toLin' A)) := by
  apply le_antisymm
  · change LinearMap.range (A.map ι).mulVecLin ≤ _
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨A *ᵥ Pi.single i 1, ⟨Pi.single i 1, rfl⟩, ?_⟩
    funext k
    rw [Matrix.mulVec_single_one]
    simp [Matrix.col]
  · rw [g34b_complexify, Submodule.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨fun i => ι (x i), ?_⟩
    funext k
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (RingHom.map_mulVec ι A x k).symm

theorem g34b_finrank_complexify_aux (ι : 𝕂 →+* ℂ) (U : Submodule 𝕂 (m → 𝕂)) :
    Module.finrank ℂ (g34b_complexify ι U) = Module.finrank 𝕂 U := by
  let _ : Algebra 𝕂 ℂ := ι.toAlgebra
  have : FaithfulSMul 𝕂 ℂ := (faithfulSMul_iff_algebraMap_injective 𝕂 ℂ).2 ι.injective
  let b := Module.finBasis 𝕂 U
  let v : Fin (Module.finrank 𝕂 U) → m → 𝕂 := fun i => (b i : m → 𝕂)
  have hv : LinearIndependent 𝕂 v :=
    (LinearIndependent.map' b.linearIndependent U.subtype (Submodule.ker_subtype U))
  have hv' : LinearIndependent ℂ (fun i => algebraMap 𝕂 ℂ ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.2 hv
  have hspan : g34b_complexify ι U =
      Submodule.span ℂ (Set.range fun i => algebraMap 𝕂 ℂ ∘ v i) := by
    apply le_antisymm
    · rw [g34b_complexify, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • v i := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      have : (fun k => ι (x k)) = ∑ i, ι (b.repr ⟨x, hx⟩ i) • (algebraMap 𝕂 ℂ ∘ v i) := by
        conv_lhs => rw [hx']
        funext k
        simp [Finset.sum_apply, map_sum, RingHom.algebraMap_toAlgebra]
      change (fun k => ι (x k)) ∈ _
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨v i, (b i).2, rfl⟩
  rw [hspan, finrank_span_eq_card hv', Fintype.card_fin]

/-- Each `S N_j` is Hermitian, from the Hermitian clause of (H3). -/
theorem g34b_SN_herm_aux (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂) (h3 : g34b_H3 S N)
    (j : Fin r) :
    (S * N j)ᴴ = S * N j := by
  have key : ∀ (M : Matrix m m 𝕂) (a b : m),
      star (Pi.single a 1 : m → 𝕂) ⬝ᵥ (M *ᵥ Pi.single b 1) = M a b := by
    intro M a b
    rw [Matrix.mulVec_single_one, ← Pi.single_star, star_one, single_one_dotProduct]
    rfl
  refine Matrix.ext fun a b => ?_
  have h := h3.herm j (Pi.single b 1) (Pi.single a 1)
  simp only [g34b_beta, key] at h
  rw [conjTranspose_apply, h]

theorem g34b_star_qsmul_aux (q : ℚ) (z : 𝕂) : star (q • z) = q • star z := by
  ext <;> simp

/-- Every element of the `ℚ`-span of the `N_j` has `S X` Hermitian. -/
theorem g34b_span_herm_aux (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂) (h3 : g34b_H3 S N)
    {X : Matrix m m 𝕂} (hX : X ∈ Submodule.span ℚ (Set.range N)) : (S * X)ᴴ = S * X := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact g34b_SN_herm_aux S N h3 j
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, conjTranspose_add, hx, hy]
  | smul q x _ hx =>
    refine Matrix.ext fun a b => ?_
    have h := congrFun (congrFun hx a) b
    rw [conjTranspose_apply] at h ⊢
    rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.smul_apply, g34b_star_qsmul_aux, h]

/-- If `S X` and `S (√-3 X)` are both Hermitian and `S` is invertible, then `X = 0`. -/
theorem g34b_herm_omega_aux (S : Matrix m m 𝕂) (hdet : S.det ≠ 0) (X : Matrix m m 𝕂)
    (h1 : (S * X)ᴴ = S * X)
    (h2 : (S * ((QuadraticAlgebra.omega : 𝕂) • X))ᴴ = S * ((QuadraticAlgebra.omega : 𝕂) • X)) :
    X = 0 := by
  have hω : star (QuadraticAlgebra.omega : 𝕂) = -QuadraticAlgebra.omega := by
    ext <;> simp
  rw [Matrix.mul_smul, conjTranspose_smul, h1, hω] at h2
  have h3 : (2 * (QuadraticAlgebra.omega : 𝕂)) • (S * X) = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 1 [← h2]
    rw [neg_smul, neg_add_cancel]
  have hne : (2 * (QuadraticAlgebra.omega : 𝕂)) ≠ 0 := by
    intro h
    have := congrArg QuadraticAlgebra.im h
    simp at this
  have hSX : S * X = 0 := (smul_eq_zero.1 h3).resolve_left hne
  have hu : IsUnit S.det := isUnit_iff_ne_zero.2 hdet
  calc X = S⁻¹ * (S * X) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hu, one_mul]
    _ = 0 := by rw [hSX, Matrix.mul_zero]

theorem g34b_indep_K_aux (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂) (hdet : S.det ≠ 0)
    (h3 : g34b_H3 S N) {k : ℕ} (v : Fin k → Matrix m m 𝕂) (hv : LinearIndependent ℚ v)
    (hmem : ∀ i, v i ∈ Submodule.span ℚ (Set.range N)) : LinearIndependent 𝕂 v := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc
  set P := ∑ i, (c i).re • v i with hPdef
  set Q := ∑ i, (c i).im • v i with hQdef
  have hPQ : P + (QuadraticAlgebra.omega : 𝕂) • Q = 0 := by
    rw [← hc, hPdef, hQdef, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ext <;> simp
    ring
  have hPmem : P ∈ Submodule.span ℚ (Set.range N) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  have hQmem : Q ∈ Submodule.span ℚ (Set.range N) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  have hωQ : (QuadraticAlgebra.omega : 𝕂) • Q = -P :=
    eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact hPQ)
  have hQ : Q = 0 := by
    refine g34b_herm_omega_aux S hdet Q (g34b_span_herm_aux S N h3 hQmem) ?_
    rw [hωQ]
    exact g34b_span_herm_aux S N h3 (Submodule.neg_mem _ hPmem)
  have hP : P = 0 := by rw [hQ, smul_zero, add_zero] at hPQ; exact hPQ
  have ha := hv _ hP
  have hb := hv _ hQ
  intro i
  exact QuadraticAlgebra.ext (ha i) (hb i)

omit [DecidableEq m] in
theorem g34b_indep_C_aux (ι : 𝕂 →+* ℂ) {k : ℕ} (v : Fin k → Matrix m m 𝕂)
    (hv : LinearIndependent 𝕂 v) : LinearIndependent ℂ (fun i => (v i).map ι) := by
  let _ : Algebra 𝕂 ℂ := ι.toAlgebra
  have : FaithfulSMul 𝕂 ℂ := (faithfulSMul_iff_algebraMap_injective 𝕂 ℂ).2 ι.injective
  let e : (m → m → 𝕂) ≃ₗ[𝕂] (m × m → 𝕂) := (LinearEquiv.curry 𝕂 𝕂 m m).symm
  have hw : LinearIndependent 𝕂 (fun i => e (v i)) := hv.map' e.toLinearMap e.ker
  have hw' : LinearIndependent ℂ (fun i => algebraMap 𝕂 ℂ ∘ e (v i)) :=
    linearIndependent_algebraMap_comp_iff.2 hw
  exact hw'.map' (LinearEquiv.curry ℂ ℂ m m).toLinearMap (LinearEquiv.ker _)

theorem g34b_map_mem_boundaryAlg_aux (ι : 𝕂 →+* ℂ) (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂)
    (h2 : g34b_H2 S N n) (j : Fin r) :
    (N j).map ι ∈ g34b_boundaryAlg (g34b_complexify ι (g34b_I N)) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have h : (N j).map ι *ᵥ v ∈ LinearMap.range (Matrix.toLin' ((N j).map ι)) := ⟨v, rfl⟩
    rw [g34b_range_map_aux] at h
    exact Submodule.span_mono (Set.image_mono
      (le_iSup (fun j => LinearMap.range (Matrix.toLin' (N j))) j)) h
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      funext k
      have h := RingHom.map_mulVec ι (N j) y k
      rw [h2.kill j y hy] at h
      simpa [Function.comp_def] using h.symm
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx, smul_zero]

omit [Fintype m] [DecidableEq m] in
theorem g34b_map_span_aux (ι : 𝕂 →+* ℂ) (N : Fin r → Matrix m m 𝕂) {X : Matrix m m 𝕂}
    (hX : X ∈ Submodule.span ℚ (Set.range N)) :
    X.map ι ∈ Submodule.span ℂ (Set.range fun j => (N j).map ι) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [Matrix.map_zero _ (map_zero ι)]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.map_add _ (map_add ι)]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx =>
    have : (q • x).map ι = (q : ℂ) • x.map ι := by
      refine Matrix.ext fun a b => ?_
      simp [Rat.smul_def, map_ratCast]
    rw [this]
    exact Submodule.smul_mem _ _ hx

theorem g34b_finrank_boundaryAlg_le_aux (J : Submodule ℂ (m → ℂ)) (hJ : Module.finrank ℂ J = n)
    (hm : Fintype.card m = 2 * n) : Module.finrank ℂ (g34b_boundaryAlg J) ≤ n ^ 2 := by
  let L : g34b_boundaryAlg J →ₗ[ℂ] ((m → ℂ) ⧸ J →ₗ[ℂ] J) :=
    { toFun := fun X => J.liftQ ((Matrix.toLin' X.1).codRestrict J fun v => X.2.1 v)
        fun v hv => by
          rw [LinearMap.mem_ker]
          exact Subtype.ext (X.2.2 v hv)
      map_add' := fun X Y => by
        apply Submodule.linearMap_qext
        refine LinearMap.ext fun v => Subtype.ext ?_
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
          LinearMap.add_apply, Submodule.coe_add]
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c X => by
        apply Submodule.linearMap_qext
        refine LinearMap.ext fun v => Subtype.ext ?_
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
          LinearMap.smul_apply, Submodule.coe_smul, RingHom.id_apply]
        exact Matrix.smul_mulVec _ _ _ }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro X hX
    rw [LinearMap.mem_ker] at hX
    apply Subtype.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have h := congrArg (fun f => ((f (J.mkQ v) : J) : m → ℂ)) hX
    rw [show ((0 : g34b_boundaryAlg J) : Matrix m m ℂ) = 0 from rfl, map_zero]
    exact h
  have hq : Module.finrank ℂ ((m → ℂ) ⧸ J) = n := by
    have := Submodule.finrank_quotient_add_finrank J
    rw [Module.finrank_fintype_fun_eq_card, hm, hJ] at this
    omega
  calc _ ≤ Module.finrank ℂ ((m → ℂ) ⧸ J →ₗ[ℂ] J) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = n ^ 2 := by rw [Module.finrank_linearMap, hq, hJ, sq]

theorem g34b_span_eq_boundaryAlg_aux (ι : 𝕂 →+* ℂ) (S : Matrix m m 𝕂)
    (N : Fin r → Matrix m m 𝕂) (hS : Sᴴ = -S) (hdet : S.det ≠ 0) (h2 : g34b_H2 S N n)
    (h3 : g34b_H3 S N) (h4 : g34b_H4 N n) (hm : Fintype.card m = 2 * n) :
    Submodule.span ℂ (Set.range fun j => (N j).map ι) =
      g34b_boundaryAlg (g34b_complexify ι (g34b_I N)) := by
  clear hS
  have hle : Submodule.span ℂ (Set.range fun j => (N j).map ι) ≤
      g34b_boundaryAlg (g34b_complexify ι (g34b_I N)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact g34b_map_mem_boundaryAlg_aux ι S N h2 j
  have hJ : Module.finrank ℂ (g34b_complexify ι (g34b_I N)) = n := by
    rw [g34b_finrank_complexify_aux, h2.finrank_eq]
  let b := Module.finBasisOfFinrankEq ℚ (Submodule.span ℚ (Set.range N)) h4
  let v : Fin (n ^ 2) → Matrix m m 𝕂 := fun i => (b i : Matrix m m 𝕂)
  have hvQ : LinearIndependent ℚ v :=
    b.linearIndependent.map' (Submodule.span ℚ (Set.range N)).subtype (Submodule.ker_subtype _)
  have hvC := g34b_indep_C_aux ι v (g34b_indep_K_aux S N hdet h3 v hvQ fun i => (b i).2)
  have hlow : n ^ 2 ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun j => (N j).map ι)) := by
    calc n ^ 2 = Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => (v i).map ι)) := by
          rw [finrank_span_eq_card hvC, Fintype.card_fin]
      _ ≤ _ := by
          refine Submodule.finrank_mono ?_
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact g34b_map_span_aux ι N (b i).2
  exact Submodule.eq_of_le_of_finrank_le hle ((g34b_finrank_boundaryAlg_le_aux _ hJ hm).trans hlow)

theorem g34b_boundaryAlg_surj_aux (J F₀ : Submodule ℂ (m → ℂ))
    (hJ : Module.finrank ℂ J = n) (hF : Module.finrank ℂ F₀ = n)
    (hm : Fintype.card m = 2 * n) (hJF : F₀ ⊓ J = ⊥)
    (φ : F₀ →ₗ[ℂ] (m → ℂ) ⧸ F₀) :
    ∃ X ∈ g34b_boundaryAlg J, F₀.mkQ ∘ₗ Matrix.toLin' X ∘ₗ F₀.subtype = φ := by
  have hc : IsCompl J F₀ := by
    rw [Submodule.isCompl_iff_disjoint _ _
      (by rw [Module.finrank_fintype_fun_eq_card, hm, hJ, hF]; omega), disjoint_iff, inf_comm]
    exact hJF
  let πJ := J.projectionOnto F₀ hc
  let πF := F₀.projectionOnto J hc.symm
  let ψ : ((m → ℂ) ⧸ F₀) →ₗ[ℂ] J := F₀.liftQ πJ (by rw [Submodule.ker_projectionOnto])
  have hψ : ∀ w, F₀.mkQ (ψ w : m → ℂ) = w := by
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H v =>
      change F₀.mkQ (πJ v : m → ℂ) = F₀.mkQ v
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have h := Submodule.projection_add_projection_eq_self hc v
      have hmem : F₀.projection J hc.symm v ∈ F₀ := Submodule.projection_apply_mem _ _
      rw [Submodule.projection_apply] at h
      have : (πJ v : m → ℂ) - v = -(F₀.projection J hc.symm v) :=
        eq_neg_of_add_eq_zero_left (by rw [sub_add_eq_add_sub, h, sub_self])
      rw [this]
      exact F₀.neg_mem hmem
  let T : (m → ℂ) →ₗ[ℂ] (m → ℂ) := J.subtype ∘ₗ ψ ∘ₗ φ ∘ₗ πF
  refine ⟨LinearMap.toMatrix' T, ⟨fun v => ?_, fun v hv => ?_⟩, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    exact (ψ (φ (πF v))).2
  · rw [LinearMap.toMatrix'_mulVec]
    have : πF v = 0 := Submodule.projectionOnto_apply_of_mem_right hc.symm hv
    simp [T, this]
  · refine LinearMap.ext fun f => ?_
    have : πF f = f := Submodule.projectionOnto_apply_left hc.symm f
    simp only [LinearMap.comp_apply, Matrix.toLin'_toMatrix', Submodule.subtype_apply, T, this]
    exact hψ _

theorem g34b_tangent_surjective_aux (ι : 𝕂 →+* ℂ) (S : Matrix m m 𝕂)
    (N : Fin r → Matrix m m 𝕂) (hS : Sᴴ = -S) (hdet : S.det ≠ 0) (h2 : g34b_H2 S N n)
    (h3 : g34b_H3 S N) (h4 : g34b_H4 N n) (hm : Fintype.card m = 2 * n)
    (c : Fin r → ℂ) (hc : ∀ j, c j ≠ 0) (F₀ : Submodule ℂ (m → ℂ))
    (hF : Module.finrank ℂ F₀ = n) (hHT : F₀ ⊓ g34b_complexify ι (g34b_I N) = ⊥) :
    Function.Surjective (g34b_tangentMap (fun j => c j • (N j).map ι) F₀) := by
  intro φ
  have hJ : Module.finrank ℂ (g34b_complexify ι (g34b_I N)) = n := by
    rw [g34b_finrank_complexify_aux, h2.finrank_eq]
  obtain ⟨X, hX, hXφ⟩ := g34b_boundaryAlg_surj_aux _ F₀ hJ hF hm hHT φ
  rw [← g34b_span_eq_boundaryAlg_aux ι S N hS hdet h2 h3 h4 hm,
    Submodule.mem_span_range_iff_exists_fun] at hX
  obtain ⟨w, rfl⟩ := hX
  refine ⟨fun j => w j / c j, ?_⟩
  rw [← hXφ]
  refine LinearMap.ext fun f => ?_
  simp [g34b_tangentMap, smul_smul, map_sum,
    LinearMap.sum_apply, div_mul_cancel₀ _ (hc _)]

theorem g34b_rank_cast_aux {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℂ) :
    ((B.rank : ℕ) : Cardinal) = (Matrix.toLin' B).rank := by
  rw [Matrix.rank, LinearMap.rank, Module.finrank_eq_rank]
  rfl

theorem g34b_rank_eventually_aux {p q : ℕ} (A : ℕ → Matrix (Fin p) (Fin q) ℂ)
    (A₀ : Matrix (Fin p) (Fin q) ℂ) (h : Tendsto A atTop (𝓝 A₀)) :
    ∀ᶠ k in atTop, A₀.rank ≤ (A k).rank := by
  let Φ : Matrix (Fin p) (Fin q) ℂ →ₗ[ℂ] ((Fin q → ℂ) →L[ℂ] (Fin p → ℂ)) :=
    (LinearMap.toContinuousLinearMap :
      ((Fin q → ℂ) →ₗ[ℂ] (Fin p → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ Matrix.toLin'.toLinearMap
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  have hopen := (isOpen_setOfPred_nat_le_rank (𝕜 := ℂ) (E := Fin q → ℂ) (F := Fin p → ℂ)
    A₀.rank).preimage hΦ
  have hmem : A₀ ∈ Φ ⁻¹' {f | (A₀.rank : Cardinal) ≤ (f : (Fin q → ℂ) →ₗ[ℂ] Fin p → ℂ).rank} := by
    change (A₀.rank : Cardinal) ≤ (Matrix.toLin' A₀).rank
    rw [g34b_rank_cast_aux]
  filter_upwards [h (hopen.mem_nhds hmem)] with k hk
  change (A₀.rank : Cardinal) ≤ (Matrix.toLin' (A k)).rank at hk
  rw [← g34b_rank_cast_aux] at hk
  exact_mod_cast hk

theorem g34b_open_image_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {d : ℕ} (f : E → Fin d → ℂ) (V : Set E) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (x : E) (hx : x ∈ V)
    (hrank : Module.finrank ℂ (LinearMap.range (fderiv ℂ f x : E →ₗ[ℂ] Fin d → ℂ)) = d) :
    ∃ U : Set (Fin d → ℂ), IsOpen U ∧ f x ∈ U ∧ U ⊆ f '' V := by
  have hrange : LinearMap.range (fderiv ℂ f x : E →ₗ[ℂ] Fin d → ℂ) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (hrank.trans (by simp))
  have himage : f '' V ∈ 𝓝 (f x) := by
    rw [← (hf x hx).hasStrictFDerivAt.map_nhds_eq_of_surj hrange]
    exact Filter.image_mem_map (hV.mem_nhds hx)
  obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp himage
  exact ⟨U, hU, hxU, hUV⟩

theorem g34b_toBlocks₁₁_eq_zero_aux {n : ℕ} (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕂)
    (hiso : ∀ x ∈ Submodule.span 𝕂
        (Set.range fun i : Fin n => (Pi.single (Sum.inl i) 1 : Fin n ⊕ Fin n → 𝕂)),
      ∀ y ∈ Submodule.span 𝕂
        (Set.range fun i : Fin n => (Pi.single (Sum.inl i) 1 : Fin n ⊕ Fin n → 𝕂)),
      star x ⬝ᵥ (G *ᵥ y) = 0) :
    G.toBlocks₁₁ = 0 := by
  refine Matrix.ext fun i j => ?_
  have h := hiso _ (Submodule.subset_span ⟨i, rfl⟩) _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [Matrix.mulVec_single_one] at h
  simpa [toBlocks₁₁, Pi.single_star, Matrix.col] using h

theorem g34b_det_isotropic_aux {n : ℕ} (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕂)
    (hG : G.IsHermitian) (h₀ : G.toBlocks₁₁ = 0) :
    G.det = (-1) ^ n * (G.toBlocks₁₂.det * star G.toBlocks₁₂.det) := by
  have h21 : G.toBlocks₂₁ = G.toBlocks₁₂ᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [toBlocks₂₁, toBlocks₁₂, conjTranspose_apply, of_apply]
    exact (hG.apply _ _).symm
  conv_lhs => rw [← fromBlocks_toBlocks G, h₀, h21]
  rw [g34b_det_fromBlocks_zero₁₁_aux, det_conjTranspose]

end Generic

section Deposited

theorem g34b_hGram_isHermitian_aux : g34b_hGram.IsHermitian := by
  have hω : star (QuadraticAlgebra.omega : 𝕂) = -QuadraticAlgebra.omega := by
    ext <;> simp
  unfold Matrix.IsHermitian
  rw [g34b_hGram, conjTranspose_smul, hω, g34b_S_skew_aux, neg_smul, smul_neg, neg_neg]

/-- `det h = 6561 = 81 · 81`. -/
theorem g34b_hGram_det_aux : g34b_hGram.det = 81 * star 81 := by
  have hω : (QuadraticAlgebra.omega : 𝕂) ^ 8 = 81 := by
    rw [show 8 = 2 * 4 by rfl, pow_mul, QuadraticAlgebra.omega_pow_two_eq_add]
    ext <;> simp <;> norm_num
  rw [g34b_hGram, det_smul, g34b_S_det_aux]
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [show 4 + 4 = 8 by rfl, hω]
  ext <;> simp

theorem g34b_hGram_det_norm_aux : ∃ x : 𝕂, x ≠ 0 ∧ g34b_hGram.det = x * star x :=
  ⟨81, by norm_num, g34b_hGram_det_aux⟩

theorem g34b_sum_Mlog_aux (ι : 𝕂 →+* ℂ) (ε : ℤ) (c : Fin 17 → ℕ) :
    ∑ j, g34b_Mlog ι ε c j = (ε : ℂ) • (∑ j, ((c j : ℚ) : 𝕂) • g34b_N j).map ι := by
  refine Matrix.ext fun i k => ?_
  simp [g34b_Mlog, Matrix.sum_apply, Finset.mul_sum, map_sum, mul_assoc]

theorem g34b_cone_range_deposited_aux (ι : 𝕂 →+* ℂ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (c : Fin 17 → ℕ) (hc : ∀ j, 0 < c j) :
    LinearMap.range (Matrix.toLin' (∑ j, g34b_Mlog ι ε c j)) =
      g34b_complexify ι (g34b_I g34b_N) := by
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  rw [g34b_sum_Mlog_aux, map_smul, LinearMap.range_smul _ _ hε0, g34b_range_map_aux,
    g34b_cone_range_aux g34b_S g34b_N g34b_h2_aux g34b_h3_aux (by simp) _
      (fun j => by exact_mod_cast hc j)]

theorem g34b_tangent_surjective_deposited_aux (ι : 𝕂 →+* ℂ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (c : Fin 17 → ℕ) (hc : ∀ j, 0 < c j) (F₀ : Submodule ℂ (Fin 4 ⊕ Fin 4 → ℂ))
    (hF : Module.finrank ℂ F₀ = 4)
    (hHT : F₀ ⊓ LinearMap.range (Matrix.toLin' (∑ j, g34b_Mlog ι ε c j)) = ⊥) :
    Function.Surjective (g34b_tangentMap (g34b_Mlog ι ε c) F₀) := by
  rw [g34b_cone_range_deposited_aux ι ε hε c hc] at hHT
  have hne : ∀ j, (((ε * c j : ℤ)) : ℂ) ≠ 0 := fun j => by
    refine Int.cast_ne_zero.2 (mul_ne_zero ?_ ?_)
    · rcases hε with rfl | rfl <;> norm_num
    · exact_mod_cast (hc j).ne'
  exact g34b_tangent_surjective_aux ι g34b_S g34b_N g34b_S_skew_aux
    (by rw [g34b_S_det_aux]; norm_num) g34b_h2_aux g34b_h3_aux g34b_h4_aux (by simp)
    (fun j => ((ε * c j : ℤ) : ℂ)) hne F₀ hF hHT

end Deposited

section Discriminant

theorem g34b_norm_class_aux (q c : ℚ) (hq : q ≠ 0) (hc : c ≠ 0) (x : 𝕂)
    (h : algebraMap ℚ 𝕂 q = (c : 𝕂) ^ 8 * (x * star x)) :
    ((Units.mk0 q hq : ℚˣ) : ℚˣ ⧸ normSubgroup 𝕂) = 1 := by
  rw [QuotientGroup.eq_one_iff, mem_normSubgroup_iff]
  refine ⟨(c : 𝕂) ^ 4 * x, ?_⟩
  apply (algebraMap ℚ 𝕂).injective
  rw [Units.val_mk0, h, QuadraticAlgebra.algebraMap_norm_eq_mul_star, star_mul, star_pow]
  have hc' : star (c : 𝕂) = c := by
    rw [← eq_ratCast (algebraMap ℚ 𝕂)]
    ext <;> simp
  rw [hc']
  ring

theorem g34b_fiber_disc_aux {S : Type} (fiber : S → wtr_Variety 4)
    (fiber_polarized : ∀ s, wtr_PolarizedWeil 4 (fiber s))
    (hpar : ∀ s, g34b_ParabolicPolarization (fiber_polarized s)) :
    ∀ s, wtr_disc (fiber_polarized s) = 1 := by
  intro s
  let hT := HodgeLean.Adapters.torusCohomology_cupProductOf (fiber s).X
  let _ := hT.finite
  rcases hpar s with ⟨c, hc, e, hgram⟩
  let E := polarizationForm hT (fiber_polarized s).nondegenerate
  let J : {J : HQ (fiber s).X 1 →ₗ[ℚ] HQ (fiber s).X 1 //
      J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
    ⟨(fiber s).W.J, (fiber s).W.J_sq⟩
  have hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y) :=
    (HodgeLean.Foundations.Symplectic.isRosatiSkew_iff_dualForm
      (fiber_polarized s).nondegenerate (fiber s).W.J).1 (fiber_polarized s).rosati
  let H := HodgeLean.Foundations.WeilHermitian.weilHermitian E J hskew
  have hsymm := HodgeLean.Foundations.WeilHermitian.isSymm_weilHermitian
    (J := J) (hskew := hskew)
    (isAlt_polarizationForm hT (fiber_polarized s).nondegenerate)
  have hnd := HodgeLean.Foundations.WeilHermitian.nondegenerate_weilHermitian
    (J := J) (hskew := hskew)
    (nondegenerate_polarizationForm hT (fiber_polarized s).nondegenerate)
  change LinearMap.toMatrix₂ e e H = _ ∨ LinearMap.toMatrix₂ e e H = _ at hgram
  change detClass H hsymm hnd = 1
  rw [detClass_eq hsymm hnd e]
  have hdet : ∃ y : 𝕂, gramDet H e = (c : 𝕂) ^ 8 * (y * star y) := by
    rcases hgram with h | h
    · refine ⟨81, ?_⟩
      rw [gramDet, h, det_smul, g34b_hGram_det_aux]
      simp
    · refine ⟨star 81, ?_⟩
      rw [gramDet, h, det_smul, show g34b_hGram.map star =
        (starRingEnd 𝕂).mapMatrix g34b_hGram from rfl, ← RingHom.map_det, g34b_hGram_det_aux]
      simp [starRingEnd_apply]
  obtain ⟨y, hy⟩ := hdet
  exact g34b_norm_class_aux _ c _ hc y (by rw [algebraMap_gramDetℚ hsymm e, hy])

end Discriminant

section Bridge

theorem g34b_rank_toMatrix'_aux {p q : ℕ} (f : (Fin q → ℂ) →ₗ[ℂ] Fin p → ℂ) :
    (LinearMap.toMatrix' f).rank = Module.finrank ℂ (LinearMap.range f) := by
  change Module.finrank ℂ (LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' f))) = _
  rw [Matrix.toLin'_toMatrix']

theorem g34b_period_rank_aux (F : wtr_UniversalFamily 4 1) {S : Type}
    (fiber : S → wtr_Variety 4) (Φ : g34b_BoundaryPeriodMap F fiber) :
    ∃ t ∈ Φ.V, Module.finrank ℂ
      (LinearMap.range (fderiv ℂ Φ.period t : (Fin 17 → ℂ) →ₗ[ℂ] Fin (4 ^ 2) → ℂ)) = 4 ^ 2 := by
  have hsurj := g34b_tangent_surjective_deposited_aux Φ.ι Φ.ε Φ.ε_sign Φ.c Φ.c_pos Φ.F₀
    Φ.F₀_finrank Φ.hodgeTate
  have hA₀ : (LinearMap.toMatrix'
      (Φ.chart.toLinearMap ∘ₗ g34b_tangentMap (g34b_Mlog Φ.ι Φ.ε Φ.c) Φ.F₀)).rank = 4 ^ 2 := by
    have hs : Function.Surjective
        (Φ.chart.toLinearMap ∘ₗ g34b_tangentMap (g34b_Mlog Φ.ι Φ.ε Φ.c) Φ.F₀) := by
      rw [LinearMap.coe_comp, LinearEquiv.coe_coe]
      exact Φ.chart.surjective.comp hsurj
    rw [g34b_rank_toMatrix'_aux, LinearMap.range_eq_top.2 hs, finrank_top, Module.finrank_fin_fun]
  obtain ⟨k, hk⟩ := (g34b_rank_eventually_aux _ _ Φ.limit).exists
  rw [hA₀] at hk
  refine ⟨Φ.pt k, Φ.pt_mem k, le_antisymm ?_ ?_⟩
  · rw [← g34b_rank_toMatrix'_aux]
    exact (Matrix.rank_le_card_height _).trans (by simp)
  · rw [← g34b_rank_toMatrix'_aux]
    exact hk.trans ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))

theorem g34b_dominant_aux (F : wtr_UniversalFamily 4 1) {S : Type}
    (fiber : S → wtr_Variety 4) (Φ : g34b_BoundaryPeriodMap F fiber) :
    ∃ U : Set (wtr_Domain 4), IsOpen U ∧ U.Nonempty ∧
      ∀ m ∈ U, ∃ s, wtr_KIsog (fiber s) (F.univ m) := by
  obtain ⟨t, ht, hrank⟩ := g34b_period_rank_aux F fiber Φ
  obtain ⟨U', hU', htU', hU'V⟩ :=
    g34b_open_image_aux Φ.period Φ.V Φ.isOpen_V Φ.analytic t ht hrank
  refine ⟨Subtype.val ⁻¹' U', hU'.preimage continuous_subtype_val,
    ⟨⟨Φ.period t, Φ.mapsTo ht⟩, htU'⟩, ?_⟩
  rintro ⟨z, hz⟩ hzU
  obtain ⟨t', ht', hzt⟩ := hU'V hzU
  obtain ⟨s, hs⟩ := Φ.isog t' ht'
  refine ⟨s, ?_⟩
  have h : (⟨Φ.period t', Φ.mapsTo ht'⟩ : wtr_Domain 4) = ⟨z, hz⟩ := Subtype.ext hzt
  rwa [h] at hs

theorem g34b_theoremA_of_boundary_aux (F : wtr_UniversalFamily 4 1) {S : Type}
    (fiber : S → wtr_Variety 4) (fiber_polarized : ∀ s, wtr_PolarizedWeil 4 (fiber s))
    (hpar : ∀ s, g34b_ParabolicPolarization (fiber_polarized s))
    (Φ : g34b_BoundaryPeriodMap F fiber) (fiber_alg : ∀ s, wtr_WeilAlg (fiber s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := by
  have := wtr_domain_connectedSpace 4
  exact wtr_g34A_of_transfer (wtr_transferFields F
    ⟨S, fiber, fiber_polarized, g34b_fiber_disc_aux fiber fiber_polarized hpar, fiber_alg,
      g34b_dominant_aux F fiber Φ, spread, transport⟩) A

end Bridge

end HodgeLean.Papers
