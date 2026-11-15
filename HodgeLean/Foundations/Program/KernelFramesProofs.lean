module

public import HodgeLean.Foundations.Program.KernelFramesBase

/-! Rational base-system ranks, nonzero blocks and kernel bases.
HC no distance; AV milestone no distance. -/
@[expose] public section

noncomputable section
namespace HodgeLean.Foundations.Program
open Matrix

theorem b65k_frame_of_block {m n p : ℕ} (S : Matrix (Fin m) (Fin n) ℚ)
    (free : Fin 3 → Fin n) (piv : Fin p → Fin n) (rows : Fin p → Fin m)
    (hbij : Function.Bijective (Sum.elim piv free))
    (hdet : (S.submatrix rows piv).det ≠ 0)
    (K : Matrix (Fin n) (Fin 3) ℚ) (hSK : S * K = 0)
    (hfree : ∀ a f, K (free a) f = if a = f then 1 else 0) :
    LinearIndependent ℚ (fun f : Fin 3 => fun i => K i f) ∧
    Submodule.span ℚ (Set.range (fun f : Fin 3 => fun i => K i f)) =
      LinearMap.ker S.mulVecLin := by
  set e := Equiv.ofBijective _ hbij
  have hcol : ∀ f, S *ᵥ (fun i => K i f) = 0 := by
    intro f; ext r
    have := congrFun (congrFun hSK r) f
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg a
    have := congrFun hg (free a)
    simpa [Finset.sum_apply, hfree] using this
  · rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact hcol f
  · intro v hv
    have hv' : S *ᵥ v = 0 := hv
    set w : Fin n → ℚ := v - ∑ f, v (free f) • fun i => K i f with hw
    have hwk : S *ᵥ w = 0 := by
      simp [hw, Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul, hv', hcol]
    have hwf : ∀ a, w (free a) = 0 := by
      intro a; simp [hw, Finset.sum_apply, hfree]
    have hwp : (fun j => w (piv j)) = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      ext i
      have := congrFun hwk (rows i)
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this ⊢
      rw [← Equiv.sum_comp e, Fintype.sum_sum_type] at this
      simpa [e, hwf] using this
    have hw0 : w = 0 := by
      ext k
      obtain ⟨x, rfl⟩ := e.surjective k
      rcases x with j | a
      · exact congrFun hwp j
      · exact hwf a
    have hv_eq : v = ∑ f, v (free f) • fun i => K i f := by
      rw [hw, sub_eq_zero] at hw0; exact hw0
    rw [hv_eq]
    exact Submodule.sum_mem _ fun f _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)

theorem b65k_rank_of_frame {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℚ)
    (K : Matrix (Fin n) (Fin 3) ℚ)
    (h : LinearIndependent ℚ (fun f : Fin 3 => fun i => K i f) ∧
      Submodule.span ℚ (Set.range (fun f : Fin 3 => fun i => K i f)) =
        LinearMap.ker S.mulVecLin) :
    S.rank + 3 = n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker S.mulVecLin
  have h2 := finrank_span_eq_card h.1
  rw [h.2] at h2
  rw [Module.finrank_fin_fun] at h1
  rw [Fintype.card_fin] at h2
  rw [Matrix.rank]
  omega

theorem b65k_r_block_aux :
    b65k_rBlock.det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse b65k_rBlock_mul_inv

theorem b65k_r_basis_aux :
    LinearIndependent ℚ (fun f : Fin 3 => fun i => b65k_rKernel i f) ∧
    Submodule.span ℚ (Set.range (fun f : Fin 3 => fun i => b65k_rKernel i f)) =
      LinearMap.ker b65k_rSystem.mulVecLin ∧
    (∀ a f : Fin 3, b65k_rKernel (b65k_rFree a) f = if a = f then 1 else 0) := by
  have hfree : ∀ a f : Fin 3, b65k_rKernel (b65k_rFree a) f = if a = f then 1 else 0 := by
    rw [b65k_rKernel_eq]
    simp only [Matrix.of_apply]
    decide +kernel
  have hSK : b65k_rSystem * b65k_rKernel = 0 := by
    rw [b65k_rKernel_eq]
    exact b65k_rSystem_mul_kernelLit
  exact ⟨(b65k_frame_of_block b65k_rSystem b65k_rFree b65k_rPivot b65k_rRows b65k_r_bijective
    b65k_r_block_aux b65k_rKernel hSK hfree).1,
    (b65k_frame_of_block b65k_rSystem b65k_rFree b65k_rPivot b65k_rRows b65k_r_bijective
    b65k_r_block_aux b65k_rKernel hSK hfree).2, hfree⟩

theorem b65k_r_rank_aux :
    b65k_rSystem.rank = 33 := by
  have h := b65k_rank_of_frame b65k_rSystem b65k_rKernel
    ⟨b65k_r_basis_aux.1, b65k_r_basis_aux.2.1⟩
  omega

theorem b65k_q_block_aux :
    b65k_qBlock.det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse b65k_qBlock_mul_inv

theorem b65k_q_basis_aux :
    LinearIndependent ℚ (fun f : Fin 3 => fun i => b65k_qKernel i f) ∧
    Submodule.span ℚ (Set.range (fun f : Fin 3 => fun i => b65k_qKernel i f)) =
      LinearMap.ker b65k_qSystem.mulVecLin ∧
    (∀ a f : Fin 3, b65k_qKernel (b65k_qFree a) f = if a = f then 1 else 0) := by
  have hfree : ∀ a f : Fin 3, b65k_qKernel (b65k_qFree a) f = if a = f then 1 else 0 := by
    rw [b65k_qKernel_eq]
    simp only [Matrix.of_apply]
    decide +kernel
  have hSK : b65k_qSystem * b65k_qKernel = 0 := by
    rw [b65k_qKernel_eq]
    exact b65k_qSystem_mul_kernelLit
  exact ⟨(b65k_frame_of_block b65k_qSystem b65k_qFree b65k_qPivot b65k_qRows b65k_q_bijective
    b65k_q_block_aux b65k_qKernel hSK hfree).1,
    (b65k_frame_of_block b65k_qSystem b65k_qFree b65k_qPivot b65k_qRows b65k_q_bijective
    b65k_q_block_aux b65k_qKernel hSK hfree).2, hfree⟩

theorem b65k_q_rank_aux :
    b65k_qSystem.rank = 45 := by
  have h := b65k_rank_of_frame b65k_qSystem b65k_qKernel
    ⟨b65k_q_basis_aux.1, b65k_q_basis_aux.2.1⟩
  omega

theorem b65k_productPoly (a b : Fin 3) :
    b65k_baseProduct a b = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly a b) := by
  match a, b with
  | 0, 0 => exact b65k_productPoly_0_0
  | 0, 1 => exact b65k_productPoly_0_1
  | 0, 2 => exact b65k_productPoly_0_2
  | 1, 0 => exact b65k_productPoly_1_0
  | 1, 1 => exact b65k_productPoly_1_1
  | 1, 2 => exact b65k_productPoly_1_2
  | 2, 0 => exact b65k_productPoly_2_0
  | 2, 1 => exact b65k_productPoly_2_1
  | 2, 2 => exact b65k_productPoly_2_2

theorem b65k_numPoly_coeff (a b : Fin 3) (j : Fin 10) :
    (b65k_numPoly a b).coeff j.val = b65k_numCoeff a b j := by
  rw [b65k_numPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Fin.val_inj]
  simp

theorem b65k_base_numerator_aux :
    ∀ a b : Fin 3, (b65k_baseProduct a b).denom = 1 ∧
      (b65k_baseNumerator a b).natDegree ≤ 9 := by
  intro a b
  refine ⟨by rw [b65k_productPoly, RatFunc.denom_algebraMap], ?_⟩
  rw [b65k_baseNumerator, b65k_productPoly, RatFunc.num_algebraMap, b65k_numPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem b65k_base_coefficients_aux :
    ∀ a b : Fin 3,
      (∑ j : Fin 10, RatFunc.C (b65k_baseMatrix (finProdFinEquiv (a,b)) j) *
        RatFunc.X^j.val) = b65k_baseProduct a b := by
  intro a b
  have h : ∀ j : Fin 10, b65k_baseMatrix (finProdFinEquiv (a,b)) j = b65k_numCoeff a b j := by
    intro j
    simp only [b65k_baseMatrix, Equiv.symm_apply_apply]
    rw [b65k_baseNumerator, b65k_productPoly, RatFunc.num_algebraMap, b65k_numPoly_coeff]
  simp only [h]
  rw [b65k_productPoly, b65k_numPoly]
  simp [map_sum, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

end HodgeLean.Foundations.Program
