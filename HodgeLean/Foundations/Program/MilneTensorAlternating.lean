import HodgeLean.Foundations.Program.MilneTensorNormal

noncomputable section
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

def m1b_matrix_bivector (n : ℕ) (C : Matrix (Fin n) (Fin n) ℂ) :
    ⋀[ℂ]^2 (Fin n → ℂ) :=
  (2 : ℂ)⁻¹ • ∑ i, exteriorPower.ιMulti ℂ 2
    ![Pi.single i 1, fun j => C j i]

theorem m1b_dual_apply_coordinates (n : ℕ) (φ : Module.Dual ℂ (Fin n → ℂ))
    (x : Fin n → ℂ) : φ x = ∑ i, x i * φ (Pi.single i 1) := by
  have h := congrArg φ ((Pi.basisFun ℂ (Fin n)).sum_repr x)
  simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply,
    smul_eq_mul] using h.symm

theorem m1b_contract_matrix_bivector (n : ℕ) (C : Matrix (Fin n) (Fin n) ℂ)
    (hs : C.transpose = -C) (φ : Module.Dual ℂ (Fin n → ℂ)) :
    contract (m1b_matrix_bivector n C) φ =
      C.mulVec (fun i => φ (Pi.single i 1)) := by
  ext j
  have hc (i j) : C i j = -C j i := congrFun (congrFun hs j) i
  have hφ (i) := m1b_dual_apply_coordinates n φ (fun j => C j i)
  simp only [m1b_matrix_bivector, map_smul, map_sum, LinearMap.smul_apply,
    LinearMap.sum_apply, contract_ιMulti, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.smul_apply, Finset.sum_apply, Pi.sub_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  change (2 : ℂ)⁻¹ * (∑ i, (φ (Pi.single i 1) * C j i -
    φ (fun k => C k i) * (Pi.single i 1 : Fin n → ℂ) j)) =
      ∑ i, C j i * φ (Pi.single i 1)
  have hsum : (∑ i, φ (fun k => C k i) * (Pi.single i 1 : Fin n → ℂ) j) =
      φ (fun k => C k j) := by simp [Pi.single_apply]
  have hcol : φ (fun i => C i j) = -(∑ i, C j i * φ (Pi.single i 1)) := by
    rw [hφ, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc i j]
    ring
  have hcomm : (∑ i, φ (Pi.single i 1) * C j i) =
      ∑ i, C j i * φ (Pi.single i 1) :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [Finset.sum_sub_distrib, hsum, hcol, hcomm]
  ring

theorem m1b_matrix_bivector_nondegenerate (n : ℕ)
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C) (hs : C.transpose = -C) :
    IsNondegenerate (m1b_matrix_bivector n C) := by
  let e := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  have he : contract (m1b_matrix_bivector n C) = C.toLin'.comp e.toLinearMap := by
    apply LinearMap.ext
    intro φ
    rw [m1b_contract_matrix_bivector n C hs]
    change C.mulVec (fun i => φ (Pi.single i 1)) = C.mulVec (e φ)
    congr 1
    funext i
    simpa only [e, Pi.basisFun_apply] using
      ((Pi.basisFun ℂ (Fin n)).dualBasis_equivFun φ i).symm
  change Function.Bijective _
  rw [he]
  exact ((Module.End.isUnit_iff _).mp (Matrix.isUnit_toLin'_iff.mpr hC)).comp e.bijective

theorem m1b_alternating_basis (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (hs : B.transpose = -B) :
    ∃ (k : ℕ) (b : Module.Basis (Fin k ⊕ Fin k) ℂ (Fin n → ℂ)),
      n = 2 * k ∧ ∀ i j, B.toBilin' (b i) (b j) = m1b_J k i j := by
  classical
  obtain ⟨U, rfl⟩ := hB
  let C : Matrix (Fin n) (Fin n) ℂ := ↑U⁻¹
  have hC : C.transpose = -C := by
    have ht := congrArg Matrix.transpose U.val_inv
    rw [Matrix.transpose_mul, hs, Matrix.mul_neg, Matrix.transpose_one] at ht
    have hh : C.transpose * U.val = -1 := neg_eq_iff_eq_neg.mp ht
    calc C.transpose = C.transpose * (U.val * C) := by
           rw [show U.val * C = 1 from U.val_inv, mul_one]
         _ = (C.transpose * U.val) * C := (mul_assoc _ _ _).symm
         _ = -C := by rw [hh, neg_one_mul]
  let ω := m1b_matrix_bivector n C
  obtain ⟨k, b, hk, hb⟩ := exists_basis_sympVec_of_isNondegenerate
    (m1b_matrix_bivector_nondegenerate n C U⁻¹.isUnit hC)
  have hcon (φ : Module.Dual ℂ (Fin n → ℂ)) :
      U.val.mulVec (contract ω φ) = fun i => φ (Pi.single i 1) := by
    rw [m1b_contract_matrix_bivector n C hC, Matrix.mulVec_mulVec,
      show U.val * C = 1 from U.val_inv, Matrix.one_mulVec]
  have hr (j : Fin k) : U.val.mulVec (b (.inr j)) =
      fun i => b.coord (.inl j) (Pi.single i 1) := by
    have h := hcon (b.coord (.inl j))
    change U.val.mulVec (contract (m1b_matrix_bivector n C) _) = _ at h
    rw [hb, contract_sympVec_coord_inl] at h
    exact h
  have hl (j : Fin k) : U.val.mulVec (b (.inl j)) =
      -(fun i => b.coord (.inr j) (Pi.single i 1)) := by
    have h := hcon (b.coord (.inr j))
    change U.val.mulVec (contract (m1b_matrix_bivector n C) _) = _ at h
    rw [hb, contract_sympVec_coord_inr, Matrix.mulVec_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  refine ⟨k, b, ?_, ?_⟩
  · simpa using hk
  · intro i j
    rw [Matrix.toBilin'_apply']
    cases j with
    | inl j =>
      rw [hl, dotProduct_neg]
      have hv := m1b_dual_apply_coordinates n (b.coord (.inr j)) (b i)
      change _ = dotProduct _ _ at hv
      rw [← hv]
      cases i <;> simp [m1b_J, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    | inr j =>
      rw [hr]
      have hv := m1b_dual_apply_coordinates n (b.coord (.inl j)) (b i)
      change _ = dotProduct _ _ at hv
      rw [← hv]
      cases i <;> simp [m1b_J, Matrix.one_apply, Finsupp.single_apply, eq_comm]

end HodgeLean.Foundations.Program
