import HodgeLean.Foundations.Program.CoverDictionaryKernels
import HodgeLean.Foundations.Program.CoverDictionaryRegular

/-! # B6-5 stage 5d, geometric part: uniqueness of represented vectors and numerators

Rational functions agreeing at infinitely many regular points are equal; on a fibre at the G32
centre the rational vector representing a `G`-map on the regular locus, and the numerator of a
quadratic differential, are therefore unique. Also the product rule for `b66e_productChange` and
linearity of the r- and q-vectors in their coefficients. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- Rational functions with equal values at infinitely many regular points are equal. -/
theorem b65g_ratfunc_eq {f g : RatFunc ℂ} {S : Set ℂ} (hS : S.Infinite)
    (h : ∀ s ∈ S, b65g_reg s f ∧ b65g_reg s g ∧ b65q_eval f s = b65q_eval g s) : f = g := by
  have hP : f.num * g.denom - g.num * f.denom = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ (hS.mono fun s hs ↦ ?_)
    obtain ⟨hf, hg, he⟩ := h s hs
    rw [b65q_eval_eq, b65q_eval_eq, div_eq_div_iff hf hg] at he
    simp only [mem_ofPred_eq, IsRoot, eval_sub, eval_mul, he, sub_self]
  rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f))
      (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero g)), ← map_mul, ← map_mul,
    sub_eq_zero.mp hP]

section Unique
variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c) {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
  (poles : Fin 4 ⊕ Fin 12 → ℂ) (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)
  (hY : ∀ x ∈ b65g_good D t a b poles, IsUnit (Y x).det)
include hab hba hY

omit hY in
/-- A vector of forms `v ⬝ (M(Y) r) ds` on the regular locus determines `r`. -/
theorem b65g_vec_eq_of_rep (M : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (hM : ∀ x ∈ b65g_good D t a b poles, IsUnit (M (Y x)).det)
    (F : (Fin 4 → RatFunc ℂ) → (Fin 4 → ℂ) → TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ)
    (hF : ∀ r v u, F r v u = (v ⬝ᵥ (M (Y u.1) *ᵥ fun j ↦ b65q_eval (r j) (b65g_sFun D t a b u.1))) *
      b65g_ds D t a b u)
    (r r' : Fin 4 → RatFunc ℂ)
    (hreg : ∀ j s, s ∉ Set.range poles → b65g_reg s (r j) ∧ b65g_reg s (r' j))
    (h : ∀ v u, u.1 ∈ b65g_good D t a b poles → F r v u = F r' v u) : r = r' := by
  funext j
  refine b65g_ratfunc_eq (b65g_rich D t hab hba poles) fun s hs ↦ ?_
  obtain ⟨u, hu, rfl, hds⟩ := hs
  have hp := b65g_good_sFun hu
  refine ⟨(hreg j _ hp).1, (hreg j _ hp).2, ?_⟩
  have hv : ∀ v, v ⬝ᵥ (M (Y u.1) *ᵥ fun j ↦ b65q_eval (r j) (b65g_sFun D t a b u.1)) =
      v ⬝ᵥ (M (Y u.1) *ᵥ fun j ↦ b65q_eval (r' j) (b65g_sFun D t a b u.1)) := fun v ↦ by
    have := h v u hu
    rw [hF, hF] at this
    exact mul_right_cancel₀ hds this
  have hvec : (M (Y u.1) *ᵥ fun j ↦ b65q_eval (r j) (b65g_sFun D t a b u.1)) =
      (M (Y u.1) *ᵥ fun j ↦ b65q_eval (r' j) (b65g_sFun D t a b u.1)) := by
    funext i; simpa using hv (Pi.single i 1)
  have hinj := (Matrix.mulVec_injective_iff_isUnit).mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (hM _ hu))
  exact congrFun (hinj hvec) j

/-- The r-vector representing a map is unique. -/
theorem b65g_r_eq_of_rep (r r' : Fin 4 → RatFunc ℂ)
    (hreg : ∀ j s, s ∉ Set.range poles → b65g_reg s (r j) ∧ b65g_reg s (r' j))
    (φ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (h : b65g_rRepresents D t a b poles Y r φ) (h' : b65g_rRepresents D t a b poles Y r' φ) :
    r = r' :=
  b65g_vec_eq_of_rep D t hab hba poles Y (fun Z ↦ Z⁻¹)
    (fun x hx ↦ by rw [Matrix.det_nonsing_inv]; exact (hY x hx).ringInverse)
    (fun r ↦ b65g_rForm D t a b Y r) (fun _ _ _ ↦ rfl) r r' hreg
    fun v u hu ↦ (h v u hu).symm.trans (h' v u hu)

/-- The q-vector representing a map is unique. -/
theorem b65g_q_eq_of_rep (q q' : Fin 4 → RatFunc ℂ)
    (hreg : ∀ j s, s ∉ Set.range poles → b65g_reg s (q j) ∧ b65g_reg s (q' j))
    (ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (h : b65g_qRepresents D t a b poles Y q ψ) (h' : b65g_qRepresents D t a b poles Y q' ψ) :
    q = q' :=
  b65g_vec_eq_of_rep D t hab hba poles Y (fun Z ↦ Zᵀ)
    (fun x hx ↦ by rw [Matrix.det_transpose]; exact hY x hx)
    (fun q ↦ b65g_qForm D t a b Y q) (fun _ _ _ ↦ rfl) q q' hreg
    fun v u hu ↦ (h v u hu).symm.trans (h' v u hu)

end Unique

/-- The numerator of a coefficient row as a polynomial. -/
theorem b65g_numerator_poly (N : Fin 10 → ℂ) :
    (∑ j : Fin 10, RatFunc.C (N j) * RatFunc.X ^ j.val) =
      algebraMap ℂ[X] (RatFunc ℂ) (∑ j : Fin 10, Polynomial.C (N j) * X ^ j.val) := by
  simp [map_sum, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

/-- The coefficients of the numerator polynomial. -/
theorem b65g_numerator_coeff (N : Fin 10 → ℂ) (k : Fin 10) :
    (∑ j : Fin 10, Polynomial.C (N j) * X ^ j.val).coeff k.val = N k := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k (fun j _ hj ↦ ite_eq_right_iff.mpr fun h ↦ absurd (Fin.ext h.symm) hj) (by simp)]
  simp

/-- The numerator of a quadratic differential on the regular locus is unique. -/
theorem b65g_N_eq_of_quadratic {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) {a b : ℂ} (hab : a * b ≠ 0)
    (hba : b - a ≠ 0) (poles : Fin 4 ⊕ Fin 12 → ℂ) (h0 : (0 : ℂ) ∈ Set.range poles)
    (N N' : Fin 10 → ℂ)
    (h : ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t), u.1 ∈ b65g_good D t a b poles →
      b65g_quadratic D t a b poles N u = b65g_quadratic D t a b poles N' u) : N = N' := by
  have hDne : b65q_denominator poles ≠ 0 := Monic.ne_zero (by
    unfold b65q_denominator
    exact monic_X.mul (monic_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _))
  have hD : algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hDne
  have hreg : ∀ (N : Fin 10 → ℂ) (s : ℂ), s ∉ Set.range poles →
      b65g_reg s ((∑ j : Fin 10, RatFunc.C (N j) * RatFunc.X ^ j.val) /
        algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles)) := by
    intro N s hs h1
    rw [b65g_numerator_poly] at h1
    have := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd _ _) h1
    simp only [b65q_denominator, eval_mul, eval_X, eval_prod, eval_sub, eval_C,
      mul_eq_zero, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero] at this
    rcases this with h | ⟨x, hx⟩
    · exact hs (h ▸ h0)
    · exact hs ⟨_, hx.symm⟩
  have hq : (∑ j : Fin 10, RatFunc.C (N j) * RatFunc.X ^ j.val) /
      algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles) =
      (∑ j : Fin 10, RatFunc.C (N' j) * RatFunc.X ^ j.val) /
      algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles) := by
    refine b65g_ratfunc_eq (b65g_rich D t hab hba poles) fun s hs ↦ ?_
    obtain ⟨u, hu, rfl, hds⟩ := hs
    have hp := b65g_good_sFun hu
    refine ⟨hreg N _ hp, hreg N' _ hp, ?_⟩
    have := h u hu
    simp only [b65g_quadratic] at this
    exact mul_right_cancel₀ (pow_ne_zero 2 hds) this
  rw [div_left_inj' hD, b65g_numerator_poly, b65g_numerator_poly] at hq
  have hp := RatFunc.algebraMap_injective ℂ hq
  funext k
  rw [← b65g_numerator_coeff N k, ← b65g_numerator_coeff N' k, hp]


/-- `K(P, R) K(P', R') = K(P' P, R' R)` for `K = b66e_productChange`. -/
theorem b65g_productChange_mul (P R P' R' : Matrix (Fin 3) (Fin 3) ℂ) :
    b66e_productChange P R * b66e_productChange P' R' = b66e_productChange (P' * P) (R' * R) := by
  ext u w
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective u
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective w
  simp only [Matrix.mul_apply, b66e_productChange, Equiv.symm_apply_apply]
  rw [← (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ ↦ Finset.sum_congr rfl fun g _ ↦ ?_
  ring

/-- `K(1, 1) = 1`. -/
theorem b65g_productChange_one : b66e_productChange 1 1 = 1 := by
  ext u w
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective u
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective w
  simp only [b66e_productChange, Matrix.one_apply, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The r-vector is linear in its coefficients. -/
theorem b65g_principal_comb (t : Fin 4 ⊕ Fin 12 → ℂ) (l : Fin 3 → ℂ) (v : Fin 3 → Fin 36 → ℂ)
    (j : Fin 4) : b65q_principal t (∑ f, l f • v f) j =
      ∑ f, RatFunc.C (l f) * b65q_principal t (v f) j := by
  simp only [b65q_principal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  exact Finset.sum_comm

/-- The q-vector is linear in its coefficients. -/
theorem b65g_qVector_comb (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (l : Fin 3 → ℂ) (v : Fin 3 → Fin 48 → ℂ) (j : Fin 4) :
    b65q_qVector t node w (∑ f, l f • v f) j =
      ∑ f, RatFunc.C (l f) * b65q_qVector t node w (v f) j := by
  have h1 : (fun i : Fin 36 ↦ (∑ f, l f • v f) ⟨i.val, by omega⟩) =
      ∑ f, l f • fun i : Fin 36 ↦ v f ⟨i.val, by omega⟩ := by
    funext i; simp [Finset.sum_apply]
  simp only [b65q_qVector, h1, b65g_principal_comb, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp_rw [← mul_div_assoc, ← Finset.sum_div, ← map_mul, ← map_sum]
  congr 2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

end HodgeLean.Foundations.Program
