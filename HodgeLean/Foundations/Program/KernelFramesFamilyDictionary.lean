import HodgeLean.Foundations.Program.KernelFramesFamilyDictTools
import HodgeLean.Foundations.Program.KernelFramesFamilyNormal

/-! # B6-5 stage 5d, family part: the differential dictionary on the `s`-line

A rational vector satisfying the order conditions of the dictionary is the principal-part
vector of its own Laurent coefficients (plus, for q, the interpolated moving-pole residues), and
those coefficients solve the systems; conversely kernel vectors satisfy the conditions. The order
conditions for an arbitrary analytic normal-form gauge are those of the zero-resonance gauge
(`b65q_gauge_cond`), the moving-pole residues are multiples of the left eigenvectors
(`b65q_rank_one_perp`), and both maps are injective.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Polynomial Matrix Filter
open scoped LaurentSeries RatFunc Topology Nat
namespace HodgeLean.Foundations.Program

/-- Twice the fixed-pole exponents. -/
def b65q_lam2 : Fin 4 → Fin 4 → ℤ := ![![-3, -2, -2, 3], ![-6, -4, -4, 6], ![-4, -4, 4, 4], ![-4, -4, 4, 4]]

theorem b65q_exponents_lam2 (k i : Fin 4) : b65p_exponents k i = (b65q_lam2 k i : ℂ) / 2 := by
  fin_cases k <;> fin_cases i <;> norm_num [b65p_exponents, b65q_lam2]

theorem b65q_rFloor_eq (k j : Fin 4) : ⌊(b65p_exponents k j).re⌋ = b65q_rFloor k j := by
  rw [b65q_exponents_lam2]
  fin_cases k <;> fin_cases j <;> norm_num [b65q_lam2, b65q_rFloor, Int.floor_eq_iff]

theorem b65q_qFloor_eq (k j : Fin 4) : ⌊(-b65p_exponents k j).re⌋ = b65q_qFloor k j := by
  rw [b65q_exponents_lam2]
  fin_cases k <;> fin_cases j <;> norm_num [b65q_lam2, b65q_qFloor, Int.floor_eq_iff]

theorem b65q_floor_table : ∀ k i j : Fin 4, (b65q_lam2 k i - b65q_lam2 k j) % 2 = 0 →
    0 ≤ b65q_lam2 k i - b65q_lam2 k j →
    b65q_rFloor k i = b65q_rFloor k j + (b65q_lam2 k i - b65q_lam2 k j) / 2 ∧
    b65q_qFloor k j = b65q_qFloor k i + (b65q_lam2 k i - b65q_lam2 k j) / 2 := by decide

theorem b65q_two_n (k i j : Fin 4) (n : ℕ) (h : (n : ℂ) = b65p_exponents k i - b65p_exponents k j) :
    2 * (n : ℤ) = b65q_lam2 k i - b65q_lam2 k j := by
  rw [b65q_exponents_lam2, b65q_exponents_lam2] at h
  have : ((2 * (n : ℤ) : ℤ) : ℂ) = ((b65q_lam2 k i - b65q_lam2 k j : ℤ) : ℂ) := by
    push_cast; linear_combination 2 * h
  exact_mod_cast this

theorem b65q_rFloor_compat (k : Fin 4) : ∀ (n : ℕ) (i j : Fin 4),
    (n : ℂ) = b65p_exponents k i - b65p_exponents k j → b65q_rFloor k i = b65q_rFloor k j + n := by
  intro n i j h
  have h2 := b65q_two_n k i j n h
  have := (b65q_floor_table k i j (by omega) (by omega)).1
  rw [this]; omega

theorem b65q_qFloor_compat (k : Fin 4) : ∀ (n : ℕ) (i j : Fin 4),
    (n : ℂ) = -b65p_exponents k i - -b65p_exponents k j → b65q_qFloor k i = b65q_qFloor k j + n := by
  intro n i j h
  have h2 := b65q_two_n k j i n (by linear_combination h)
  have := (b65q_floor_table k j i (by omega) (by omega)).2
  rw [this]; omega

theorem b65q_minFloor (k j : Fin 4) : -(b65q_maxOrder k : ℤ) ≤ b65q_rFloor k j ∧
    -(b65q_maxOrder k : ℤ) ≤ b65q_qFloor k j := by
  revert k j; decide

theorem b65q_rRow_lt_floor (r : Fin 41) :
    (b65q_rRow r).2.2 < b65q_rFloor (b65q_rRow r).1 (b65q_rRow r).2.1 := by revert r; decide

theorem b65q_qRow_lt_floor (r : Fin 53) :
    (b65q_qRow r).2.2 < b65q_qFloor (b65q_qRow r).1 (b65q_qRow r).2.1 := by revert r; decide

theorem b65q_maxOrder_le (k : Fin 4) : b65q_maxOrder k ≤ 3 := by fin_cases k <;> decide

theorem b65q_slot_spec (k : Fin 4) (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ b65q_maxOrder k) :
    b65k_poleIndex (b65q_slot k ⟨m, by have := b65q_maxOrder_le k; omega⟩) = k ∧
      b65k_poleOrder (b65q_slot k ⟨m, by have := b65q_maxOrder_le k; omega⟩) = m := by
  fin_cases k <;> simp only [b65q_maxOrder] at h2 <;> norm_num at h2 <;> interval_cases m <;>
    simp [b65q_slot, b65k_poleIndex, b65k_poleOrder]

/-- Recovering a vector of Laurent series from its image under an invertible coefficient
matrix. -/
theorem b65q_combo_inv {K K' : Matrix (Fin 4) (Fin 4) (PowerSeries ℂ)} (hKK' : K * K' = 1)
    (L : Fin 4 → LaurentSeries ℂ) (i : Fin 4) :
    L i = ∑ j, HahnSeries.ofPowerSeries ℤ ℂ (K i j) *
      ∑ l, HahnSeries.ofPowerSeries ℤ ℂ (K' j l) * L l := by
  simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, hKK', Matrix.one_apply]
  simp [apply_ite (HahnSeries.ofPowerSeries ℤ ℂ)]

theorem b65q_rCoeff_inverse (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (hP : IsUnit (P k)) :
    (b65q_cst (P k) * b65q_MPS (b65q_gauge t A (P k) k)) * b65q_MPS (b65q_rCoeff t A P k) = 1 := by
  rw [show b65q_rCoeff t A P k = fun n ↦ b65q_seriesInv (b65q_gauge t A (P k) k) n * (P k)⁻¹ from rfl,
    b65q_MPS_mul_cst, show b65q_cst (P k) * b65q_MPS (b65q_gauge t A (P k) k) *
      (b65q_MPS (b65q_seriesInv (b65q_gauge t A (P k) k)) * b65q_cst (P k)⁻¹) =
      b65q_cst (P k) * (b65q_MPS (b65q_gauge t A (P k) k) *
        b65q_MPS (b65q_seriesInv (b65q_gauge t A (P k) k))) * b65q_cst (P k)⁻¹ by noncomm_ring,
    b65q_MPS_seriesInv _ (b65q_gauge_zero_coeff t A (P k) k), mul_one, ← b65q_cst_mul,
    Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP)]
  simp [b65q_cst]

/-- The Laurent coefficients of a rational vector at the fixed poles, in the column order of the
unknowns. -/
def b65q_coeffVec (t : Fin 4 ⊕ Fin 12 → ℂ) (r : Fin 4 → RatFunc ℂ) : Fin 36 → ℂ := fun col ↦
  (b65q_L (t (Sum.inl (b65k_poleIndex ⟨col.val / 4, by omega⟩))) (r ⟨col.val % 4, by omega⟩)).coeff
    (-(b65k_poleOrder ⟨col.val / 4, by omega⟩ : ℤ))

theorem b65q_coeffVec_apply (t : Fin 4 ⊕ Fin 12 → ℂ) (r : Fin 4 → RatFunc ℂ) (b : Fin 9) (i : Fin 4) :
    b65q_coeffVec t r ⟨4 * b.val + i.val, by omega⟩ =
      (b65q_L (t (Sum.inl (b65k_poleIndex b))) (r i)).coeff (-(b65k_poleOrder b : ℤ)) := by
  have h1 : (⟨(4 * b.val + i.val) / 4, by omega⟩ : Fin 9) = b := by
    ext; show (4 * b.val + i.val) / 4 = b.val; omega
  have h2 : (⟨(4 * b.val + i.val) % 4, by omega⟩ : Fin 4) = i := by
    ext; show (4 * b.val + i.val) % 4 = i.val; omega
  simp only [b65q_coeffVec, h1, h2]

theorem b65q_ge_sub {f g : LaurentSeries ℂ} {n : ℤ} (hf : b65q_ge f n) (hg : b65q_ge g n) :
    b65q_ge (f - g) n := by
  rw [sub_eq_add_neg]
  exact b65q_ge_add hf (by rw [b65q_ge, HahnSeries.orderTop_neg]; exact hg)

attribute [local instance] Classical.propDecidable in
/-- **A rational vector with the pole bounds of the fixed principal parts is the principal-part
vector of its Laurent coefficients.** -/
theorem b65q_eq_principal (t : Fin 4 ⊕ Fin 12 → ℂ)
    (htf : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) (r : Fin 4 → RatFunc ℂ) (i : Fin 4)
    (hfix : ∀ k, b65q_ge (b65q_L (t (Sum.inl k)) (r i)) (-(b65q_maxOrder k : ℤ)))
    (hoff : ∀ a, (∀ k, a ≠ t (Sum.inl k)) → b65q_ge (b65q_L a (r i)) 0)
    (hv : RatFunc.inftyValuation ℂ (r i) ≤ WithZero.exp (-2)) :
    r i = b65q_principal t (b65q_coeffVec t r) i := by
  set D := r i - b65q_principal t (b65q_coeffVec t r) i
  have hD : ∀ a, b65q_ge (b65q_L a D) 0 := by
    intro a
    by_cases ha : ∃ k, a = t (Sum.inl k)
    · obtain ⟨k, rfl⟩ := ha
      rw [b65q_ge_iff]
      intro m hm
      simp only [D, map_sub, HahnSeries.coeff_sub]
      by_cases hm' : m < -(b65q_maxOrder k : ℤ)
      · rw [(b65q_ge_iff _ _).mp (hfix k) m hm',
          (b65q_ge_iff _ _).mp (b65q_ge_L_principal_at t _ k (htf k) i) m hm', sub_zero]
      · obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = -(m' : ℤ) := ⟨(-m).toNat, by omega⟩
        have h1 : 1 ≤ m' := by omega
        have h2 : m' ≤ b65q_maxOrder k := by omega
        rw [b65q_principal_coeff t _ k (htf k) i m' h1, b65q_slot_sum k m' h1, dif_pos h2,
          b65q_coeffVec_apply]
        obtain ⟨hs1, hs2⟩ := b65q_slot_spec k m' h1 h2
        rw [hs1, hs2, sub_self]
    · simp only [not_exists] at ha
      simp only [D, map_sub]
      exact b65q_ge_sub (hoff a ha) (b65q_ge_L_principal_off t _ a ha i)
  have hden := b65q_denom_eq_one D hD
  have hvD : RatFunc.inftyValuation ℂ D ≤ WithZero.exp (-1) := by
    simp only [D]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (b65q_v_principal_le t _ i))
    exact hv.trans (WithZero.exp_le_exp.mpr (by norm_num))
  have := b65q_poly_zero_of_v D hden hvD
  exact sub_eq_zero.mp this

attribute [local instance] Classical.propDecidable in
theorem b65q_inf_zero (f : RatFunc ℂ) (s : ℂ)
    (hrest : RatFunc.inftyValuation ℂ (f - RatFunc.C s * (1 / RatFunc.X)) ≤ WithZero.exp (-2))
    (hf : RatFunc.inftyValuation ℂ f ≤ WithZero.exp (-2)) : s = 0 := by
  by_contra hs
  have h1 : RatFunc.C s * (1 / RatFunc.X) = f - (f - RatFunc.C s * (1 / RatFunc.X)) := by ring
  have h2 : RatFunc.inftyValuation ℂ (RatFunc.C s * (1 / RatFunc.X)) ≤ WithZero.exp (-2) := by
    rw [h1]; exact (Valuation.map_sub _ _ _).trans (max_le hf hrest)
  rw [map_mul, RatFunc.inftyValuation.C _ hs, one_mul, RatFunc.inftyValuation.X_inv] at h2
  have := WithZero.exp_le_exp.mp h2
  omega

attribute [local instance] Classical.propDecidable in
/-- **The r-dictionary.** Under the order-condition equivalence at each fixed pole, the r-space
is the image of the kernel of the r-system under the principal-part map. -/
theorem b65q_rSpace_char (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (htf : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b'))
    (htm : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x)) (hP : ∀ k, IsUnit (P k))
    (hcond : ∀ k (r : Fin 4 → RatFunc ℂ), (∀ j, ((b65q_rFloor k j : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun s ↦ ((P k * H k s)⁻¹ *ᵥ fun i ↦ b65q_eval (r i) s) j)
          (t (Sum.inl k))) ↔
      ∀ j, b65q_ge (b65q_KL (t (Sum.inl k)) (b65q_rCoeff t A P k) r j) (b65q_rFloor k j)) :
    b65q_rSpace t P H = b65q_principal t '' {c | b65q_rSystem t A P *ᵥ c = 0} := by
  ext r
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hfl : ∀ k j, b65q_ge (b65q_KL (t (Sum.inl k)) (b65q_rCoeff t A P k) r j)
        (b65q_rFloor k j) := fun k ↦ (hcond k r).mp fun j ↦ by
      rw [← b65q_rFloor_eq]; exact h3 k j
    have hfix : ∀ k i, b65q_ge (b65q_L (t (Sum.inl k)) (r i)) (-(b65q_maxOrder k : ℤ)) := by
      intro k i
      rw [b65q_combo_inv (b65q_rCoeff_inverse t A P k (hP k)) (fun i ↦ b65q_L (t (Sum.inl k)) (r i)) i]
      refine b65q_ge_sum _ fun j _ ↦ ?_
      exact b65q_ge_mono (b65q_ge_mul (b65q_ge_ofPS _) (hfl k j))
        (by have := (b65q_minFloor k j).1; omega)
    have hoff : ∀ i a, (∀ k, a ≠ t (Sum.inl k)) → b65q_ge (b65q_L a (r i)) 0 := by
      intro i a ha
      apply b65q_ge_of_denom_ne
      intro h0
      obtain ⟨q, hq⟩ := h1 i a h0
      rcases q with k | x
      · exact ha k hq.symm
      · exact h2 x i (hq ▸ h0)
    have hv : ∀ i, RatFunc.inftyValuation ℂ (r i) ≤ WithZero.exp (-2) :=
      fun i ↦ b65q_v_le_of_intDegree _ (h4 i)
    have hr : ∀ i, r i = b65q_principal t (b65q_coeffVec t r) i := fun i ↦
      b65q_eq_principal t htf r i (fun k ↦ hfix k i) (hoff i) (hv i)
    refine ⟨b65q_coeffVec t r, ?_, (funext hr).symm⟩
    show b65q_rSystem t A P *ᵥ b65q_coeffVec t r = 0
    funext row
    by_cases hrow : row.val < 41
    · have h := b65q_rSystem_row t A P (b65q_coeffVec t r) ⟨row.val, hrow⟩ htf
      rw [show (⟨row.val, by omega⟩ : Fin 45) = row from rfl] at h
      rw [h, show b65q_principal t (b65q_coeffVec t r) = r from (funext hr).symm]
      exact (b65q_ge_iff _ _).mp (hfl _ _) _ (b65q_rRow_lt_floor _)
    · set i : Fin 4 := ⟨row.val - 41, by omega⟩ with hi_def
      have hi : row = ⟨41 + i.val, by omega⟩ := by
        ext; show row.val = 41 + (row.val - 41); omega
      rw [hi, b65q_rSystem_inf]
      have := b65q_v_principal t (b65q_coeffVec t r) i
      rw [← hr i] at this
      exact b65q_inf_zero (r i) _ this (hv i)
  · rintro ⟨c, hc, rfl⟩
    have hc' : b65q_rSystem t A P *ᵥ c = 0 := hc
    have hinf : ∀ i : Fin 4, (∑ b : Fin 9, if b65k_poleOrder b = 1 then
        c ⟨4 * b.val + i.val, by omega⟩ else 0) = 0 := fun i ↦ by
      rw [← b65q_rSystem_inf t A P c i, hc']; rfl
    refine ⟨fun i s h0 ↦ ?_, fun x i ↦ ?_, fun k j ↦ ?_, fun i ↦ ?_⟩
    · by_contra hs
      have ha : ∀ k, s ≠ t (Sum.inl k) := fun k h ↦ hs ⟨Sum.inl k, h.symm⟩
      exact b65q_denom_eval_ne _ s (b65q_ge_L_principal_off t c s ha i) h0
    · exact b65q_denom_eval_ne _ _ (b65q_ge_L_principal_off t c _ (fun k h ↦ htm k x h.symm) i)
    · rw [b65q_rFloor_eq]
      exact (hcond k (b65q_principal t c)).mpr (fun j ↦ b65q_r_order t A P c hc' htf k j) j
    · apply b65q_intDegree_of_v
      have := b65q_v_principal t c i
      rw [hinf i, map_zero, zero_mul, sub_zero] at this
      exact this

theorem b65q_qCoeff_inverse (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (hP : IsUnit (P k)) :
    (b65q_MPS (b65q_seriesInv (b65q_gauge t A (P k) k)) * b65q_cst (P k)⁻¹)ᵀ *
      b65q_MPS (b65q_qCoeff t A P k) = 1 := by
  rw [show b65q_qCoeff t A P k = fun n ↦ (P k * b65q_gauge t A (P k) k n)ᵀ from rfl,
    b65q_MPS_transpose, b65q_MPS_cst_mul, ← Matrix.transpose_mul,
    show b65q_cst (P k) * b65q_MPS (b65q_gauge t A (P k) k) *
      (b65q_MPS (b65q_seriesInv (b65q_gauge t A (P k) k)) * b65q_cst (P k)⁻¹) =
      b65q_cst (P k) * (b65q_MPS (b65q_gauge t A (P k) k) *
        b65q_MPS (b65q_seriesInv (b65q_gauge t A (P k) k))) * b65q_cst (P k)⁻¹ by noncomm_ring,
    b65q_MPS_seriesInv _ (b65q_gauge_zero_coeff t A (P k) k), mul_one, ← b65q_cst_mul,
    Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP)]
  simp [b65q_cst]

theorem b65q_betaPart_coeff_neg (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (a : ℂ) (ha : ∀ x, a ≠ t (Sum.inr x)) (i : Fin 4) (m : ℤ) (hm : m < 0) :
    (b65q_L a (b65q_betaPart t node w d i)).coeff m = 0 :=
  (b65q_ge_iff _ _).mp (b65q_ge_L_betaPart t node w d a ha i) m hm

/-- The interpolated residue multiple `β(node_t)` of a q-coefficient vector at the label `x`. -/
def b65q_beta (node : Fin 12 → ℂ) (d : Fin 48 → ℂ) (x : Fin 12) : ℂ :=
  ∑ v : Fin 6, d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val

theorem b65q_betaPart_residue (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (x : Fin 12) (hx : ∀ y, y ≠ x → t (Sum.inr x) ≠ t (Sum.inr y)) (i : Fin 4) :
    (b65q_L (t (Sum.inr x)) (b65q_betaPart t node w d i)).coeff (-1) =
      b65q_beta node d x * w x i := by
  simp only [b65q_betaPart, map_sum, HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single x]
  · rw [← pow_one (RatFunc.X - RatFunc.C (t (Sum.inr x))), b65q_L_div, b65q_L_inv_pow_eq,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    simp [b65q_beta]
  · intro y _ hy
    rw [← pow_one (RatFunc.X - RatFunc.C (t (Sum.inr y))), b65q_L_div,
      b65q_L_inv_pow_ne (hx y hy), HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
      b65q_ofPS_coeff, if_neg (by norm_num), mul_zero]
  · simp

attribute [local instance] Classical.propDecidable in
theorem b65q_v_betaPart_le (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (i : Fin 4) :
    RatFunc.inftyValuation ℂ (b65q_betaPart t node w d i) ≤ WithZero.exp (-1) := by
  simp only [b65q_betaPart]
  refine Valuation.map_sum_le _ fun x _ ↦ ?_
  rw [div_eq_mul_inv, map_mul, ← pow_one (RatFunc.X - RatFunc.C (t (Sum.inr x))), b65q_v_inv_pow]
  calc RatFunc.inftyValuation ℂ (RatFunc.C _) * WithZero.exp (-((1 : ℕ) : ℤ)) ≤
      1 * WithZero.exp (-1) := by
        gcongr
        · exact b65q_v_C_le _
        · simp
    _ = _ := one_mul _

theorem b65q_qVector_split (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (i : Fin 4) :
    b65q_qVector t node w d i -
        RatFunc.C ((∑ b : Fin 9, if b65k_poleOrder b = 1 then d ⟨4 * b.val + i.val, by omega⟩
          else 0) + ∑ x : Fin 12, b65q_beta node d x * w x i) * (1 / RatFunc.X) =
      (b65q_principal t (fun i ↦ d ⟨i.val, by omega⟩) i -
        RatFunc.C (∑ b : Fin 9, if b65k_poleOrder b = 1 then d ⟨4 * b.val + i.val, by omega⟩
          else 0) * (1 / RatFunc.X)) +
      (b65q_betaPart t node w d i - RatFunc.C (∑ x : Fin 12, (∑ v : Fin 6,
        d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x i) *
          (1 / RatFunc.X)) := by
  rw [b65q_qVector_eq, map_add]
  simp only [b65q_beta]
  ring

attribute [local instance] Classical.propDecidable in
theorem b65q_v_qVector_split (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (i : Fin 4) :
    RatFunc.inftyValuation ℂ (b65q_qVector t node w d i -
        RatFunc.C ((∑ b : Fin 9, if b65k_poleOrder b = 1 then d ⟨4 * b.val + i.val, by omega⟩
          else 0) + ∑ x : Fin 12, b65q_beta node d x * w x i) * (1 / RatFunc.X)) ≤
      WithZero.exp (-2) := by
  rw [b65q_qVector_split]
  exact (Valuation.map_add _ _ _).trans (max_le (b65q_v_principal t _ i)
    (b65q_v_betaPart t node w d i))

theorem b65q_ge_L_qVector_moving (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ)
    (w : Fin 12 → Fin 4 → ℂ) (d : Fin 48 → ℂ)
    (htm : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x))
    (htmm : ∀ x y, y ≠ x → t (Sum.inr x) ≠ t (Sum.inr y)) (x : Fin 12) (i : Fin 4) :
    b65q_ge (b65q_L (t (Sum.inr x)) (b65q_qVector t node w d i)) (-1) := by
  rw [b65q_qVector_eq, map_add]
  exact b65q_ge_add (b65q_ge_mono (b65q_ge_L_principal_off t _ _ (fun k h ↦ htm k x h.symm) i)
    (by norm_num)) (b65q_ge_L_betaPart_at t node w d x (htmm x) i)

theorem b65q_qVector_residue (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ)
    (w : Fin 12 → Fin 4 → ℂ) (d : Fin 48 → ℂ)
    (htm : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x))
    (htmm : ∀ x y, y ≠ x → t (Sum.inr x) ≠ t (Sum.inr y)) (x : Fin 12) (i : Fin 4) :
    (b65q_L (t (Sum.inr x)) (b65q_qVector t node w d i)).coeff (-1) =
      b65q_beta node d x * w x i := by
  rw [b65q_qVector_eq, map_add, HahnSeries.coeff_add, b65q_betaPart_residue t node w d x (htmm x),
    (b65q_ge_iff _ _).mp (b65q_ge_L_principal_off t _ _ (fun k h ↦ htm k x h.symm) i) (-1)
      (by norm_num), zero_add]

theorem b65q_qVector_fixed_coeff (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ)
    (w : Fin 12 → Fin 4 → ℂ) (d : Fin 48 → ℂ) (k : Fin 4)
    (htm : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x)) (i : Fin 4) (m : ℤ) (hm : m < 0) :
    (b65q_L (t (Sum.inl k)) (b65q_qVector t node w d i)).coeff m =
      (b65q_L (t (Sum.inl k)) (b65q_principal t (fun i ↦ d ⟨i.val, by omega⟩) i)).coeff m := by
  rw [b65q_qVector_eq, map_add, HahnSeries.coeff_add,
    b65q_betaPart_coeff_neg t node w d _ (htm k) i m hm, add_zero]

attribute [local instance] Classical.propDecidable in
/-- **The q-dictionary.** -/
theorem b65q_qSpace_char (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (htf : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b'))
    (htm : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x))
    (htmm : ∀ x y, y ≠ x → t (Sum.inr x) ≠ t (Sum.inr y)) (hP : ∀ k, IsUnit (P k))
    (hnode : ∀ e, Set.InjOn node (b65q_fibreSet e))
    (hperp : ∀ x (ρ : Fin 4 → ℂ), (∀ v, A (Sum.inr x) *ᵥ v = 0 → v ⬝ᵥ ρ = 0) →
      ∃ β : ℂ, ρ = β • w x)
    (hwA : ∀ x v, A (Sum.inr x) *ᵥ v = 0 → v ⬝ᵥ w x = 0)
    (hcond : ∀ k (q : Fin 4 → RatFunc ℂ), (∀ j, ((b65q_qFloor k j : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun s ↦ ((P k * H k s)ᵀ *ᵥ fun i ↦ b65q_eval (q i) s) j)
          (t (Sum.inl k))) ↔
      ∀ j, b65q_ge (b65q_KL (t (Sum.inl k)) (b65q_qCoeff t A P k) q j) (b65q_qFloor k j)) :
    b65q_qSpace t A P H = b65q_qVector t node w '' {d | b65q_qSystem t A P node w *ᵥ d = 0} := by
  ext q
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hfl : ∀ k j, b65q_ge (b65q_KL (t (Sum.inl k)) (b65q_qCoeff t A P k) q j)
        (b65q_qFloor k j) := fun k ↦ (hcond k q).mp fun j ↦ by
      rw [← b65q_qFloor_eq]; exact h4 k j
    have hfix : ∀ k i, b65q_ge (b65q_L (t (Sum.inl k)) (q i)) (-(b65q_maxOrder k : ℤ)) := by
      intro k i
      rw [b65q_combo_inv (b65q_qCoeff_inverse t A P k (hP k)) (fun i ↦ b65q_L (t (Sum.inl k)) (q i)) i]
      refine b65q_ge_sum _ fun j _ ↦ ?_
      exact b65q_ge_mono (b65q_ge_mul (b65q_ge_ofPS _) (hfl k j))
        (by have := (b65q_minFloor k j).2; omega)
    have hmov : ∀ x i, b65q_ge (b65q_L (t (Sum.inr x)) (q i)) (-1) := by
      intro x i
      have := h2 x i
      rw [b65q_merOrd_eval] at this
      exact this
    have hoff : ∀ i a, (∀ r, a ≠ t r) → b65q_ge (b65q_L a (q i)) 0 := by
      intro i a ha
      apply b65q_ge_of_denom_ne
      intro h0
      obtain ⟨r, hr⟩ := h1 i a h0
      exact ha r hr.symm
    set ρ : Fin 12 → Fin 4 → ℂ := fun x i ↦ (b65q_L (t (Sum.inr x)) (q i)).coeff (-1)
    have hρ : ∀ x v, A (Sum.inr x) *ᵥ v = 0 → v ⬝ᵥ ρ x = 0 := by
      intro x v hv
      have := h3 x v hv
      rw [b65q_merOrd_dot] at this
      have h0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (i := (-1 : ℤ))
        (lt_of_lt_of_le (by exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)) this)
      simp only [HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        smul_eq_mul] at h0
      simpa [dotProduct, ρ] using h0
    choose β hβ using fun x ↦ hperp x (ρ x) (hρ x)
    choose dv hdv using fun e ↦ b65q_interpolate node e (hnode e) β
    set dvec : Fin 48 → ℂ := fun col ↦ if h : col.val < 36 then b65q_coeffVec t q ⟨col.val, h⟩
      else dv ⟨(col.val - 36) / 6, by omega⟩ ⟨(col.val - 36) % 6, by omega⟩
    have hd36 : (fun i : Fin 36 ↦ dvec ⟨i.val, by omega⟩) = b65q_coeffVec t q := by
      funext i; simp [dvec, i.isLt]
    have hbeta : ∀ x, b65q_beta node dvec x = β x := by
      intro x
      rw [← hdv (b65q_fibreIndex x) x (by simp [b65q_fibreSet])]
      simp only [b65q_beta, dvec]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [dif_neg (by omega)]
      have h1 : (⟨(36 + 6 * (b65q_fibreIndex x).val + v.val - 36) / 6, by omega⟩ : Fin 2) =
          b65q_fibreIndex x := by
        ext; show (36 + 6 * (b65q_fibreIndex x).val + v.val - 36) / 6 = (b65q_fibreIndex x).val
        omega
      have h2 : (⟨(36 + 6 * (b65q_fibreIndex x).val + v.val - 36) % 6, by omega⟩ : Fin 6) = v := by
        ext; show (36 + 6 * (b65q_fibreIndex x).val + v.val - 36) % 6 = v.val
        omega
      rw [h1, h2]
    have hq : ∀ i, q i = b65q_qVector t node w dvec i := by
      intro i
      set D := q i - b65q_qVector t node w dvec i
      have hD : ∀ a, b65q_ge (b65q_L a D) 0 := by
        intro a
        by_cases hfa : ∃ k, a = t (Sum.inl k)
        · obtain ⟨k, rfl⟩ := hfa
          rw [b65q_ge_iff]
          intro m hm
          simp only [D, map_sub, HahnSeries.coeff_sub]
          rw [b65q_qVector_fixed_coeff t node w dvec k htm i m hm, hd36]
          by_cases hm' : m < -(b65q_maxOrder k : ℤ)
          · rw [(b65q_ge_iff _ _).mp (hfix k i) m hm',
              (b65q_ge_iff _ _).mp (b65q_ge_L_principal_at t _ k (htf k) i) m hm', sub_zero]
          · obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = -(m' : ℤ) := ⟨(-m).toNat, by omega⟩
            have h1' : 1 ≤ m' := by omega
            have h2' : m' ≤ b65q_maxOrder k := by omega
            rw [b65q_principal_coeff t _ k (htf k) i m' h1', b65q_slot_sum k m' h1', dif_pos h2',
              b65q_coeffVec_apply]
            obtain ⟨hs1, hs2⟩ := b65q_slot_spec k m' h1' h2'
            rw [hs1, hs2, sub_self]
        · simp only [not_exists] at hfa
          by_cases hma : ∃ x, a = t (Sum.inr x)
          · obtain ⟨x, rfl⟩ := hma
            rw [b65q_ge_iff]
            intro m hm
            simp only [D, map_sub, HahnSeries.coeff_sub]
            by_cases hm1 : m < -1
            · rw [(b65q_ge_iff _ _).mp (hmov x i) m hm1,
                (b65q_ge_iff _ _).mp (b65q_ge_L_qVector_moving t node w dvec htm htmm x i) m hm1,
                sub_zero]
            · rw [show m = -1 by omega, b65q_qVector_residue t node w dvec htm htmm x i, hbeta]
              have := congrFun (hβ x) i
              simp only [ρ, Pi.smul_apply, smul_eq_mul] at this
              rw [this, sub_self]
          · simp only [not_exists] at hma
            have ha : ∀ r, a ≠ t r := fun r ↦ by
              rcases r with k | x
              · exact hfa k
              · exact hma x
            simp only [D, map_sub]
            refine b65q_ge_sub (hoff i a ha) ?_
            rw [b65q_qVector_eq, map_add]
            exact b65q_ge_add (by simpa using b65q_ge_L_principal_off t _ a hfa i)
              (b65q_ge_L_betaPart t node w dvec a hma i)
      have hden := b65q_denom_eq_one D hD
      have hvD : RatFunc.inftyValuation ℂ D ≤ WithZero.exp (-1) := by
        simp only [D]
        refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
        · exact (b65q_v_le_of_intDegree _ (h5 i)).trans (WithZero.exp_le_exp.mpr (by norm_num))
        · rw [b65q_qVector_eq]
          exact (Valuation.map_add _ _ _).trans (max_le (b65q_v_principal_le t _ i)
            (b65q_v_betaPart_le t node w dvec i))
      exact sub_eq_zero.mp (b65q_poly_zero_of_v D hden hvD)
    refine ⟨dvec, ?_, (funext hq).symm⟩
    show b65q_qSystem t A P node w *ᵥ dvec = 0
    funext row
    by_cases hrow : row.val < 53
    · have h := b65q_qSystem_row t A P node w dvec ⟨row.val, hrow⟩ htf htm
      rw [show (⟨row.val, by omega⟩ : Fin 57) = row from rfl] at h
      rw [h, show b65q_qVector t node w dvec = q from (funext hq).symm]
      exact (b65q_ge_iff _ _).mp (hfl _ _) _ (b65q_qRow_lt_floor _)
    · set i : Fin 4 := ⟨row.val - 53, by omega⟩ with hi_def
      have hi : row = ⟨53 + i.val, by omega⟩ := by
        ext; show row.val = 53 + (row.val - 53); omega
      rw [hi, b65q_qSystem_inf]
      have := b65q_v_qVector_split t node w dvec i
      rw [← hq i] at this
      have h0 := b65q_inf_zero (q i) _ this (b65q_v_le_of_intDegree _ (h5 i))
      simpa [b65q_beta] using h0
  · rintro ⟨d, hd, rfl⟩
    have hd' : b65q_qSystem t A P node w *ᵥ d = 0 := hd
    have hinf : ∀ i : Fin 4, (∑ b : Fin 9, if b65k_poleOrder b = 1 then
        d ⟨4 * b.val + i.val, by omega⟩ else 0) + ∑ x : Fin 12, b65q_beta node d x * w x i = 0 := by
      intro i
      have := congrFun hd' ⟨53 + i.val, by omega⟩
      rw [b65q_qSystem_inf] at this
      simpa [b65q_beta] using this
    refine ⟨fun i s h0 ↦ ?_, fun x i ↦ ?_, fun x v hv ↦ ?_, fun k j ↦ ?_, fun i ↦ ?_⟩
    · by_contra hs
      have ha : ∀ r, s ≠ t r := fun r h ↦ hs ⟨r, h.symm⟩
      have hge : b65q_ge (b65q_L s (b65q_qVector t node w d i)) 0 := by
        rw [b65q_qVector_eq, map_add]
        exact b65q_ge_add (b65q_ge_L_principal_off t _ s (fun k ↦ ha _) i)
          (b65q_ge_L_betaPart t node w d s (fun x ↦ ha _) i)
      exact b65q_denom_eval_ne _ s hge h0
    · rw [b65q_merOrd_eval]
      exact b65q_ge_L_qVector_moving t node w d htm htmm x i
    · rw [b65q_merOrd_dot]
      show b65q_ge _ 0
      rw [b65q_ge_iff]
      intro m hm
      simp only [HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        smul_eq_mul]
      by_cases hm1 : m < -1
      · exact Finset.sum_eq_zero fun i _ ↦ by
          rw [(b65q_ge_iff _ _).mp (b65q_ge_L_qVector_moving t node w d htm htmm x i) m hm1,
            mul_zero]
      · rw [show m = -1 by omega]
        simp only [b65q_qVector_residue t node w d htm htmm x]
        have := hwA x v hv
        simp only [dotProduct] at this
        calc ∑ i, v i * (b65q_beta node d x * w x i) = b65q_beta node d x * ∑ i, v i * w x i := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
          _ = 0 := by rw [this, mul_zero]
    · rw [b65q_qFloor_eq]
      exact (hcond k (b65q_qVector t node w d)).mpr
        (fun j ↦ b65q_q_order t A P node w d hd' htf htm k j) j
    · apply b65q_intDegree_of_v
      have := b65q_v_qVector_split t node w d i
      rw [hinf i, map_zero, zero_mul, sub_zero] at this
      exact this

theorem b65q_poleOrder_pos : ∀ b : Fin 9, 0 < b65k_poleOrder b := by decide

theorem b65q_principal_injective (t : Fin 4 ⊕ Fin 12 → ℂ)
    (htf : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) :
    Function.Injective (b65q_principal t) := by
  intro c c' h
  funext col
  set b : Fin 9 := ⟨col.val / 4, by omega⟩
  set i : Fin 4 := ⟨col.val % 4, by omega⟩
  have hcol : col = ⟨4 * b.val + i.val, by omega⟩ := by
    ext; show col.val = 4 * (col.val / 4) + col.val % 4; omega
  rw [hcol, ← b65q_principal_extract t c htf b i, ← b65q_principal_extract t c' htf b i, h]

theorem b65q_qVector_injective (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ)
    (w : Fin 12 → Fin 4 → ℂ)
    (htf : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b'))
    (htm : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x))
    (htmm : ∀ x y, y ≠ x → t (Sum.inr x) ≠ t (Sum.inr y))
    (hnode : ∀ e, Set.InjOn node (b65q_fibreSet e)) (hw : ∀ x, w x ≠ 0) :
    Function.Injective (b65q_qVector t node w) := by
  intro d d' h
  have hfix : ∀ col : Fin 36, d ⟨col.val, by omega⟩ = d' ⟨col.val, by omega⟩ := by
    intro col
    set b : Fin 9 := ⟨col.val / 4, by omega⟩
    set i : Fin 4 := ⟨col.val % 4, by omega⟩
    have hpos : -(b65k_poleOrder b : ℤ) < 0 := by
      have : 0 < b65k_poleOrder b := b65q_poleOrder_pos b
      omega
    have e1 := b65q_qVector_fixed_coeff t node w d (b65k_poleIndex b) htm i _ hpos
    have e2 := b65q_qVector_fixed_coeff t node w d' (b65k_poleIndex b) htm i _ hpos
    rw [b65q_principal_extract t (fun i : Fin 36 ↦ d ⟨i.val, by omega⟩) htf b i] at e1
    rw [b65q_principal_extract t (fun i : Fin 36 ↦ d' ⟨i.val, by omega⟩) htf b i] at e2
    rw [h] at e1
    have hc : (⟨col.val, by omega⟩ : Fin 48) = ⟨4 * b.val + i.val, by omega⟩ := by
      ext; show col.val = 4 * (col.val / 4) + col.val % 4; omega
    rw [hc]
    exact e1.symm.trans e2
  have hbeta : ∀ x, b65q_beta node d x = b65q_beta node d' x := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, w x i ≠ 0 := by
      by_contra h0; push_neg at h0; exact hw x (funext h0)
    have e1 := b65q_qVector_residue t node w d htm htmm x i
    have e2 := b65q_qVector_residue t node w d' htm htmm x i
    rw [h] at e1
    exact mul_right_cancel₀ hi (e1.symm.trans e2)
  have hv : ∀ e : Fin 2, ∀ v : Fin 6, d ⟨36 + 6 * e.val + v.val, by omega⟩ =
      d' ⟨36 + 6 * e.val + v.val, by omega⟩ := by
    intro e
    have := b65q_vandermonde node e (hnode e)
      (fun v ↦ d ⟨36 + 6 * e.val + v.val, by omega⟩ - d' ⟨36 + 6 * e.val + v.val, by omega⟩)
      (fun x hx ↦ by
        have hxe : b65q_fibreIndex x = e := (Finset.mem_filter.mp hx).2
        have := hbeta x
        simp only [b65q_beta, hxe] at this
        simp only [sub_mul, Finset.sum_sub_distrib, this, sub_self])
    intro v
    have := congrFun this v
    simpa [sub_eq_zero] using this
  funext col
  by_cases hc : col.val < 36
  · exact hfix ⟨col.val, hc⟩
  · set e : Fin 2 := ⟨(col.val - 36) / 6, by omega⟩
    set v : Fin 6 := ⟨(col.val - 36) % 6, by omega⟩
    have hcol : col = ⟨36 + 6 * e.val + v.val, by omega⟩ := by
      ext; show col.val = 36 + 6 * ((col.val - 36) / 6) + (col.val - 36) % 6; omega
    rw [hcol]; exact hv e v

/-- **The differential dictionary** on a good disc. -/
theorem b65q_dictionary_on {p : Fin 12 → ℂ} (O : b65p_Outputs p) {ε : ℝ} (hε : ε ≤ O.radius)
    (hgood : ∀ θ ∈ Metric.ball (0 : ℂ) ε,
      (∀ k i, (b65q_cmp O.residue θ k i).det ≠ 0) ∧ ∀ x, b65q_nrm O.residue θ x ≠ 0) :
    ∀ θ ∈ Metric.ball (0 : ℂ) ε,
      ∀ H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ k : Fin 4, ∃ δ : ℝ, 0 < δ ∧
        (∀ i j : Fin 4,
          AnalyticOnNhd ℂ (fun s ↦ H k s i j) (Metric.ball (b65p_fixedPole k) δ)) ∧
        H k (b65p_fixedPole k) = 1 ∧
        ∀ s ∈ Metric.ball (b65p_fixedPole k) δ, ∀ i j : Fin 4,
          (s - b65p_fixedPole k) * deriv (fun s ↦ H k s i j) s =
            (diagonal (b65p_exponents k) * H k s - H k s * diagonal (b65p_exponents k) +
              (s - b65p_fixedPole k) • ((b65q_basis O.residue θ k)⁻¹ *
                b65q_regular (b65p_poles p θ) (b65q_res O.residue θ) k s *
                  b65q_basis O.residue θ k * H k s)) i j) →
      b65q_rSpace (b65p_poles p θ) (b65q_basis O.residue θ) H =
          b65q_principal (b65p_poles p θ) '' {c | b65q_rFamily p O.residue θ *ᵥ c = 0} ∧
      b65q_qSpace (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) H =
          b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) ''
            {d | b65q_qFamily p O.residue θ *ᵥ d = 0} ∧
      Function.Injective (b65q_principal (b65p_poles p θ)) ∧
      Function.Injective (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ)) := by
  intro θ hθ H hH
  have hθr : θ ∈ Metric.ball (0 : ℂ) O.radius := Metric.ball_subset_ball hε hθ
  have hinj := O.poles_injective θ hθr
  have htf : ∀ k b', b' ≠ k → b65p_poles p θ (Sum.inl k) ≠ b65p_poles p θ (Sum.inl b') :=
    fun k b' hb h ↦ hb (Sum.inl_injective (hinj h)).symm
  have htm : ∀ k x, b65p_poles p θ (Sum.inl k) ≠ b65p_poles p θ (Sum.inr x) :=
    fun k x h ↦ Sum.inl_ne_inr (hinj h)
  have htmm : ∀ x y, y ≠ x → b65p_poles p θ (Sum.inr x) ≠ b65p_poles p θ (Sum.inr y) :=
    fun x y hxy h ↦ hxy (Sum.inr_injective (hinj h)).symm
  have hne : ∀ k q, q ≠ Sum.inl k → b65p_poles p θ (Sum.inl k) ≠ b65p_poles p θ q :=
    fun k q hq h ↦ hq (hinj h).symm
  obtain ⟨-, -, hpt⟩ := b65q_normalizations_on O hε hgood
  obtain ⟨hfixed, hmoving⟩ := hpt θ hθ
  have hP : ∀ k, IsUnit (b65q_basis O.residue θ k) := fun k ↦ (hfixed k).1
  have hinj0 := O.poles_injective 0 (Metric.mem_ball_self O.radius_pos)
  have hnode : ∀ e, Set.InjOn p (b65q_fibreSet e) := fun e x _ y _ hxy ↦ by
    have : b65p_poles p 0 (Sum.inr x) = b65p_poles p 0 (Sum.inr y) := by
      simpa [b65p_poles] using hxy
    exact Sum.inr_injective (hinj0 this)
  have hτ : ∀ x, Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) ≠ 0 := fun x ↦ by
    rw [b65q_trace_zero_inr]; exact_mod_cast b65q_BQ_trace_ne _
  have hwA : ∀ x v, b65q_res O.residue θ (Sum.inr x) *ᵥ v = 0 →
      v ⬝ᵥ b65q_left O.residue θ x = 0 := by
    intro x v hv
    have h1 := (hmoving x).2.1
    have h2 : (b65q_left O.residue θ x ᵥ* b65q_res O.residue θ (Sum.inr x)) ⬝ᵥ v = 0 := by
      rw [← Matrix.dotProduct_mulVec, hv, dotProduct_zero]
    rw [h1, smul_dotProduct, smul_eq_mul] at h2
    rw [dotProduct_comm]
    exact (mul_eq_zero.mp h2).resolve_left (hτ x)
  have hperp : ∀ x (ρ : Fin 4 → ℂ), (∀ v, b65q_res O.residue θ (Sum.inr x) *ᵥ v = 0 →
      v ⬝ᵥ ρ = 0) → ∃ β : ℂ, ρ = β • b65q_left O.residue θ x := fun x ρ hρ ↦
    b65q_rank_one_perp _ _ (hτ x) (b65q_rank_one_flow O x θ hθr)
      (b65q_trace_flow O (Sum.inr x) θ hθr) _ (hmoving x).1 (hmoving x).2.1 ρ hρ
  refine ⟨?_, ?_, b65q_principal_injective _ htf,
    b65q_qVector_injective _ p _ htf htm htmm hnode (fun x ↦ (hmoving x).1)⟩
  · refine b65q_rSpace_char _ _ _ H htf htm hP fun k r ↦ ?_
    obtain ⟨δ, hδ, han, h1, hode⟩ := hH k
    exact (b65q_gauge_cond (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) k
      (hne k) (hP k) (H k) (fun i j ↦ han i j _ (Metric.mem_ball_self hδ)) h1
      (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hδ) fun s hs ↦ hode s hs)).1
        (b65q_rFloor k) (b65q_rFloor_compat k) r
  · refine b65q_qSpace_char _ _ _ H p _ htf htm htmm hP hnode hperp hwA fun k q ↦ ?_
    obtain ⟨δ, hδ, han, h1, hode⟩ := hH k
    exact (b65q_gauge_cond (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) k
      (hne k) (hP k) (H k) (fun i j ↦ han i j _ (Metric.mem_ball_self hδ)) h1
      (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hδ) fun s hs ↦ hode s hs)).2
        (b65q_qFloor k) (b65q_qFloor_compat k) q

end HodgeLean.Foundations.Program
