import HodgeLean.Foundations.Program.KernelFramesFamilyLaurent

/-! # B6-5 stage 5d, family part: polynomial numerators of kernel pairs

A rational function whose Laurent expansions are all power series is a polynomial
(`b65q_denom_eq_one`). For kernel vectors of the two systems, the order conditions encoded by
the rows and the duality of the coefficient series give nonnegative orders of `D qᵀr` at every
point (`b65q_product_ge`); the infinity rows and the valuation at infinity bound its degree by
nine (`b65q_product_poly`). At `θ = 0` the frame products and the numerator array are the casts
of the printed ones.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Polynomial Matrix
open scoped LaurentSeries RatFunc
namespace HodgeLean.Foundations.Program

theorem b65q_ge_one_of_root (a : ℂ) (g : ℂ[X]) (hg : g.eval a = 0) :
    b65q_ge (b65q_L a (algebraMap ℂ[X] (RatFunc ℂ) g)) 1 := by
  rw [b65q_L_algebraMap, b65q_ge_iff]
  intro m hm
  rw [b65q_ofPS_coeff]
  split_ifs with h
  · rw [show m.toNat = 0 by omega, Polynomial.coeff_coe, taylor_coeff_zero, hg]
  · rfl

/-- **A rational function whose Laurent expansions are all power series is a polynomial.** -/
theorem b65q_denom_eq_one (f : RatFunc ℂ) (h : ∀ a, b65q_ge (b65q_L a f) 0) : f.denom = 1 := by
  by_contra hd
  have hmon : f.denom.Monic := RatFunc.monic_denom f
  have hdeg : f.denom.degree ≠ 0 := by
    intro h0
    exact hd (Polynomial.eq_one_of_monic_natDegree_zero hmon
      (natDegree_eq_zero_iff_degree_le_zero.mpr h0.le))
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom hdeg
  have hnum : f.num.eval a ≠ 0 := by
    intro h0
    have hc := RatFunc.isCoprime_num_denom f
    have h1 : X - C a ∣ f.num := dvd_iff_isRoot.mpr h0
    have h2 : X - C a ∣ f.denom := dvd_iff_isRoot.mpr ha
    exact not_isUnit_X_sub_C a (hc.isUnit_of_dvd' h1 h2)
  have hden : algebraMap ℂ[X] (RatFunc ℂ) f.denom ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hfd : f * algebraMap ℂ[X] (RatFunc ℂ) f.denom = algebraMap ℂ[X] (RatFunc ℂ) f.num := by
    calc f * algebraMap ℂ[X] (RatFunc ℂ) f.denom =
        algebraMap ℂ[X] (RatFunc ℂ) f.num / algebraMap ℂ[X] (RatFunc ℂ) f.denom *
          algebraMap ℂ[X] (RatFunc ℂ) f.denom := by rw [RatFunc.num_div_denom]
      _ = _ := div_mul_cancel₀ _ hden
  have hL := congrArg (b65q_L a) hfd
  rw [map_mul] at hL
  have hge := b65q_ge_mul (h a) (b65q_ge_one_of_root a f.denom ha)
  rw [hL, zero_add, b65q_ge_iff] at hge
  have := hge 0 (by norm_num)
  rw [b65q_L_algebraMap, b65q_ofPS_coeff, if_pos le_rfl, show (0 : ℤ).toNat = 0 from rfl,
    Polynomial.coeff_coe, taylor_coeff_zero] at this
  exact hnum this

theorem b65q_ge_L_principal_off (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (a : ℂ)
    (ha : ∀ k, a ≠ t (Sum.inl k)) (i : Fin 4) : b65q_ge (b65q_L a (b65q_principal t c i)) 0 := by
  simp only [b65q_principal, map_sum, b65q_L_div]
  refine b65q_ge_sum _ fun b _ ↦ ?_
  have h := b65q_ge_mul (b65q_ge_C (c ⟨4 * b.val + i.val, by omega⟩))
    (b65q_ge_L_inv_pow a (t (Sum.inl (b65k_poleIndex b))) (b65k_poleOrder b))
  rw [if_neg (ha _)] at h
  simpa using h

theorem b65q_ge_L_betaPart_at (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (x : Fin 12) (hx : ∀ y, y ≠ x → t (Sum.inr x) ≠ t (Sum.inr y)) (i : Fin 4) :
    b65q_ge (b65q_L (t (Sum.inr x)) (b65q_betaPart t node w d i)) (-1) := by
  simp only [b65q_betaPart, map_sum]
  refine b65q_ge_sum _ fun y _ ↦ ?_
  rw [← pow_one (RatFunc.X - RatFunc.C (t (Sum.inr y))), b65q_L_div]
  have h := b65q_ge_mul (b65q_ge_C ((∑ v : Fin 6,
      d ⟨36 + 6 * (b65q_fibreIndex y).val + v.val, by omega⟩ * node y ^ v.val) * w y i))
    (b65q_ge_L_inv_pow (t (Sum.inr x)) (t (Sum.inr y)) 1)
  refine b65q_ge_mono h ?_
  split_ifs <;> simp

theorem b65q_denominator_eval_moving (t : Fin 4 ⊕ Fin 12 → ℂ) (x : Fin 12) :
    (b65q_denominator t).eval (t (Sum.inr x)) = 0 := by
  rw [b65q_denominator, eval_mul, eval_prod]
  rw [Finset.prod_eq_zero (Finset.mem_univ x) (by simp), mul_zero]

theorem b65q_denominator_eval_zero (t : Fin 4 ⊕ Fin 12 → ℂ) : (b65q_denominator t).eval 0 = 0 := by
  simp [b65q_denominator]

/-- **Local orders of the numerator product.** For kernel vectors of the two systems, the
product `D qᵀr` has nonnegative order at every point. -/
theorem b65q_product_ge (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (c : Fin 36 → ℂ) (d : Fin 48 → ℂ)
    (htf : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b'))
    (htm : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x))
    (htmm : ∀ x y, y ≠ x → t (Sum.inr x) ≠ t (Sum.inr y)) (ht0 : t (Sum.inl 0) = 0)
    (hP : ∀ k, P k * (P k)⁻¹ = 1)
    (hc : b65q_rSystem t A P *ᵥ c = 0) (hd : b65q_qSystem t A P node w *ᵥ d = 0) (a : ℂ) :
    b65q_ge (b65q_L a (b65q_product t node w c d)) 0 := by
  unfold b65q_product
  rw [map_mul]
  by_cases hf : ∃ k, a = t (Sum.inl k)
  · obtain ⟨k, rfl⟩ := hf
    have hpair := b65q_KL_pair (t (Sum.inl k)) (b65q_qCoeff t A P k) (b65q_rCoeff t A P k)
      (b65q_coeff_pair t A P k (hP k)) (b65q_qVector t node w d) (b65q_principal t c)
    rw [← hpair]
    have hS : b65q_ge (∑ j : Fin 4, b65q_KL (t (Sum.inl k)) (b65q_qCoeff t A P k)
        (b65q_qVector t node w d) j * b65q_KL (t (Sum.inl k)) (b65q_rCoeff t A P k)
          (b65q_principal t c) j) (if k = 0 then -1 else 0) := by
      refine b65q_ge_sum _ fun j _ ↦ ?_
      exact b65q_ge_mono (b65q_ge_mul (b65q_q_order t A P node w d hd htf htm k j)
        (b65q_r_order t A P c hc htf k j)) (by have := b65q_floor_sum k j; omega)
    have hD : b65q_ge (b65q_L (t (Sum.inl k)) (algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator t)))
        (if k = 0 then 1 else 0) := by
      split_ifs with hk
      · subst hk; rw [ht0]; exact b65q_ge_one_of_root 0 _ (b65q_denominator_eval_zero t)
      · exact b65q_ge_L_poly _ _
    exact b65q_ge_mono (b65q_ge_mul hD hS) (by split_ifs <;> norm_num)
  · push_neg at hf
    have hr : ∀ j, b65q_ge (b65q_L a (b65q_principal t c j)) 0 := fun j ↦
      b65q_ge_L_principal_off t c a hf j
    have hq0 : ∀ j, b65q_ge (b65q_L a (b65q_principal t (fun i ↦ d ⟨i.val, by omega⟩) j)) 0 :=
      fun j ↦ b65q_ge_L_principal_off t _ a hf j
    by_cases hm : ∃ x, a = t (Sum.inr x)
    · obtain ⟨x, rfl⟩ := hm
      have hq : ∀ j, b65q_ge (b65q_L (t (Sum.inr x)) (b65q_qVector t node w d j)) (-1) := by
        intro j
        rw [b65q_qVector_eq, map_add]
        exact b65q_ge_add (b65q_ge_mono (hq0 j) (by norm_num))
          (b65q_ge_L_betaPart_at t node w d x (htmm x) j)
      have hS : b65q_ge (b65q_L (t (Sum.inr x)) (∑ j : Fin 4, b65q_qVector t node w d j *
          b65q_principal t c j)) (-1) := by
        rw [map_sum]
        refine b65q_ge_sum _ fun j _ ↦ ?_
        rw [map_mul]
        simpa using b65q_ge_mul (hq j) (hr j)
      have hD := b65q_ge_one_of_root (t (Sum.inr x)) _ (b65q_denominator_eval_moving t x)
      simpa using b65q_ge_mul hD hS
    · push_neg at hm
      have hS : b65q_ge (b65q_L a (∑ j : Fin 4, b65q_qVector t node w d j *
          b65q_principal t c j)) 0 := by
        rw [map_sum]
        refine b65q_ge_sum _ fun j _ ↦ ?_
        rw [map_mul, b65q_qVector_eq, map_add]
        simpa using b65q_ge_mul (b65q_ge_add (hq0 j) (b65q_ge_L_betaPart t node w d a hm j)) (hr j)
      simpa using b65q_ge_mul (b65q_ge_L_poly a (b65q_denominator t)) hS

attribute [local instance] Classical.propDecidable

local notation "𝓋" => RatFunc.inftyValuation ℂ

theorem b65q_v_poly (g : ℂ[X]) (hg : g ≠ 0) :
    𝓋 (algebraMap ℂ[X] (RatFunc ℂ) g) = WithZero.exp (g.natDegree : ℤ) := by
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial _ hg]

theorem b65q_v_X_sub (t : ℂ) : 𝓋 (RatFunc.X - RatFunc.C t) = WithZero.exp 1 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub, b65q_v_poly _ (X_sub_C_ne_zero t),
    natDegree_X_sub_C]
  rfl

theorem b65q_v_C_le (c : ℂ) : 𝓋 (RatFunc.C c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [RatFunc.inftyValuation.C _ hc]

theorem b65q_v_inv_pow (t : ℂ) (m : ℕ) :
    𝓋 ((RatFunc.X - RatFunc.C t) ^ m)⁻¹ = WithZero.exp (-(m : ℤ)) := by
  rw [map_inv₀, map_pow, b65q_v_X_sub, ← WithZero.exp_nsmul, ← WithZero.exp_neg]
  simp

theorem b65q_v_simple (t : ℂ) :
    𝓋 (1 / (RatFunc.X - RatFunc.C t) - 1 / RatFunc.X) ≤ WithZero.exp (-2) := by
  have h1 := b65q_X_sub_C_ne t
  have h2 : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have : 1 / (RatFunc.X - RatFunc.C t) - 1 / RatFunc.X =
      RatFunc.C t * ((RatFunc.X - RatFunc.C t) ^ 1)⁻¹ * ((RatFunc.X - RatFunc.C 0) ^ 1)⁻¹ := by
    simp only [map_zero, sub_zero, pow_one]
    field_simp
    ring
  rw [this, map_mul, map_mul, b65q_v_inv_pow, b65q_v_inv_pow]
  calc 𝓋 (RatFunc.C t) * WithZero.exp (-((1 : ℕ) : ℤ)) * WithZero.exp (-((1 : ℕ) : ℤ)) ≤
      1 * WithZero.exp (-((1 : ℕ) : ℤ)) * WithZero.exp (-((1 : ℕ) : ℤ)) := by
        gcongr; exact b65q_v_C_le t
    _ = WithZero.exp (-2) := by rw [one_mul, ← WithZero.exp_add]; norm_num

theorem b65q_v_sum_le {ι : Type*} (S : Finset ι) (f : ι → RatFunc ℂ) (γ : WithZero (Multiplicative ℤ))
    (h : ∀ i ∈ S, 𝓋 (f i) ≤ γ) : 𝓋 (∑ i ∈ S, f i) ≤ γ :=
  Valuation.map_sum_le _ h

theorem b65q_v_principal (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (j : Fin 4) :
    𝓋 (b65q_principal t c j - RatFunc.C (∑ b : Fin 9, (if b65k_poleOrder b = 1 then
      c ⟨4 * b.val + j.val, by omega⟩ else 0)) * (1 / RatFunc.X)) ≤ WithZero.exp (-2) := by
  have heq : b65q_principal t c j - RatFunc.C (∑ b : Fin 9, (if b65k_poleOrder b = 1 then
      c ⟨4 * b.val + j.val, by omega⟩ else 0)) * (1 / RatFunc.X) = ∑ b : Fin 9, RatFunc.C (c ⟨4 * b.val + j.val, by omega⟩) *
      (((RatFunc.X - RatFunc.C (t (Sum.inl (b65k_poleIndex b)))) ^ b65k_poleOrder b)⁻¹ -
        if b65k_poleOrder b = 1 then 1 / RatFunc.X else 0) := by
    have key : ∀ b : Fin 9, RatFunc.C (c ⟨4 * b.val + j.val, by omega⟩) /
        (RatFunc.X - RatFunc.C (t (Sum.inl (b65k_poleIndex b)))) ^ b65k_poleOrder b =
        RatFunc.C (c ⟨4 * b.val + j.val, by omega⟩) *
          (((RatFunc.X - RatFunc.C (t (Sum.inl (b65k_poleIndex b)))) ^ b65k_poleOrder b)⁻¹ -
            if b65k_poleOrder b = 1 then 1 / RatFunc.X else 0) +
        RatFunc.C (if b65k_poleOrder b = 1 then c ⟨4 * b.val + j.val, by omega⟩ else 0) *
          (1 / RatFunc.X) := by
      intro b; split_ifs <;> simp [div_eq_mul_inv] <;> ring
    rw [b65q_principal, Finset.sum_congr rfl fun b _ ↦ key b, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← map_sum, add_sub_cancel_right]
  rw [heq]
  refine b65q_v_sum_le _ _ _ fun b _ ↦ ?_
  rw [map_mul]
  have hb : 𝓋 (((RatFunc.X - RatFunc.C (t (Sum.inl (b65k_poleIndex b)))) ^ b65k_poleOrder b)⁻¹ -
      if b65k_poleOrder b = 1 then 1 / RatFunc.X else 0) ≤ WithZero.exp (-2) := by
    split_ifs with h1
    · rw [h1, pow_one, ← one_div]; exact b65q_v_simple _
    · rw [sub_zero, b65q_v_inv_pow]
      have h2 : 2 ≤ b65k_poleOrder b := by
        have : 1 ≤ b65k_poleOrder b := by fin_cases b <;> decide
        omega
      exact WithZero.exp_le_exp.mpr (by omega)
  calc 𝓋 (RatFunc.C _) * 𝓋 _ ≤ 1 * WithZero.exp (-2) := by gcongr; exact b65q_v_C_le _
    _ = _ := one_mul _

theorem b65q_v_betaPart (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (j : Fin 4) :
    𝓋 (b65q_betaPart t node w d j - RatFunc.C (∑ x : Fin 12, (∑ v : Fin 6,
      d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j) *
        (1 / RatFunc.X)) ≤ WithZero.exp (-2) := by
  rw [b65q_betaPart, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine b65q_v_sum_le _ _ _ fun x _ ↦ ?_
  rw [div_eq_mul_inv, ← mul_sub, map_mul, ← one_div]
  calc 𝓋 (RatFunc.C _) * 𝓋 _ ≤ 1 * WithZero.exp (-2) := by
        gcongr
        · exact b65q_v_C_le _
        · exact b65q_v_simple _
    _ = _ := one_mul _

theorem b65q_infinityEntry_e36 (i0 : Fin 4) (b : Fin 9) (i : Fin 4) :
    b65q_infinityEntry i0 (b65q_e36 (b, i)) = if b65k_poleOrder b = 1 ∧ i = i0 then 1 else 0 := by
  have h1 : (⟨(b65q_e36 (b, i)).val / 4, by omega⟩ : Fin 9) = b := by
    ext; simp only [b65q_e36_val]; omega
  unfold b65q_infinityEntry
  rw [h1]
  congr 1
  apply propext
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, Fin.ext (by rw [b65q_e36_val] at h'; omega)⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, by rw [b65q_e36_val]; omega⟩

theorem b65q_e36_eq (b : Fin 9) (j : Fin 4) :
    b65q_e36 (b, j) = ⟨4 * b.val + j.val, by omega⟩ := by
  ext; show j.val + 4 * b.val = 4 * b.val + j.val; omega

theorem b65q_rSystem_inf (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : Fin 36 → ℂ) (j : Fin 4) :
    (b65q_rSystem t A P *ᵥ c) ⟨41 + j.val, by omega⟩ =
      ∑ b : Fin 9, (if b65k_poleOrder b = 1 then c ⟨4 * b.val + j.val, by omega⟩ else 0) := by
  have hj : (⟨41 + j.val - 41, by omega⟩ : Fin 4) = j := by ext; simp
  unfold Matrix.mulVec dotProduct
  rw [← Equiv.sum_comp b65q_e36, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [b65q_rSystem, show ¬ (41 + j.val < 41) by omega, dif_neg, not_false_eq_true, hj,
    b65q_infinityEntry_e36]
  by_cases hb : b65k_poleOrder b = 1
  · simp [hb, b65q_e36_eq]
  · simp [hb]

theorem b65q_qSystem_inf_left (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (j : Fin 4) (c : Fin 36) :
    b65q_qSystem t A P node w ⟨53 + j.val, by omega⟩ (Fin.castAdd 12 c) = b65q_infinityEntry j c := by
  unfold b65q_qSystem
  rw [dif_neg (by simp), dif_pos (by simp)]
  congr 1 <;> ext <;> simp

theorem b65q_qSystem_inf_right (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (j : Fin 4) (e : Fin 2) (v : Fin 6) :
    b65q_qSystem t A P node w ⟨53 + j.val, by omega⟩ (Fin.natAdd 36 (b65q_e12 (e, v))) =
      b65q_betaInfinity node w j e v := by
  unfold b65q_qSystem
  rw [dif_neg (by simp), dif_neg (by simp)]
  congr 1 <;> ext <;> simp [b65q_e12_val] <;> omega

theorem b65q_qSystem_inf (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (j : Fin 4) :
    (b65q_qSystem t A P node w *ᵥ d) ⟨53 + j.val, by omega⟩ =
      ∑ b : Fin 9, (if b65k_poleOrder b = 1 then d ⟨4 * b.val + j.val, by omega⟩ else 0) +
      ∑ x : Fin 12, (∑ v : Fin 6,
        d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j := by
  unfold Matrix.mulVec dotProduct
  rw [Fin.sum_univ_add (a := 36) (b := 12)]
  congr 1
  · rw [← Equiv.sum_comp b65q_e36, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    simp only [b65q_qSystem_inf_left, b65q_infinityEntry_e36]
    by_cases hb : b65k_poleOrder b = 1
    · simp only [hb, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      congr 1; ext; simp [b65q_e36_val]; omega
    · simp [hb]
  · rw [← Equiv.sum_comp b65q_e12, Fintype.sum_prod_type]
    simp only [b65q_qSystem_inf_right, b65q_betaInfinity, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_congr rfl fun e _ ↦ Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have : (⟨36 + (b65q_e12 (b65q_fibreIndex x, v)).val, by omega⟩ : Fin 48) =
        ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ := by
      ext; simp only [b65q_e12_val]; omega
    simp only [Fin.natAdd] at *
    rw [this]; ring

theorem b65q_v_denominator (t : Fin 4 ⊕ Fin 12 → ℂ) :
    𝓋 (algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator t)) = WithZero.exp 13 := by
  have hm : (∏ x : Fin 12, (X - C (t (Sum.inr x)))).Monic :=
    monic_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _
  have hD : (b65q_denominator t).Monic := monic_X.mul hm
  have hdeg : (b65q_denominator t).natDegree = 13 := by
    rw [b65q_denominator, (monic_X).natDegree_mul hm, natDegree_X,
      natDegree_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _]
    simp
  rw [b65q_v_poly _ hD.ne_zero, hdeg]
  rfl

theorem b65q_v_split (f g : RatFunc ℂ) (γ : WithZero (Multiplicative ℤ)) (hf : 𝓋 (f - g) ≤ γ)
    (hg : g = 0) : 𝓋 f ≤ γ := by
  rw [hg, sub_zero] at hf; exact hf

/-- **Numerators of kernel pairs.** For kernel vectors of the two systems, `D qᵀr` is a polynomial
of degree at most nine. -/
theorem b65q_product_poly (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (c : Fin 36 → ℂ) (d : Fin 48 → ℂ)
    (htf : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b'))
    (htm : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x))
    (htmm : ∀ x y, y ≠ x → t (Sum.inr x) ≠ t (Sum.inr y)) (ht0 : t (Sum.inl 0) = 0)
    (hP : ∀ k, P k * (P k)⁻¹ = 1)
    (hc : b65q_rSystem t A P *ᵥ c = 0) (hd : b65q_qSystem t A P node w *ᵥ d = 0) :
    (b65q_product t node w c d).denom = 1 ∧ (b65q_product t node w c d).num.natDegree ≤ 9 := by
  have hden := b65q_denom_eq_one _ (b65q_product_ge t A P node w c d htf htm htmm ht0 hP hc hd)
  refine ⟨hden, ?_⟩
  have hr : ∀ j, 𝓋 (b65q_principal t c j) ≤ WithZero.exp (-2) := by
    intro j
    refine b65q_v_split _ _ _ (b65q_v_principal t c j) ?_
    have := congrFun hc ⟨41 + j.val, by omega⟩
    rw [b65q_rSystem_inf] at this
    rw [show (∑ b : Fin 9, if b65k_poleOrder b = 1 then c ⟨4 * b.val + j.val, by omega⟩ else 0) = 0
      from this]
    simp
  have hq : ∀ j, 𝓋 (b65q_qVector t node w d j) ≤ WithZero.exp (-2) := by
    intro j
    have h0 := congrFun hd ⟨53 + j.val, by omega⟩
    rw [b65q_qSystem_inf] at h0
    simp only [Pi.zero_apply] at h0
    have heq : b65q_qVector t node w d j =
        (b65q_principal t (fun i ↦ d ⟨i.val, by omega⟩) j - RatFunc.C (∑ b : Fin 9,
          (if b65k_poleOrder b = 1 then d ⟨4 * b.val + j.val, by omega⟩ else 0)) * (1 / RatFunc.X)) +
        (b65q_betaPart t node w d j - RatFunc.C (∑ x : Fin 12, (∑ v : Fin 6,
          d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j) *
            (1 / RatFunc.X)) := by
      rw [b65q_qVector_eq]
      have : RatFunc.C (∑ b : Fin 9,
          (if b65k_poleOrder b = 1 then d ⟨4 * b.val + j.val, by omega⟩ else 0)) * (1 / RatFunc.X) +
          RatFunc.C (∑ x : Fin 12, (∑ v : Fin 6,
          d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j) *
            (1 / RatFunc.X) = 0 := by
        rw [← add_mul, ← map_add, h0]; simp
      linear_combination this
    rw [heq]
    exact (Valuation.map_add _ _ _).trans (max_le (b65q_v_principal t _ j) (b65q_v_betaPart t node w d j))
  have hS : 𝓋 (∑ j : Fin 4, b65q_qVector t node w d j * b65q_principal t c j) ≤ WithZero.exp (-4) := by
    refine b65q_v_sum_le _ _ _ fun j _ ↦ ?_
    rw [map_mul]
    calc 𝓋 (b65q_qVector t node w d j) * 𝓋 (b65q_principal t c j) ≤
        WithZero.exp (-2) * WithZero.exp (-2) := by gcongr <;> [exact hq j; exact hr j]
      _ = WithZero.exp (-4) := by rw [← WithZero.exp_add]; norm_num
  have hv : 𝓋 (b65q_product t node w c d) ≤ WithZero.exp 9 := by
    unfold b65q_product
    rw [map_mul, b65q_v_denominator]
    calc WithZero.exp 13 * 𝓋 _ ≤ WithZero.exp 13 * WithZero.exp (-4) := by gcongr
      _ = WithZero.exp 9 := by rw [← WithZero.exp_add]; norm_num
  have hf : b65q_product t node w c d =
      algebraMap ℂ[X] (RatFunc ℂ) (b65q_product t node w c d).num := by
    conv_lhs => rw [← RatFunc.num_div_denom (b65q_product t node w c d)]
    rw [hden, map_one, div_one]
  by_cases hn : (b65q_product t node w c d).num = 0
  · rw [hn]; simp
  · rw [hf, b65q_v_poly _ hn] at hv
    have := WithZero.exp_le_exp.mp hv
    exact_mod_cast this

theorem b65q_num_div_coprime (p q : ℂ[X]) (hq : q.Monic) (h : IsCoprime p q) :
    (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q).num = p := by
  have hg : gcd p q = 1 := by
    rw [← normalize_gcd, normalize_eq_one]
    exact gcd_isUnit_iff_isRelPrime.mpr h.isRelPrime
  rw [RatFunc.num_div, hg, EuclideanDomain.div_one, EuclideanDomain.div_one, hq.leadingCoeff,
    inv_one, map_one, one_mul]

theorem b65q_num_castRat (f : RatFunc ℚ) : (b65q_castRat f).num = f.num.map (Rat.castHom ℂ) := by
  rw [b65q_castRat, RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply]
  exact b65q_num_div_coprime _ _ ((RatFunc.monic_denom f).map _)
    ((RatFunc.isCoprime_num_denom f).map (Polynomial.mapRingHom (Rat.castHom ℂ)))

theorem b65q_denominator_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    b65q_denominator (b65p_poles p 0) = b65k_baseDenominator.map (Rat.castHom ℂ) := by
  have h0 := b65q_fibreC_map 0
  have h1 := b65q_fibreC_map 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [b65k_baseDenominator, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_X, h0, h1,
    ← b65q_fibre_prod O 0, ← b65q_fibre_prod O 1, b65q_denominator, b65q_poles_zero, mul_assoc]
  refine congrArg (fun q ↦ X * q) ?_
  rw [← Finset.prod_fiberwise Finset.univ b65q_fibreIndex, Fin.prod_univ_two]
  simp only [Sum.elim_inr, b65q_fibreSet]

theorem b65q_frameProduct_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (a b : Fin 3) :
    b65q_frameProduct p O.residue 0 a b = b65q_castRat (b65k_baseProduct a b) := by
  rw [b65q_frameProduct, b65q_product, b65k_baseProduct, map_mul, b65q_castRat_algebraMap,
    ← b65q_denominator_zero O, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, b65q_qVector_frame_zero O, b65q_principal_frame_zero O]

theorem b65q_numMatrix_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    b65q_numMatrix p O.residue 0 = b65k_baseMatrix.map (Rat.castHom ℂ) := by
  ext i j
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective i
  simp only [b65q_numMatrix, b65k_baseMatrix, Matrix.map_apply, Equiv.symm_apply_apply,
    b65q_frameProduct_zero, b65q_num_castRat, Polynomial.coeff_map, b65k_baseNumerator]

theorem b65q_reconstruct (f : RatFunc ℂ) (hd : f.denom = 1) (hn : f.num.natDegree ≤ 9) :
    ∑ j : Fin 10, RatFunc.C (f.num.coeff j.val) * RatFunc.X ^ j.val = f := by
  have hf : f = algebraMap ℂ[X] (RatFunc ℂ) f.num := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [hd, map_one, div_one]
  conv_rhs => rw [hf, f.num.as_sum_range' 10 (by omega)]
  rw [map_sum, Fin.sum_univ_eq_sum_range (fun j ↦ RatFunc.C (f.num.coeff j) * RatFunc.X ^ j)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X]

theorem b65q_col_ker {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) (F : Matrix (Fin n) (Fin 3) ℂ)
    (h : S * F = 0) (a : Fin 3) : S *ᵥ (fun i ↦ F i a) = 0 := by
  ext r; have := congrFun (congrFun h r) a
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/-- **Family numerators** on a good disc. -/
theorem b65q_family_numerators_on {p : Fin 12 → ℂ} (O : b65p_Outputs p) {ε : ℝ}
    (hε : ε ≤ O.radius)
    (hgood : ∀ θ ∈ Metric.ball (0 : ℂ) ε,
      (∀ k i, (b65q_cmp O.residue θ k i).det ≠ 0) ∧ ∀ x, b65q_nrm O.residue θ x ≠ 0) :
    (∀ θ ∈ Metric.ball (0 : ℂ) ε, ∀ (c : Fin 36 → ℂ) (d : Fin 48 → ℂ),
        b65q_rFamily p O.residue θ *ᵥ c = 0 → b65q_qFamily p O.residue θ *ᵥ d = 0 →
        (b65q_product (b65p_poles p θ) p (b65q_left O.residue θ) c d).denom = 1 ∧
        (b65q_product (b65p_poles p θ) p (b65q_left O.residue θ) c d).num.natDegree ≤ 9) ∧
      (∀ θ ∈ Metric.ball (0 : ℂ) ε,
        b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 →
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0 →
        ∀ a b : Fin 3,
          (∑ j : Fin 10, RatFunc.C (b65q_numMatrix p O.residue θ (finProdFinEquiv (a, b)) j) *
            RatFunc.X ^ j.val) = b65q_frameProduct p O.residue θ a b) := by
  have hpoly : ∀ θ ∈ Metric.ball (0 : ℂ) ε, ∀ (c : Fin 36 → ℂ) (d : Fin 48 → ℂ),
      b65q_rFamily p O.residue θ *ᵥ c = 0 → b65q_qFamily p O.residue θ *ᵥ d = 0 →
      (b65q_product (b65p_poles p θ) p (b65q_left O.residue θ) c d).denom = 1 ∧
      (b65q_product (b65p_poles p θ) p (b65q_left O.residue θ) c d).num.natDegree ≤ 9 := by
    intro θ hθ c d hc hd
    have hθr : θ ∈ Metric.ball (0 : ℂ) O.radius := Metric.ball_subset_ball hε hθ
    have hinj := O.poles_injective θ hθr
    have hunit := ((b65q_normalizations_on O hε hgood).2.2 θ hθ).1
    exact b65q_product_poly (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) p
      (b65q_left O.residue θ) c d
      (fun k b' hb h ↦ hb (Sum.inl_injective (hinj h)).symm)
      (fun k x h ↦ Sum.inl_ne_inr (hinj h))
      (fun x y hxy h ↦ hxy (Sum.inr_injective (hinj h)).symm)
      (by simp [b65p_poles, b65p_fixedPole])
      (fun k ↦ Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (hunit k).1)) hc hd
  refine ⟨hpoly, fun θ hθ hr hq a b ↦ ?_⟩
  have h := hpoly θ hθ _ _ (b65q_col_ker _ _ hr a) (b65q_col_ker _ _ hq b)
  have hm : ∀ j : Fin 10, b65q_numMatrix p O.residue θ (finProdFinEquiv (a, b)) j =
      (b65q_frameProduct p O.residue θ a b).num.coeff j.val := fun j ↦ by
    simp only [b65q_numMatrix, Equiv.symm_apply_apply]
  simp only [hm]
  exact b65q_reconstruct _ h.1 h.2

end HodgeLean.Foundations.Program
