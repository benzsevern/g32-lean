import HodgeLean.Foundations.Program.KernelFramesFamilyOrders

/-! # B6-5 stage 5d, family part: tools for the differential dictionary

Meromorphic orders of single rational functions and of pairings, the Laurent coefficients of
principal-part vectors at their poles, residues orthogonal to the kernel of a rank-one residue,
Lagrange interpolation and Vandermonde uniqueness at the six nodes of a fibre, and valuation
bounds at infinity.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Polynomial Matrix Filter
open scoped LaurentSeries RatFunc Topology Nat
namespace HodgeLean.Foundations.Program

theorem b65q_merOrd_eval (f : RatFunc ℂ) (a : ℂ) :
    meromorphicOrderAt (fun s ↦ b65q_eval f s) a = (b65q_L a f).orderTop := by
  have := b65q_bridge (Finset.univ : Finset (Fin 1)) a (fun _ _ ↦ 1) (fun _ _ ↦ analyticAt_const)
    (fun _ ↦ f)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, b65q_T_const, map_one] at this
  simpa using this

theorem b65q_merOrd_dot (v : Fin 4 → ℂ) (q : Fin 4 → RatFunc ℂ) (a : ℂ) :
    meromorphicOrderAt (fun s ↦ v ⬝ᵥ fun i ↦ b65q_eval (q i) s) a =
      (∑ i, HahnSeries.C (v i) * b65q_L a (q i)).orderTop := by
  have := b65q_bridge (Finset.univ : Finset (Fin 4)) a (fun i _ ↦ v i)
    (fun _ _ ↦ analyticAt_const) q
  simp only [b65q_T_const, HahnSeries.ofPowerSeries_C] at this
  simpa [dotProduct] using this

theorem b65q_principal_coeff (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (k : Fin 4)
    (htf : ∀ b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) (i : Fin 4) (m : ℕ) (hm : 1 ≤ m) :
    (b65q_L (t (Sum.inl k)) (b65q_principal t c i)).coeff (-(m : ℤ)) =
      ∑ b : Fin 9, if b65k_poleIndex b = k ∧ b65k_poleOrder b = m then
        c ⟨4 * b.val + i.val, by omega⟩ else 0 := by
  simp only [b65q_principal, map_sum, b65q_L_div, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  by_cases hb : b65k_poleIndex b = k
  · rw [hb, b65q_L_inv_pow_eq, HahnSeries.coeff_single]
    by_cases hm' : b65k_poleOrder b = m
    · simp [hm']
    · rw [if_neg (by omega), if_neg (by tauto), mul_zero]
  · rw [b65q_L_inv_pow_ne (htf _ hb), b65q_ofPS_coeff, if_neg (by omega),
      if_neg (by tauto), mul_zero]

/-- The largest pole order allotted at each fixed pole. -/
def b65q_maxOrder : Fin 4 → ℕ := ![2, 3, 2, 2]

/-- The unknown slot of order `m` at the fixed pole `k`. -/
def b65q_slot : Fin 4 → Fin 4 → Fin 9 := ![![0, 0, 1, 1], ![2, 2, 3, 4], ![5, 5, 6, 6], ![7, 7, 8, 8]]

theorem b65q_slot_sum (k : Fin 4) (m : ℕ) (hm : 1 ≤ m) (f : Fin 9 → ℂ) :
    (∑ b : Fin 9, if b65k_poleIndex b = k ∧ b65k_poleOrder b = m then f b else 0) =
      if h : m ≤ b65q_maxOrder k then f (b65q_slot k ⟨m, by fin_cases k <;> simp_all [b65q_maxOrder] <;> omega⟩) else 0 := by
  rcases m with _ | _ | _ | _ | m
  · omega
  all_goals fin_cases k <;>
    simp [Fin.sum_univ_succ, b65k_poleIndex, b65k_poleOrder, b65q_maxOrder, b65q_slot]

/-- **Residues orthogonal to the kernel of a rank-one residue are multiples of `w`.** -/
theorem b65q_rank_one_perp (A : Matrix (Fin 4) (Fin 4) ℂ) (τ : ℂ) (hτ : τ ≠ 0)
    (hA : A * A = τ • A) (htr : Matrix.trace A = τ) (w : Fin 4 → ℂ) (hw : w ≠ 0)
    (hwA : w ᵥ* A = τ • w) (ρ : Fin 4 → ℂ) (hρ : ∀ v, A *ᵥ v = 0 → v ⬝ᵥ ρ = 0) :
    ∃ β : ℂ, ρ = β • w := by
  set E := τ⁻¹ • A with hE
  have hEE : E * E = E := by
    rw [hE, Matrix.smul_mul, Matrix.mul_smul, hA, smul_smul, smul_smul]
    congr 1; field_simp
  have hρE : ρ = ρ ᵥ* E := by
    have h1 : ∀ v, v ⬝ᵥ ρ = (E *ᵥ v) ⬝ᵥ ρ := by
      intro v
      have hv : A *ᵥ (v - E *ᵥ v) = 0 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hE, Matrix.mul_smul, hA, smul_smul,
          inv_mul_cancel₀ hτ, one_smul, sub_self]
      have := hρ _ hv
      rw [sub_dotProduct, sub_eq_zero] at this
      exact this
    ext i
    have := h1 (Pi.single i 1)
    simp only [Matrix.mulVec_single_one, dotProduct, Pi.single_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [this]
    simp [Matrix.vecMul, dotProduct, Matrix.col, mul_comm]
  set e : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) := (Eᵀ).mulVecLin
  have he : IsIdempotentElem e := by
    show e * e = e
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, ← Matrix.transpose_mul, hEE]
  have htrE : LinearMap.trace ℂ (Fin 4 → ℂ) e = 1 := by
    rw [show e = Matrix.toLin' Eᵀ from (Matrix.toLin'_apply' _).symm, Matrix.trace_toLin'_eq,
      Matrix.trace_transpose, hE, Matrix.trace_smul, htr, smul_eq_mul, inv_mul_cancel₀ hτ]
  have hrank : Module.finrank ℂ (LinearMap.range e) = 1 := by
    have := (LinearMap.IsIdempotentElem.isProj_range e he).trace
    rw [htrE] at this
    exact_mod_cast this.symm
  have hwmem : w ∈ LinearMap.range e := by
    refine ⟨w, ?_⟩
    show Eᵀ *ᵥ w = w
    rw [Matrix.mulVec_transpose, hE, Matrix.vecMul_smul, hwA, smul_smul, inv_mul_cancel₀ hτ,
      one_smul]
  have hρmem : ρ ∈ LinearMap.range e := by
    refine ⟨ρ, ?_⟩
    show Eᵀ *ᵥ ρ = ρ
    rw [Matrix.mulVec_transpose]; exact hρE.symm
  obtain ⟨β, hβ⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwmem⟩ : LinearMap.range e)
    (by simpa using hw)).mp hrank ⟨ρ, hρmem⟩
  exact ⟨β, by simpa using congrArg Subtype.val hβ.symm⟩

/-- **Interpolation at the six nodes of a fibre.** -/
theorem b65q_interpolate (node : Fin 12 → ℂ) (e : Fin 2)
    (hnode : Set.InjOn node (b65q_fibreSet e)) (β : Fin 12 → ℂ) :
    ∃ dv : Fin 6 → ℂ, ∀ x ∈ b65q_fibreSet e, ∑ v : Fin 6, dv v * node x ^ v.val = β x := by
  classical
  set L := Lagrange.interpolate (b65q_fibreSet e) node β
  have hdeg : L.natDegree < 6 := by
    have h := Lagrange.degree_interpolate_lt (r := β) hnode
    rw [b65q_fibreSet_card] at h
    by_cases hL : L = 0
    · rw [hL]; simp
    · exact (natDegree_lt_iff_degree_lt hL).mpr (by exact_mod_cast h)
  refine ⟨fun v ↦ L.coeff v, fun x hx ↦ ?_⟩
  rw [← Lagrange.eval_interpolate_at_node β hnode hx, eval_eq_sum_range' hdeg,
    Fin.sum_univ_eq_sum_range (fun v ↦ L.coeff v * node x ^ v)]

/-- **Uniqueness of the interpolating coefficients.** -/
theorem b65q_vandermonde (node : Fin 12 → ℂ) (e : Fin 2)
    (hnode : Set.InjOn node (b65q_fibreSet e)) (dv : Fin 6 → ℂ)
    (h : ∀ x ∈ b65q_fibreSet e, ∑ v : Fin 6, dv v * node x ^ v.val = 0) : dv = 0 := by
  classical
  set P : ℂ[X] := ∑ v : Fin 6, C (dv v) * X ^ v.val
  have hP : P = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      (f := fun x : b65q_fibreSet e ↦ node x)
    · intro x y hxy; exact Subtype.ext (hnode x.2 y.2 hxy)
    · intro x; simpa [P, eval_finset_sum] using h x x.2
    · rw [Fintype.card_coe, b65q_fibreSet_card]
      calc P.natDegree ≤ 5 := by
            refine natDegree_sum_le_of_forall_le _ _ fun v _ ↦ ?_
            exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
        _ < 6 := by norm_num
  funext v
  have := congrArg (fun p : ℂ[X] ↦ p.coeff v.val) hP
  simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single v (fun b _ hb ↦ by rw [if_neg (fun h ↦ hb (Fin.ext h.symm))]; simp)
    (by simp)] at this
  simpa using this

attribute [local instance] Classical.propDecidable in
theorem b65q_v_le_of_intDegree (f : RatFunc ℂ) (h : f = 0 ∨ f.intDegree ≤ -2) :
    RatFunc.inftyValuation ℂ f ≤ WithZero.exp (-2) := by
  rcases h with h | h
  · rw [h, map_zero]; exact zero_le'
  · by_cases hf : f = 0
    · rw [hf, map_zero]; exact zero_le'
    · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero ℂ hf]
      exact WithZero.exp_le_exp.mpr h

attribute [local instance] Classical.propDecidable in
theorem b65q_intDegree_of_v (f : RatFunc ℂ) (h : RatFunc.inftyValuation ℂ f ≤ WithZero.exp (-2)) :
    f = 0 ∨ f.intDegree ≤ -2 := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · right
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero ℂ hf] at h
    exact WithZero.exp_le_exp.mp h

attribute [local instance] Classical.propDecidable in
/-- A polynomial with negative valuation at infinity is zero. -/
theorem b65q_poly_zero_of_v (f : RatFunc ℂ) (hd : f.denom = 1)
    (h : RatFunc.inftyValuation ℂ f ≤ WithZero.exp (-1)) : f = 0 := by
  have hf : f = algebraMap ℂ[X] (RatFunc ℂ) f.num := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [hd, map_one, div_one]
  by_contra hne
  have hn : f.num ≠ 0 := by intro h0; apply hne; rw [hf, h0, map_zero]
  rw [hf, b65q_v_poly _ hn] at h
  have := WithZero.exp_le_exp.mp h
  omega

theorem b65q_poleIndex_order_inj (b b' : Fin 9) :
    (b65k_poleIndex b' = b65k_poleIndex b ∧ b65k_poleOrder b' = b65k_poleOrder b) ↔ b' = b := by
  revert b b'; decide

/-- **The Laurent coefficients of a principal-part vector are its unknowns.** -/
theorem b65q_principal_extract (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ)
    (htf : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) (b : Fin 9) (i : Fin 4) :
    (b65q_L (t (Sum.inl (b65k_poleIndex b))) (b65q_principal t c i)).coeff
      (-(b65k_poleOrder b : ℤ)) = c ⟨4 * b.val + i.val, by omega⟩ := by
  have h1 : 1 ≤ b65k_poleOrder b := by fin_cases b <;> decide
  rw [b65q_principal_coeff t c _ (htf _) i _ h1]
  simp only [b65q_poleIndex_order_inj]
  rw [Finset.sum_ite_eq']
  simp

theorem b65q_ge_L_principal_at (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (k : Fin 4)
    (htf : ∀ b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) (i : Fin 4) :
    b65q_ge (b65q_L (t (Sum.inl k)) (b65q_principal t c i)) (-(b65q_maxOrder k : ℤ)) := by
  simp only [b65q_principal, map_sum, b65q_L_div]
  refine b65q_ge_sum _ fun b _ ↦ ?_
  have h := b65q_ge_mul (b65q_ge_C (c ⟨4 * b.val + i.val, by omega⟩))
    (b65q_ge_L_inv_pow (t (Sum.inl k)) (t (Sum.inl (b65k_poleIndex b))) (b65k_poleOrder b))
  refine b65q_ge_mono h ?_
  split_ifs with h1
  · have hb : b65k_poleIndex b = k := by
      by_contra hb; exact htf _ hb h1
    have : b65k_poleOrder b ≤ b65q_maxOrder k := by
      subst hb; fin_cases b <;> decide
    omega
  · simp

attribute [local instance] Classical.propDecidable in
theorem b65q_v_principal_le (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (i : Fin 4) :
    RatFunc.inftyValuation ℂ (b65q_principal t c i) ≤ WithZero.exp (-1) := by
  simp only [b65q_principal]
  refine Valuation.map_sum_le _ fun b _ ↦ ?_
  rw [div_eq_mul_inv, map_mul, b65q_v_inv_pow]
  have h1 : 1 ≤ b65k_poleOrder b := by fin_cases b <;> decide
  calc RatFunc.inftyValuation ℂ (RatFunc.C _) * WithZero.exp (-(b65k_poleOrder b : ℤ)) ≤
      1 * WithZero.exp (-1) := by
        gcongr
        · exact b65q_v_C_le _
        · exact WithZero.exp_le_exp.mpr (by omega)
    _ = _ := one_mul _

end HodgeLean.Foundations.Program
