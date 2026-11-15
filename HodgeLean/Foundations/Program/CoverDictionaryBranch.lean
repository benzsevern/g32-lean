import HodgeLean.Foundations.Program.CoverDictionaryDefs

/-! # B6-5 stage 5d, geometric part: branch-point coordinates over a 5c record

Analytic determinants and inverses of matrix families, the branch polynomial split at a moving
root, the derivative of the normalization, and the branch-point coordinate statement: the matrix
`V(θ)` is a Vandermonde matrix times an invertible diagonal, its inverse is analytic, and its
entries are the residues of `N(s)/(D_θ(s) m_θ'(s))` at the chart branch points.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Determinants of entrywise analytic matrix families are analytic. -/
theorem b65g_det_analytic {U : Set ℂ} {n : Type*} [Fintype n] [DecidableEq n]
    {A : ℂ → Matrix n n ℂ} (hA : ∀ i j, AnalyticOnNhd ℂ (fun θ ↦ A θ i j) U) :
    AnalyticOnNhd ℂ (fun θ ↦ (A θ).det) U := by
  have h : (fun θ ↦ (A θ).det) = fun θ ↦
      ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A θ (σ i) i := by
    funext θ; rw [Matrix.det_apply']
  rw [h]
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ ↦
    analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun i _ ↦ hA _ _)

/-- Inverses of entrywise analytic matrix families with nonzero determinant are analytic. -/
theorem b65g_inv_analytic {U : Set ℂ} {n : Type*} [Fintype n] [DecidableEq n]
    {A : ℂ → Matrix n n ℂ} (hA : ∀ i j, AnalyticOnNhd ℂ (fun θ ↦ A θ i j) U)
    (hdet : ∀ θ ∈ U, (A θ).det ≠ 0) (i j : n) :
    AnalyticOnNhd ℂ (fun θ ↦ (A θ)⁻¹ i j) U := by
  have hadj : AnalyticOnNhd ℂ (fun θ ↦ (A θ).adjugate i j) U := by
    simp only [Matrix.adjugate_apply]
    refine b65g_det_analytic (A := fun θ ↦ (A θ).updateRow j (Pi.single i 1)) fun k l ↦ ?_
    by_cases hk : k = j
    · subst hk; simp only [Matrix.updateRow_self]; exact analyticOnNhd_const
    · simp only [Matrix.updateRow_ne hk]; exact hA k l
  have h : (fun θ ↦ (A θ)⁻¹ i j) = fun θ ↦ ((A θ).det)⁻¹ * (A θ).adjugate i j := by
    funext θ; rw [Matrix.inv_def, Ring.inverse_eq_inv']; rfl
  rw [h]
  exact ((b65g_det_analytic hA).inv hdet).mul hadj

/-- The branch polynomial with the factor `s − t_k` removed: `s · Π_{x ≠ k} (s − t_x)`.
Source: G32 v0.16, §5.5(7), `D_θ = s D_{5,θ} D_{−7,θ}`; `b65q_denominator`. -/
def b65g_rest (t : Fin 4 ⊕ Fin 12 → ℂ) (k : Fin 12) (s : ℂ) : ℂ :=
  s * ∏ x ∈ Finset.univ.erase k, (s - t (Sum.inr x))

/-- The reduced branch polynomial is continuous. -/
theorem b65g_rest_continuous (t : Fin 4 ⊕ Fin 12 → ℂ) (k : Fin 12) :
    Continuous (b65g_rest t k) := by
  unfold b65g_rest; fun_prop

/-- Splitting off one moving root of the branch polynomial. -/
theorem b65g_denominator_split (t : Fin 4 ⊕ Fin 12 → ℂ) (k : Fin 12) :
    b65q_denominator t = (X - C (t (Sum.inr k))) *
      (X * ∏ x ∈ Finset.univ.erase k, (X - C (t (Sum.inr x)))) := by
  rw [b65q_denominator, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]; ring

/-- Evaluation of the split branch polynomial. -/
theorem b65g_denominator_eval (t : Fin 4 ⊕ Fin 12 → ℂ) (k : Fin 12) (s : ℂ) :
    (b65q_denominator t).eval s = (s - t (Sum.inr k)) * b65g_rest t k s := by
  rw [b65g_denominator_split t k]; simp [eval_prod, b65g_rest]

/-- The derivative of the branch polynomial at a moving root. -/
theorem b65g_denominator_deriv (t : Fin 4 ⊕ Fin 12 → ℂ) (k : Fin 12) :
    (derivative (b65q_denominator t)).eval (t (Sum.inr k)) = b65g_rest t k (t (Sum.inr k)) := by
  rw [b65g_denominator_split t k, derivative_mul]; simp [eval_prod, b65g_rest]

/-- The derivative of the normalization `z ↦ (z − a)b/(z(b − a))` away from `0`. -/
theorem b65g_normalize_hasDerivAt {a b z : ℂ} (hab : a ≠ b) (hz : z ≠ 0) :
    HasDerivAt (b65s_normalize a b) (a * b / ((b - a) * z ^ 2)) z := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h := (((hasDerivAt_id z).sub_const a).mul_const b).div
    ((hasDerivAt_id z).mul_const (b - a)) (mul_ne_zero hz hba)
  convert h using 1
  · funext y; simp [b65s_normalize]
  · simp only [id]; field_simp; ring


/-- Facts about the chart branch points at a parameter in the record's ball. -/
theorem b65g_point_facts (p : Fin 12 → ℂ) (O : b65p_Outputs p) {θ : ℂ}
    (hθ : θ ∈ ball (0 : ℂ) O.radius) (k : Fin 10) :
    b65p_moving p θ (Fin.castLE (by norm_num) k) ≠ 0 ∧
      b65p_moving p θ 10 ≠ b65p_moving p θ 11 ∧
      b65g_rest (b65p_poles p θ) (Fin.castLE (by norm_num) k)
        (b65p_moving p θ (Fin.castLE (by norm_num) k)) ≠ 0 ∧
      b65p_moving p θ 10 ≠ 0 ∧ b65p_moving p θ 11 ≠ 0 := by
  have hinj := O.poles_injective θ hθ
  have h0 : b65p_poles p θ (Sum.inl 0) = 0 := rfl
  have hne0 : ∀ j : Fin 12, b65p_moving p θ j ≠ 0 := fun j h ↦ by
    have := hinj (h.trans h0.symm); simp at this
  have hne : ∀ i j : Fin 12, i ≠ j → b65p_moving p θ i ≠ b65p_moving p θ j :=
    fun i j hij h ↦ hij (Sum.inr_injective (hinj h))
  refine ⟨hne0 _, hne _ _ (by decide), ?_, hne0 _, hne0 _⟩
  refine mul_ne_zero (hne0 _) (Finset.prod_ne_zero_iff.mpr fun x hx ↦ ?_)
  exact sub_ne_zero.mpr (hne _ _ (Finset.ne_of_mem_erase hx).symm)

/-- The explicit form of the branch-matrix denominators. -/
theorem b65g_branchMatrix_eq (p : Fin 12 → ℂ) (O : b65p_Outputs p) {θ : ℂ}
    (hθ : θ ∈ ball (0 : ℂ) O.radius) (j k : Fin 10) :
    b65g_branchMatrix p θ j k = b65p_moving p θ (Fin.castLE (by norm_num) k) ^ j.val /
      (b65g_rest (b65p_poles p θ) (Fin.castLE (by norm_num) k)
          (b65p_moving p θ (Fin.castLE (by norm_num) k)) *
        (b65p_moving p θ 10 * b65p_moving p θ 11 /
          ((b65p_moving p θ 11 - b65p_moving p θ 10) *
            b65p_moving p θ (Fin.castLE (by norm_num) k) ^ 2))) := by
  obtain ⟨hs, hab, -, -, -⟩ := b65g_point_facts p O hθ k
  rw [b65g_branchMatrix, (b65g_normalize_hasDerivAt hab hs).deriv]
  congr 2
  exact b65g_denominator_deriv _ _

/-- The branch-coordinate statement over a 5c record. -/
theorem b65g_branch_coordinates_core (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ j k : Fin 10, AnalyticOnNhd ℂ (fun θ ↦ b65g_B p θ j k) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, IsUnit (b65g_branchMatrix p θ) ∧
        ∀ (N : Fin 10 → ℂ) (k : Fin 10),
          Tendsto (fun s : ℂ ↦ (s - b65p_moving p θ (Fin.castLE (by norm_num) k)) *
              (∑ j : Fin 10, N j * s ^ j.val) /
              ((b65q_denominator (b65p_poles p θ)).eval s *
                deriv (b65s_normalize (b65p_moving p θ 10) (b65p_moving p θ 11)) s))
            (𝓝[≠] (b65p_moving p θ (Fin.castLE (by norm_num) k)))
            (𝓝 ((N ᵥ* b65g_branchMatrix p θ) k)) := by
  have hpole : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ b65p_poles p θ q) univ := by
    rintro (q | q)
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const.add (analyticOnNhd_id.mul analyticOnNhd_const)
  have hmov : ∀ j, AnalyticOnNhd ℂ (fun θ ↦ b65p_moving p θ j) (ball 0 O.radius) :=
    fun j ↦ (hpole (Sum.inr j)).mono (subset_univ _)
  have hV : ∀ θ ∈ ball (0 : ℂ) O.radius, (b65g_branchMatrix p θ).det ≠ 0 := by
    intro θ hθ
    have hfac : b65g_branchMatrix p θ =
        (Matrix.vandermonde fun k : Fin 10 ↦ b65p_moving p θ (Fin.castLE (by norm_num) k))ᵀ *
          Matrix.diagonal fun k : Fin 10 ↦
            (b65g_rest (b65p_poles p θ) (Fin.castLE (by norm_num) k)
              (b65p_moving p θ (Fin.castLE (by norm_num) k)) *
            (b65p_moving p θ 10 * b65p_moving p θ 11 /
              ((b65p_moving p θ 11 - b65p_moving p θ 10) *
                b65p_moving p θ (Fin.castLE (by norm_num) k) ^ 2)))⁻¹ := by
      ext j k
      rw [b65g_branchMatrix_eq p O hθ, Matrix.mul_diagonal, Matrix.transpose_apply,
        Matrix.vandermonde_apply, div_eq_mul_inv]
    rw [hfac, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    refine mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)
      (Finset.prod_ne_zero_iff.mpr fun k _ ↦ ?_)
    · intro i j h
      have := Sum.inr_injective (O.poles_injective θ hθ h)
      exact Fin.castLE_injective _ this
    · obtain ⟨hs, hab, hr, ha, hb⟩ := b65g_point_facts p O hθ k
      have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
      exact inv_ne_zero (mul_ne_zero hr (div_ne_zero (mul_ne_zero ha hb)
        (mul_ne_zero hba (pow_ne_zero 2 hs))))
  refine ⟨O.radius, O.radius_pos, le_rfl, ?_, ?_⟩
  · intro j k
    refine b65g_inv_analytic (fun j k ↦ ?_) hV j k
    have hexp : AnalyticOnNhd ℂ (fun θ ↦ b65p_moving p θ (Fin.castLE (by norm_num) k) ^ j.val /
        (b65g_rest (b65p_poles p θ) (Fin.castLE (by norm_num) k)
            (b65p_moving p θ (Fin.castLE (by norm_num) k)) *
          (b65p_moving p θ 10 * b65p_moving p θ 11 /
            ((b65p_moving p θ 11 - b65p_moving p θ 10) *
              b65p_moving p θ (Fin.castLE (by norm_num) k) ^ 2)))) (ball 0 O.radius) := by
      have hrest : AnalyticOnNhd ℂ (fun θ ↦ b65g_rest (b65p_poles p θ) (Fin.castLE (by norm_num) k)
          (b65p_moving p θ (Fin.castLE (by norm_num) k))) (ball 0 O.radius) :=
        (hmov _).mul (Finset.analyticOnNhd_fun_prod _ fun x _ ↦ (hmov _).sub (hmov x))
      refine ((hmov _).pow _).div (hrest.mul ((((hmov 10).mul (hmov 11)).div
        (((hmov 11).sub (hmov 10)).mul ((hmov _).pow 2))) fun θ hθ ↦ ?_)) fun θ hθ ↦ ?_
      · obtain ⟨hs, hab, -, -, -⟩ := b65g_point_facts p O hθ k
        exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) (pow_ne_zero 2 hs)
      · obtain ⟨hs, hab, hr, ha, hb⟩ := b65g_point_facts p O hθ k
        exact mul_ne_zero hr (div_ne_zero (mul_ne_zero ha hb)
          (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) (pow_ne_zero 2 hs)))
    exact hexp.congr isOpen_ball fun θ hθ ↦ (b65g_branchMatrix_eq p O hθ j k).symm
  intro θ hθ
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hV θ hθ)), ?_⟩
  intro N k
  obtain ⟨hs, hab, hr, ha, hb⟩ := b65g_point_facts p O hθ k
  set sk := b65p_moving p θ (Fin.castLE (by norm_num) k) with hsk
  set a := b65p_moving p θ 10
  set b := b65p_moving p θ 11
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set g : ℂ → ℂ := fun s ↦ (∑ j : Fin 10, N j * s ^ j.val) /
    (b65g_rest (b65p_poles p θ) (Fin.castLE (by norm_num) k) s * (a * b / ((b - a) * s ^ 2)))
    with hg
  have hcont : ContinuousAt g sk := by
    refine ContinuousAt.div (by fun_prop) (ContinuousAt.mul ?_ ?_) ?_
    · exact (b65g_rest_continuous _ _).continuousAt
    · exact continuousAt_const.div (by fun_prop) (mul_ne_zero hba (pow_ne_zero 2 hs))
    · exact mul_ne_zero hr (div_ne_zero (mul_ne_zero ha hb) (mul_ne_zero hba (pow_ne_zero 2 hs)))
  have hval : g sk = (N ᵥ* b65g_branchMatrix p θ) k := by
    simp only [hg, Matrix.vecMul, dotProduct, b65g_branchMatrix_eq p O hθ, ← hsk]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ (mul_div_assoc _ _ _)
  rw [← hval]
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev : ∀ᶠ s in 𝓝[≠] sk, s ≠ 0 ∧ s ≠ sk :=
    (eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hs)).and
      self_mem_nhdsWithin
  filter_upwards [hev] with s ⟨hs0, hssk⟩
  have hsub : s - sk ≠ 0 := sub_ne_zero.mpr hssk
  rw [b65g_denominator_eval _ (Fin.castLE (by norm_num) k), (b65g_normalize_hasDerivAt hab hs0).deriv]
  change _ = (s - sk) * _ / ((s - sk) * _ * _)
  rw [mul_assoc (s - sk), mul_div_mul_left _ _ hsub]

end HodgeLean.Foundations.Program
