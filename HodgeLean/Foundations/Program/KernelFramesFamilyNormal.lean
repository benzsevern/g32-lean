import HodgeLean.Foundations.Program.KernelFramesFamilyAnalytic

/-! # B6-5 stage 5d, family part: normalized eigenbases and left eigenvectors along the path

On a disc where the comparison determinants and the pairings `uᵀA_t u` are nonzero, the
normalized fixed-pole eigenbases are analytic, invertible eigenbases with the constant
exponents normalized against the initial eigenbases, and the normalized moving-pole left
eigenvectors are analytic, nonzero left eigenvectors for the constant trace with `wᵀu = tr`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- The comparison matrix `Π(A₀)Π(A(θ)) + 1 − Π(A₀)` of the normalized eigenbasis at the fixed
pole `k`, for the eigenvalue of index `i`. -/
def b65q_cmp (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) (k i : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  b65q_projector (b65q_res R 0 (Sum.inl k)) (b65p_exponents k) (b65p_exponents k i) *
    b65q_projector (b65q_res R θ (Sum.inl k)) (b65p_exponents k) (b65p_exponents k i) + 1 -
      b65q_projector (b65q_res R 0 (Sum.inl k)) (b65p_exponents k) (b65p_exponents k i)

/-- The normalizing pairing `uᵀ A_t u` at the moving pole `x`. -/
def b65q_nrm (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) (x : Fin 12) : ℂ :=
  b65q_u (b65q_fibreIndex x) ᵥ* b65q_res R θ (Sum.inr x) ⬝ᵥ b65q_u (b65q_fibreIndex x)

theorem b65q_fixed_eig_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k : Fin 4) :
    b65q_res O.residue 0 (Sum.inl k) * b65q_eigen0 k = b65q_eigen0 k * diagonal (b65p_exponents k) := by
  rw [b65q_res_zero_inl]; exact b65q_fixed_eig k

theorem b65q_minpoly_flow {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k : Fin 4) :
    ∀ θ ∈ ball (0 : ℂ) O.radius,
      aeval (b65q_res O.residue θ (Sum.inl k)) (b65q_minpoly (b65p_exponents k)) = 0 :=
  b65q_aeval_flow O (Sum.inl k) _
    (b65q_minpoly_base _ _ _ (b65q_eigen0_isUnit k) (b65q_fixed_eig_zero O k))

theorem b65q_cmp_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k i : Fin 4) :
    b65q_cmp O.residue 0 k i = 1 := by
  rw [b65q_cmp, b65q_proj_idem _ _ (b65q_minpoly_base _ _ _ (b65q_eigen0_isUnit k)
    (b65q_fixed_eig_zero O k)) (Finset.mem_image_of_mem _ (Finset.mem_univ i)),
    add_sub_cancel_left]

theorem b65q_cmp_an {p : Fin 12 → ℂ} (O : b65p_Outputs p) (k i : Fin 4) :
    b65q_MatAn (ball 0 O.radius) fun θ ↦ b65q_cmp O.residue θ k i :=
  ((b65q_MatAn.const _).mul ((b65q_MatAn.res O _).aeval _)).add (b65q_MatAn.const _) |>.sub
    (b65q_MatAn.const _)

theorem b65q_uQ_cast (e : Fin 2) : b65q_u e = fun i ↦ ((b65q_uQ e i : ℚ) : ℂ) := by
  funext i; fin_cases e <;> fin_cases i <;> norm_num [b65q_u, b65q_uQ]

theorem b65q_nrm_an {p : Fin 12 → ℂ} (O : b65p_Outputs p) (x : Fin 12) :
    AnalyticOnNhd ℂ (fun θ ↦ b65q_nrm O.residue θ x) (ball 0 O.radius) := by
  unfold b65q_nrm
  simp only [dotProduct, Matrix.vecMul]
  exact b65q_an_sum _ fun j _ ↦ (b65q_an_sum _ fun i _ ↦
    analyticOnNhd_const.mul (b65q_MatAn.res O _ i j)).mul analyticOnNhd_const

theorem b65q_BQ_sq (e : Fin 2) : b65q_BQ e * b65q_BQ e = Matrix.trace (b65q_BQ e) • b65q_BQ e := by
  fin_cases e <;> decide +kernel

theorem b65q_BQ_trace_ne (e : Fin 2) : Matrix.trace (b65q_BQ e) ≠ 0 := by
  fin_cases e <;> decide +kernel

theorem b65q_nrmQ_ne (e : Fin 2) : b65q_uQ e ᵥ* b65q_BQ e ⬝ᵥ b65q_uQ e ≠ 0 := by
  fin_cases e <;> decide +kernel

theorem b65q_nrm_zero {p : Fin 12 → ℂ} (O : b65p_Outputs p) (x : Fin 12) :
    b65q_nrm O.residue 0 x ≠ 0 := by
  rw [b65q_nrm, b65q_res_zero_inr, b65q_uQ_cast]
  have h := b65q_nrmQ_ne (b65q_fibreIndex x)
  have : ((fun i ↦ ((b65q_uQ (b65q_fibreIndex x) i : ℚ) : ℂ)) ᵥ*
      (b65q_BQ (b65q_fibreIndex x)).map ι ⬝ᵥ fun i ↦ ((b65q_uQ (b65q_fibreIndex x) i : ℚ) : ℂ)) =
      ((b65q_uQ (b65q_fibreIndex x) ᵥ* b65q_BQ (b65q_fibreIndex x) ⬝ᵥ
        b65q_uQ (b65q_fibreIndex x) : ℚ) : ℂ) := by
    simp [dotProduct, Matrix.vecMul, Matrix.map_apply]
  rw [this]; exact_mod_cast h

theorem b65q_trace_zero_inr {p : Fin 12 → ℂ} (O : b65p_Outputs p) (x : Fin 12) :
    Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) =
      ((Matrix.trace (b65q_BQ (b65q_fibreIndex x)) : ℚ) : ℂ) := by
  rw [b65q_res_zero_inr]; simp [Matrix.trace, Matrix.map_apply]

theorem b65q_rank_one_flow {p : Fin 12 → ℂ} (O : b65p_Outputs p) (x : Fin 12) :
    ∀ θ ∈ ball (0 : ℂ) O.radius, b65q_res O.residue θ (Sum.inr x) * b65q_res O.residue θ (Sum.inr x) =
      Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) • b65q_res O.residue θ (Sum.inr x) := by
  intro θ hθ
  have h := b65q_aeval_flow O (Sum.inr x)
    (X ^ 2 - C (Matrix.trace (b65q_res O.residue 0 (Sum.inr x))) * X) ?_ θ hθ
  · simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul] at h
    rw [← sub_eq_zero, ← h, sq]
  · simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, sub_eq_zero, sq]
    rw [b65q_trace_zero_inr, b65q_res_zero_inr, ← Matrix.map_mul, b65q_BQ_sq]
    ext i j; simp [Matrix.map_apply]

/-- A disc on which all comparison determinants and normalizing pairings are nonzero. -/
theorem b65q_good_disc {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      (∀ k i, (b65q_cmp O.residue θ k i).det ≠ 0) ∧ ∀ x, b65q_nrm O.residue θ x ≠ 0 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) O.radius := mem_ball_self O.radius_pos
  have hev : ∀ᶠ θ in 𝓝 (0 : ℂ),
      (∀ k i, (b65q_cmp O.residue θ k i).det ≠ 0) ∧ ∀ x, b65q_nrm O.residue θ x ≠ 0 := by
    refine (eventually_all.2 fun k ↦ eventually_all.2 fun i ↦ ?_).and (eventually_all.2 fun x ↦ ?_)
    · have hc := ((b65q_cmp_an O k i).det 0 h0).continuousAt
      exact hc.eventually_ne (by rw [b65q_cmp_zero, det_one]; exact one_ne_zero)
    · exact ((b65q_nrm_an O x) 0 h0).continuousAt.eventually_ne (b65q_nrm_zero O x)
  obtain ⟨ε₁, hε₁, h⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨min ε₁ O.radius, lt_min hε₁ O.radius_pos, min_le_right _ _,
    fun θ hθ ↦ h θ (ball_subset_ball (min_le_left _ _) hθ)⟩

theorem b65q_basis_apply (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ)
    (k i j : Fin 4) : b65q_basis R θ k i j =
      (b65q_projector (b65q_res R θ (Sum.inl k)) (b65p_exponents k) (b65p_exponents k j) *
        (b65q_cmp R θ k j)⁻¹ * b65q_eigen0 k) i j := rfl

theorem b65q_left_apply (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ)
    (x : Fin 12) : b65q_left R θ x =
      (Matrix.trace (b65q_res R θ (Sum.inr x)) / b65q_nrm R θ x) •
        (b65q_u (b65q_fibreIndex x) ᵥ* b65q_res R θ (Sum.inr x)) := rfl

theorem b65q_normalizations_on {p : Fin 12 → ℂ} (O : b65p_Outputs p) {ε : ℝ} (hε : ε ≤ O.radius)
    (hgood : ∀ θ ∈ ball (0 : ℂ) ε,
      (∀ k i, (b65q_cmp O.residue θ k i).det ≠ 0) ∧ ∀ x, b65q_nrm O.residue θ x ≠ 0) :
      (∀ k : Fin 4, ∀ i j : Fin 4,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_basis O.residue θ k i j) (ball 0 ε)) ∧
      (∀ x : Fin 12, ∀ i : Fin 4,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_left O.residue θ x i) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε,
        (∀ k : Fin 4, IsUnit (b65q_basis O.residue θ k) ∧
          b65q_res O.residue θ (Sum.inl k) * b65q_basis O.residue θ k =
            b65q_basis O.residue θ k * diagonal (b65p_exponents k) ∧
          ∀ i j : Fin 4, b65p_exponents k i = b65p_exponents k j →
            ((b65q_eigen0 k)⁻¹ * b65q_basis O.residue θ k) i j = if i = j then 1 else 0) ∧
        ∀ x : Fin 12, b65q_left O.residue θ x ≠ 0 ∧
          b65q_left O.residue θ x ᵥ* b65q_res O.residue θ (Sum.inr x) =
            Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) • b65q_left O.residue θ x ∧
          b65q_left O.residue θ x ⬝ᵥ b65q_u (b65q_fibreIndex x) =
            Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) := by
  have hsub : ball (0 : ℂ) ε ⊆ ball 0 O.radius := ball_subset_ball hε
  refine ⟨fun k i j ↦ ?_, fun x i ↦ ?_, fun θ hθ ↦ ⟨fun k ↦ ?_, fun x ↦ ?_⟩⟩
  · simp only [b65q_basis_apply]
    have hres := (b65q_MatAn.res O (Sum.inl k)).mono hsub
    have hc := (b65q_cmp_an O k j).mono hsub
    exact (((hres.aeval _).mul (hc.inv fun θ hθ ↦ (hgood θ hθ).1 k j)).mul
      (b65q_MatAn.const _)) i j
  · simp only [b65q_left_apply, Pi.smul_apply, smul_eq_mul]
    have hres := (b65q_MatAn.res O (Sum.inr x)).mono hsub
    refine AnalyticOnNhd.mul ?_ ?_
    · refine AnalyticOnNhd.div ?_ ((b65q_nrm_an O x).mono hsub) fun θ hθ ↦ (hgood θ hθ).2 x
      simp only [Matrix.trace, Matrix.diag]
      exact b65q_an_sum _ fun a _ ↦ hres a a
    · simp only [Matrix.vecMul, dotProduct]
      exact b65q_an_sum _ fun a _ ↦ analyticOnNhd_const.mul (hres a i)
  · have hm := b65q_minpoly_flow O k θ (hsub hθ)
    have hX : ∀ i, IsUnit (b65q_cmp O.residue θ k i) := fun i ↦
      (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ((hgood θ hθ).1 k i))
    have hP₀ := b65q_eigen0_isUnit k
    have hA₀ := b65q_fixed_eig_zero O k
    exact ⟨b65q_eigenbasis_isUnit _ _ _ _ hm hP₀ hA₀ hX, b65q_eigenbasis_eig _ _ _ _ hm,
      fun i j hij ↦ b65q_eigenbasis_norm _ _ _ _ hP₀ hA₀ hX i j hij⟩
  · have hn := (hgood θ hθ).2 x
    have hsq := b65q_rank_one_flow O x θ (hsub hθ)
    have htr := b65q_trace_flow O (Sum.inr x) θ (hsub hθ)
    set A := b65q_res O.residue θ (Sum.inr x)
    set u := b65q_u (b65q_fibreIndex x)
    have hdot : b65q_left O.residue θ x ⬝ᵥ u = Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) := by
      rw [b65q_left_apply, smul_dotProduct, smul_eq_mul, ← htr]
      exact div_mul_cancel₀ _ hn
    refine ⟨fun h0 ↦ ?_, ?_, hdot⟩
    · rw [h0, zero_dotProduct, b65q_trace_zero_inr] at hdot
      exact b65q_BQ_trace_ne _ (by exact_mod_cast hdot.symm)
    · rw [b65q_left_apply, Matrix.smul_vecMul, Matrix.vecMul_vecMul, hsq, Matrix.vecMul_smul,
        smul_comm]

end HodgeLean.Foundations.Program
