import HodgeLean.Foundations.Program.PrymParabolicSaturatedLemmas

/-! # Lemmas for stage H5, first part: Schur's lemma for the `K`-form and the coordinate cup

Over `K = ℚ(√−3)`, for `σ = hg4_sigmaK`: unitarity, the commutant of the conjugate
representation, the primitive projector matrix `Σ_h c_h σ(h) = D·E₀₀`, the group average of
`E₀₀`, and the irreducibility of `σ` in the form used by the comparison. Then the coordinate
cup matrix of two equivariant cochains is scalar, with trace H4's cup form.
HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Papers Matrix

namespace HodgeLean.Foundations.Program

/-! ## Matrices over `K` -/

theorem hg6_natCast_ne_zero (n : ℕ) (hn : n ≠ 0) : (n : hp_K) ≠ 0 := by
  intro h
  have h' := congrArg hp_embed h
  rw [map_natCast, map_zero] at h'
  exact hn (by exact_mod_cast h')

/-- `σ` is unitary for the standard Hermitian form over `K`. -/
theorem hg6_sigma_unitary (h : b4b_Group) : (hg4_sigmaK h)ᴴ * hg4_sigmaK h = 1 := by
  have hstar : Function.Semiconj hp_embed star star := hp_embed_star
  apply hg4_embedMatrix_injective
  change ((hg4_sigmaK h)ᴴ * hg4_sigmaK h).map hp_embed = (1 : Matrix _ _ hp_K).map hp_embed
  rw [Matrix.map_mul, Matrix.conjTranspose_map _ hstar, hg4_sigmaK_map,
    Matrix.map_one _ (map_zero _) (map_one _), ← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)

theorem hg6_sigma_transpose_conj (h : b4b_Group) :
    (hg4_sigmaK h)ᵀ * (hg4_sigmaK h).map star = 1 := by
  have h' := congrArg Matrix.transpose (hg6_sigma_unitary h)
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h'
  rw [← h']
  rfl

/-- A `K`-matrix commuting with every `σ̄(h)` is scalar (Schur's lemma, through the complex
embedding followed by complex conjugation and `b63d_matrix_commutant`). -/
theorem hg6_commutant_conj (M : Matrix (Fin 4) (Fin 4) hp_K)
    (hM : ∀ h : b4b_Group, M * (hg4_sigmaK h).map star = (hg4_sigmaK h).map star * M) :
    M = M 0 0 • (1 : Matrix (Fin 4) (Fin 4) hp_K) := by
  let R : hp_K →+* ℂ := (starRingEnd ℂ).comp hp_embed
  have hR : ∀ x, R (star x) = hp_embed x := fun x => by
    simp only [R, RingHom.comp_apply, hp_embed_star, starRingEnd_apply, star_star]
  have hmap : ∀ h, ((hg4_sigmaK h).map star).map R = b4b_toMatrix h := fun h => by
    rw [Matrix.map_map, ← hg4_sigmaK_map]
    congr 1
    funext x
    exact hR x
  have hc : ∀ h, M.map R * b4b_toMatrix h = b4b_toMatrix h * M.map R := fun h => by
    rw [← hmap, ← Matrix.map_mul, ← Matrix.map_mul, hM h]
  have hP := b63d_matrix_commutant (M.map R) (hc (b4b_generators 0)) (hc (b4b_generators 1))
    (hc (b4b_generators 2))
  refine Matrix.ext fun i j => ?_
  apply R.injective
  have h := congrFun (congrFun hP i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h ⊢
  split_ifs at h ⊢ <;> simp_all

/-- The primitive projector over `K`: `Σ_h c_h σ(h) = D·E₀₀` (`b63l_projector_matrix`). -/
theorem hg6_sigma_projector :
    ∑ h : b4b_Group, b4b_projectorCoeff h • hg4_sigmaK h =
      b4b_projectorDenominator • (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) hp_K) := by
  apply Matrix.map_injective hp_embed.injective
  change hp_embed.mapMatrix _ = hp_embed.mapMatrix _
  rw [map_sum, map_zsmul]
  simp only [map_zsmul, RingHom.mapMatrix_apply, hg4_sigmaK_map]
  have hs : (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) hp_K).map hp_embed =
      Matrix.single 0 0 1 := by
    ext i j
    simp [Matrix.single_apply]
  rw [hs]
  have h := b63l_projector_matrix
  simp only [Int.cast_smul_eq_zsmul] at h
  exact h

/-- The group average of `E₀₀` over `K`: `Σ_h σ(h⁻¹) E₀₀ σ(h) = (|G|/4)·1`
(`b63l_average_scalar`). -/
theorem hg6_sigma_average :
    ∑ h : b4b_Group, hg4_sigmaK h⁻¹ * Matrix.single 0 0 1 * hg4_sigmaK h =
      (38880 : ℕ) • (1 : Matrix (Fin 4) (Fin 4) hp_K) := by
  apply Matrix.map_injective hp_embed.injective
  change hp_embed.mapMatrix _ = hp_embed.mapMatrix _
  rw [map_sum, map_nsmul, map_one]
  simp only [map_mul, RingHom.mapMatrix_apply, hg4_sigmaK_map]
  have hs : (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) hp_K).map hp_embed =
      Matrix.single 0 0 1 := by
    ext i j
    simp [Matrix.single_apply]
  rw [hs]
  have h := b63l_average_scalar (Matrix.single 0 0 1)
  have h2 : ∑ h : b4b_Group, b4b_toMatrix h⁻¹ * Matrix.single 0 0 1 * b4b_toMatrix h =
      ∑ g : b4b_Group, b4b_toMatrix g * Matrix.single 0 0 1 * b4b_toMatrix g⁻¹ :=
    Fintype.sum_equiv (Equiv.inv b4b_Group) _ _ (fun h => by simp)
  rw [h2, h, Matrix.trace_single_eq_same]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  norm_num

/-- Irreducibility of `σ` in the form used below: a vector whose `σ`-translates all have
vanishing `0`-th coordinate is zero (apply `hg6_sigma_average`). -/
theorem hg6_sigma_irreducible (v : Fin 4 → hp_K) (hv : ∀ h : b4b_Group, (hg4_sigmaK h *ᵥ v) 0 = 0) :
    v = 0 := by
  have h := congrArg (fun M => M *ᵥ v) hg6_sigma_average
  simp only [Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.single_mulVec, hv, mul_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have h' : ((38880 : ℕ) : hp_K) • v = 0 := by
    rw [Nat.cast_smul_eq_nsmul, ← h]
    simp
  exact (smul_eq_zero.mp h').resolve_left (hg6_natCast_ne_zero _ (by norm_num))

/-! ## The coordinate cup matrix -/

theorem hg6_vecMulVec_mulVec {ι K : Type*} [Fintype ι] [Field K] [StarRing K]
    (A : Matrix ι ι K) (u v : ι → K) :
    vecMulVec (star (A *ᵥ u)) (A *ᵥ v) = A.map star * vecMulVec (star u) v * Aᵀ := by
  ext i j
  simp only [vecMulVec_apply, Pi.star_apply, mulVec, dotProduct, mul_apply, map_apply,
    transpose_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The coordinate cup products as a matrix of outer products over the orientation chain. -/
theorem hg6_coordMat_eq {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} {r : ℕ} (g : Fin r → G) (α β : hg_Edge G r → ι → K) :
    Matrix.of (fun i j => hg6_coordCup g i j α β) =
      ∑ k, ∑ x, (vecMulVec (star (α (Sum.inl (k, x)))) (β (Sum.inr (Sum.inr (k, x)))) -
        vecMulVec (star (α (Sum.inl (k, x)))) (β (Sum.inr (Sum.inr (k, x * (g k)⁻¹))))) := by
  ext i j
  simp only [of_apply, hg6_coordCup, hg_fundEval, hg_face2, hg_face0, Matrix.sum_apply,
    Matrix.sub_apply, vecMulVec_apply, Pi.star_apply]

/-- For equivariant cochains the coordinate cup matrix satisfies `M = σ̄(h) M σ(h)ᵀ`. -/
theorem hg6_coordMat_equivariant {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K)
    (g : Fin r → G) (α β : hg_Edge G r → ι → K)
    (hα : α ∈ hg_eqCochain1 σ) (hβ : β ∈ hg_eqCochain1 σ) (h : G) :
    Matrix.of (fun i j => hg6_coordCup g i j α β) =
      (σ h).map star * Matrix.of (fun i j => hg6_coordCup g i j α β) * (σ h)ᵀ := by
  rw [hg6_coordMat_eq]
  have key : ∀ k x,
      vecMulVec (star (α (Sum.inl (k, h * x)))) (β (Sum.inr (Sum.inr (k, h * x)))) -
        vecMulVec (star (α (Sum.inl (k, h * x))))
          (β (Sum.inr (Sum.inr (k, h * x * (g k)⁻¹)))) =
      (σ h).map star * (vecMulVec (star (α (Sum.inl (k, x)))) (β (Sum.inr (Sum.inr (k, x)))) -
        vecMulVec (star (α (Sum.inl (k, x)))) (β (Sum.inr (Sum.inr (k, x * (g k)⁻¹))))) *
        (σ h)ᵀ := fun k x => by
    have h1 : α (Sum.inl (k, h * x)) = σ h *ᵥ α (Sum.inl (k, x)) := hα h (Sum.inl (k, x))
    have h2 : β (Sum.inr (Sum.inr (k, h * x))) = σ h *ᵥ β (Sum.inr (Sum.inr (k, x))) :=
      hβ h (Sum.inr (Sum.inr (k, x)))
    have h3 : β (Sum.inr (Sum.inr (k, h * x * (g k)⁻¹))) =
        σ h *ᵥ β (Sum.inr (Sum.inr (k, x * (g k)⁻¹))) := by
      rw [mul_assoc]
      exact hβ h (Sum.inr (Sum.inr (k, x * (g k)⁻¹)))
    rw [h1, h2, h3, hg6_vecMulVec_mulVec, hg6_vecMulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul]
  calc _ = ∑ k, ∑ x,
        (vecMulVec (star (α (Sum.inl (k, h * x)))) (β (Sum.inr (Sum.inr (k, h * x)))) -
        vecMulVec (star (α (Sum.inl (k, h * x))))
          (β (Sum.inr (Sum.inr (k, h * x * (g k)⁻¹))))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact (Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun x => rfl)).symm
    _ = _ := by
        simp only [key, Finset.mul_sum, Finset.sum_mul]

theorem hg6_coordCup_trace {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (g : Fin r → G)
    (α β : hg_Edge G r → ι → K) :
    ∑ i, hg6_coordCup g i i α β = hg4_cupForm g 1 α β := by
  simp only [hg6_coordCup, hg4_cupForm, LinearMap.mk₂'ₛₗ_apply, hg_cup, hg_fundEval,
    Matrix.one_mulVec, dotProduct, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_sub_distrib]

theorem hg6_coordCup_schur_lemma (α β : hg_Edge b4b_Group 13 → Fin 4 → hp_K)
    (hα : α ∈ hg_eqCochain1 hg4_sigmaK) (hβ : β ∈ hg_eqCochain1 hg4_sigmaK) (i j : Fin 4) :
    hg6_coordCup b4b_root i j α β =
      if i = j then (4 : hp_K)⁻¹ * hg4_cupForm b4b_root 1 α β else 0 := by
  set M := Matrix.of (fun i j => hg6_coordCup b4b_root i j α β) with hMdef
  have hcomm : ∀ h : b4b_Group,
      M * (hg4_sigmaK h).map star = (hg4_sigmaK h).map star * M := fun h => by
    have hM := hg6_coordMat_equivariant hg4_sigmaK b4b_root α β hα hβ h
    rw [← hMdef] at hM
    nth_rewrite 1 [hM]
    rw [Matrix.mul_assoc, hg6_sigma_transpose_conj, Matrix.mul_one]
  have hs := hg6_commutant_conj M hcomm
  have hentry : ∀ a b, hg6_coordCup b4b_root a b α β = if a = b then M 0 0 else 0 :=
    fun a b => by
      have := congrFun (congrFun hs a) b
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero] at this
      exact this
  have htr := hg6_coordCup_trace b4b_root α β
  simp only [hentry, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at htr
  have h4 : (4 : hp_K) ≠ 0 := by exact_mod_cast hg6_natCast_ne_zero 4 (by norm_num)
  rw [hentry]
  split_ifs
  · rw [← htr]
    field_simp
    norm_num
  · rfl

end HodgeLean.Foundations.Program
