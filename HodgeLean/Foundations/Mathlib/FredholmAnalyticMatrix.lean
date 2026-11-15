module

public import Mathlib

/-! # Analytic kernel frames for constant-rank analytic matrix families -/

@[expose] public noncomputable section

open Set Filter Topology Module

namespace HodgeLean.Foundations

/-- A rank-`k` matrix has `k` columns forming a rank-`k` submatrix. -/
theorem b63r_mat_exists_cols {m n k : ℕ} (N : Matrix (Fin m) (Fin n) ℂ) (hN : N.rank = k) :
    ∃ c : Fin k → Fin n, (N.submatrix id c).rank = k := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ N.col
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  have hk : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hN]
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hk).symm
  refine ⟨a ∘ e, ?_⟩
  have hcol : (N.submatrix id (a ∘ e)).col = (N.col ∘ a) ∘ e := by
    funext j i; rfl
  rw [Matrix.rank_eq_finrank_span_cols, hcol, EquivLike.range_comp, finrank_span_eq_card hli, hk]

theorem b63r_mat_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.rank = n) :
    A.det ≠ 0 := by
  have hs : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_rank_eq_card.2 (by simpa using hA)
  have hu : IsUnit A := Matrix.mulVec_surjective_iff_isUnit.1 hs
  exact ((Matrix.isUnit_iff_isUnit_det A).1 hu).ne_zero

theorem b63r_mat_det_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
    {s : Set E} (A : E → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t ↦ A t i j) s) :
    AnalyticOnNhd ℂ (fun t ↦ (A t).det) s := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticOnNhd_fun_sum
  intro σ _
  apply analyticOnNhd_const.mul
  exact Finset.analyticOnNhd_fun_prod _ (fun i _ ↦ hA (σ i) i)


/-- The kernel vectors built from a nonvanishing minor via the adjugate. -/
def b63r_mat_vec {p q ρ m : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) (r : Fin ρ → Fin p)
    (c : Fin ρ → Fin q) (c' : Fin m → Fin q) (i : Fin m) : Fin q → ℂ :=
  fun x ↦ (if x = c' i then (A.submatrix r c).det else 0) -
    ∑ j, if x = c j then ((A.submatrix r c).adjugate * A.submatrix r c') j i else 0

/-- The adjugate vectors lie in the kernel of the selected rows. -/
theorem b63r_mat_vec_rows {p q ρ m : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) (r : Fin ρ → Fin p)
    (c : Fin ρ → Fin q) (c' : Fin m → Fin q) (i : Fin m) :
    (A.submatrix r id).mulVec (b63r_mat_vec A r c c' i) = 0 := by
  funext a
  have h := congrFun (congrFun (show (A.submatrix r c) * ((A.submatrix r c).adjugate *
    A.submatrix r c') = (A.submatrix r c).det • A.submatrix r c' by
      rw [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]) a) i
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul] at h
  simp only [Matrix.mulVec, dotProduct, b63r_mat_vec, Matrix.submatrix_apply, id, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.mul_sum, Pi.zero_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply] at h ⊢
  rw [h]; ring

/-- On a constant-rank analytic matrix family, the kernel has a local analytic frame near each
point, built from a nonvanishing minor via the adjugate.
Source: Kato, *Perturbation Theory for Linear Operators*, 2nd ed. (1976), Ch. II, §4. -/
theorem b63r_matrix_frame_core {k p q ρ : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin p) (Fin q) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun t ↦ M t i j) W)
    (hρ : ∀ t ∈ W, (M t).rank = ρ) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ v : Fin (q - ρ) → (Fin k → ℂ) → (Fin q → ℂ), (∀ i, AnalyticOnNhd ℂ (v i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ v i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ v i t) = LinearMap.ker (M t).mulVecLin := by
  obtain ⟨c, hc⟩ := b63r_mat_exists_cols (M t₀) (hρ t₀ ht₀)
  have hQ : ((M t₀).submatrix id c).transpose.rank = ρ := by rw [Matrix.rank_transpose, hc]
  obtain ⟨r, hr⟩ := b63r_mat_exists_cols _ hQ
  have hP₀ : ((M t₀).submatrix r c).det ≠ 0 := by
    apply b63r_mat_det_ne_zero
    rw [← Matrix.rank_transpose]
    simpa [Matrix.transpose_submatrix, Matrix.submatrix_submatrix] using hr
  have hPan : AnalyticOnNhd ℂ (fun t ↦ ((M t).submatrix r c).det) W :=
    b63r_mat_det_analytic _ (fun a b ↦ hM (r a) (c b))
  set W' : Set (Fin k → ℂ) := W ∩ (fun t ↦ ((M t).submatrix r c).det) ⁻¹' {0}ᶜ with hW'
  have hW'o : IsOpen W' := hPan.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hW'W : W' ⊆ W := Set.inter_subset_left
  -- injectivity of the selected columns
  have hcinj : Function.Injective c := by
    intro a b hab
    by_contra hne
    exact hP₀ (Matrix.det_zero_of_column_eq hne (fun l ↦ by simp [hab]))
  set s : Finset (Fin q) := Finset.univ \ Finset.univ.image c with hs
  have hscard : s.card = q - ρ := by
    rw [hs, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_image_of_injective _ hcinj]
    simp
  let c' : Fin (q - ρ) → Fin q := s.orderEmbOfFin hscard
  have hc'inj : Function.Injective c' := (s.orderEmbOfFin hscard).injective
  have hc'c : ∀ i j, c' i ≠ c j := by
    intro i j h
    have hm : c' i ∈ Finset.univ \ Finset.univ.image c := s.orderEmbOfFin_mem hscard i
    exact (Finset.mem_sdiff.1 hm).2 (Finset.mem_image.2 ⟨j, Finset.mem_univ _, h.symm⟩)
  refine ⟨W', hW'o, ⟨ht₀, hP₀⟩, hW'W, fun i t ↦ b63r_mat_vec (M t) r c c' i, ?_, ?_⟩
  · intro i
    apply AnalyticOnNhd.mono _ hW'W
    apply AnalyticOnNhd.pi
    intro x
    show AnalyticOnNhd ℂ (fun t ↦ b63r_mat_vec (M t) r c c' i x) W
    simp only [b63r_mat_vec]
    apply AnalyticOnNhd.sub
    · by_cases hx : x = c' i
      · simpa [hx] using hPan
      · simpa [hx] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ ↦ (0 : ℂ)) W)
    · apply Finset.analyticOnNhd_fun_sum
      intro j _
      by_cases hx : x = c j
      · simp only [hx, ite_true, Matrix.mul_apply]
        apply Finset.analyticOnNhd_fun_sum
        intro l _
        apply AnalyticOnNhd.mul
        · simp only [Matrix.adjugate_apply]
          apply b63r_mat_det_analytic
          intro a b
          simp only [Matrix.updateRow_apply, Matrix.submatrix_apply]
          by_cases ha : a = l
          · simpa [ha] using analyticOnNhd_const
          · simpa [ha] using hM (r a) (c b)
        · exact hM _ _
      · simpa [hx] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ ↦ (0 : ℂ)) W)
  · intro t ht
    have hPt : ((M t).submatrix r c).det ≠ 0 := ht.2
    have hli : LinearIndependent ℂ (fun i ↦ b63r_mat_vec (M t) r c c' i) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i₀
      have := congrFun hg (c' i₀)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b63r_mat_vec, hc'c,
        ite_false, Finset.sum_const_zero, sub_zero, hc'inj.eq_iff, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_right hPt
    refine ⟨hli, ?_⟩
    have hrank : (M t).rank = ρ := hρ t ht.1
    have hMr : ((M t).submatrix r id).rank = ρ := by
      apply le_antisymm (Matrix.rank_le_height _)
      have h1 := Matrix.rank_submatrix_le ((M t).submatrix r id) id c
      have h2 : ((M t).submatrix r c).rank = ρ := by
        rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hPt))]
        simp
      simpa [Matrix.submatrix_submatrix, h2] using h1
    have hdimM : finrank ℂ (LinearMap.ker (M t).mulVecLin) = q - ρ := by
      have := LinearMap.finrank_range_add_finrank_ker (M t).mulVecLin
      rw [← Matrix.rank, hrank, Module.finrank_fin_fun] at this
      omega
    have hdimMr : finrank ℂ (LinearMap.ker ((M t).submatrix r id).mulVecLin) = q - ρ := by
      have := LinearMap.finrank_range_add_finrank_ker ((M t).submatrix r id).mulVecLin
      rw [← Matrix.rank, hMr, Module.finrank_fin_fun] at this
      omega
    have hle : LinearMap.ker (M t).mulVecLin ≤ LinearMap.ker ((M t).submatrix r id).mulVecLin := by
      intro x hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      funext a
      have := congrFun hx (r a)
      simpa [Matrix.mulVec, dotProduct] using this
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hdimM, hdimMr])
    have hsle : Submodule.span ℂ (Set.range fun i ↦ b63r_mat_vec (M t) r c c' i) ≤
        LinearMap.ker (M t).mulVecLin := by
      rw [Submodule.span_le, heq]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact b63r_mat_vec_rows (M t) r c c' i
    apply Submodule.eq_of_le_of_finrank_eq hsle
    rw [finrank_span_eq_card hli, hdimM, Fintype.card_fin]

end HodgeLean.Foundations
