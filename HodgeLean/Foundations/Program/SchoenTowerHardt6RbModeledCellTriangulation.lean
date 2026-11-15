import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRankedModeledCells
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFiniteConvexCellTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubcomplexDifferenceSelection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubcomplexUnion

/-! Shared modeled cells yield actual finite geometric triangulations compatible with every open target cell. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_modeled_cell_triangulation {n : ℕ} {ι : Type*} [Fintype ι]
    (C T : ι → Set (EuclideanSpace ℝ (Fin n))) (D : ι → Finset ι) (rank : ι → ℕ)
    (hD : ∀ i j, j ∈ D i → rank j < rank i)
    (hcompact : ∀ i, IsCompact (C i)) (hconv : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (hboundary : ∀ i, C i \ intrinsicInterior ℝ (C i) = ⋃ j : D i, C j.val)
    (hsep : ∀ i j, j ≠ i → rank j ≤ rank i → C j ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i))
    (hTB : ∀ i, (⋃ j : D i, T j.val) ⊆ T i)
    (hTsep : ∀ i j, j ≠ i → rank j ≤ rank i → T j ∩ T i ⊆ ⋃ q : D i, T q.val)
    (model : ∀ i, C i ≃ₜ T i)
    (hmodel : ∀ i (x : C i), x.val ∉ intrinsicInterior ℝ (C i) ↔ (model i x).val ∈ ⋃ j : D i, T j.val)
    (F : ι → s2v_t11b_Formula n) (hF : ∀ i, (F i).realize = C i \ intrinsicInterior ℝ (C i))
    (J : ι → s2v_t11b_Formula (n + n))
    (hJ : ∀ i z, z ∈ (J i).realize ↔ ∃ x : C i,
      (∀ j, z (Fin.castAdd n j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (model i x).val j)) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)), K.faces.Finite ∧
      ∃ H : K.space ≃ₜ (⋃ i, T i),
        (∀ i, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑R : Set _) ⊆ K.faces ∧
          T i \ (⋃ j : D i, T j.val) = (fun x : K.space => (H x).val) ''
            {x : K.space | ∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ G : s2v_t11b_Formula (n + n), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
          (∀ j, z (Fin.castAdd n j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (H x).val j) := by
  classical
  obtain ⟨K, hK, hKs, hP⟩ := s2v_hardt6rb_finite_convex_cell_triangulation C D rank hD
    hcompact hconv hne hboundary hsep
  choose P hPf hPs hPK using hP
  obtain ⟨H₀, G, hH₀, hG⟩ := s2v_hardt6rb_ranked_modeled_cells C T D rank hD hcompact hconv hne
    hboundary hsep hTB hTsep model hmodel F hF J hJ
  let H := (Homeomorph.setCongr hKs).trans H₀
  have hH (i : ι) (x : K.space) : x.val ∈ C i ↔ (H x).val ∈ T i :=
    hH₀ i ((Homeomorph.setCongr hKs) x)
  refine ⟨K, hK, H, ?_, G, ?_⟩
  · intro i
    obtain ⟨Q, _, _, hQs, hQK⟩ := s2v_hardt6rb_subcomplex_union K hK
      (fun j : D i => P j.val) (fun j => hPK j.val)
    have hQs' : Q.space = ⋃ j : D i, C j.val := by simpa only [hPs] using hQs
    obtain ⟨R, hRK, hR⟩ := s2v_hardt6rb_subcomplex_difference_selection K (P i) Q hK (hPK i) hQK
    have hsel (x : K.space) :
        (∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))) ↔
        (H x).val ∈ T i \ (⋃ j : D i, T j.val) := by
      rw [hR, hPs, hQs']
      change (x.val ∈ C i ∧ x.val ∉ ⋃ j : D i, C j.val) ↔ _
      rw [hH]
      apply and_congr_right
      intro _
      apply not_congr
      simp only [Set.mem_iUnion]
      exact exists_congr (fun j => hH j.val x)
    refine ⟨R, hRK, ?_⟩
    ext y
    constructor
    · intro hy
      let q : (⋃ j, T j) := ⟨y, Set.mem_iUnion.mpr ⟨i, hy.1⟩⟩
      refine ⟨H.symm q, (hsel _).mpr ?_, ?_⟩
      · simpa only [H.apply_symm_apply] using hy
      · exact congrArg Subtype.val (H.apply_symm_apply q)
    · rintro ⟨x, hx, rfl⟩
      exact (hsel x).mp hx
  · intro z
    rw [hG]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hKs.symm ▸ x.property⟩, hx, hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hKs ▸ x.property⟩, hx, hy⟩

end HodgeLean.Foundations.Program
