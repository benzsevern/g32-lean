import HodgeLean.Foundations.Program.SchoenTowerHardt6RbModeledCellTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceTransport

/-! Actual linear ambient coordinates transport modeled cell triangulations and their Boolean graphs. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_modeled_cell_linear_triangulation {n : ℕ} {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (C T : ι → Set E) (D : ι → Finset ι) (rank : ι → ℕ)
    (hD : ∀ i j, j ∈ D i → rank j < rank i)
    (hcompact : ∀ i, IsCompact (C i)) (hconv : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (hboundary : ∀ i, C i \ intrinsicInterior ℝ (C i) = ⋃ j : D i, C j.val)
    (hsep : ∀ i j, j ≠ i → rank j ≤ rank i → C j ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i))
    (hTB : ∀ i, (⋃ j : D i, T j.val) ⊆ T i)
    (hTsep : ∀ i j, j ≠ i → rank j ≤ rank i → T j ∩ T i ⊆ ⋃ q : D i, T q.val)
    (model : ∀ i, C i ≃ₜ T i)
    (hmodel : ∀ i (x : C i), x.val ∉ intrinsicInterior ℝ (C i) ↔ (model i x).val ∈ ⋃ j : D i, T j.val)
    (F : ι → s2v_t11b_Formula n) (hF : ∀ i, (F i).realize = e '' (C i \ intrinsicInterior ℝ (C i)))
    (J : ι → s2v_t11b_Formula (n + n))
    (hJ : ∀ i z, z ∈ (J i).realize ↔ ∃ x : C i,
      (∀ j, z (Fin.castAdd n j) = e x.val j) ∧ (∀ j, z (Fin.natAdd n j) = e (model i x).val j)) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)), K.faces.Finite ∧
      ∃ H : K.space ≃ₜ (⋃ i, e '' T i),
        (∀ i, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑R : Set _) ⊆ K.faces ∧
          e '' (T i \ (⋃ j : D i, T j.val)) = (fun x : K.space => (H x).val) ''
            {x : K.space | ∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ G : s2v_t11b_Formula (n + n), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
          (∀ j, z (Fin.castAdd n j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (H x).val j) := by
  classical
  let C' : ι → Set (EuclideanSpace ℝ (Fin n)) := fun i => e '' C i
  let T' : ι → Set (EuclideanSpace ℝ (Fin n)) := fun i => e '' T i
  have hInt (i : ι) : intrinsicInterior ℝ (C' i) = e '' intrinsicInterior ℝ (C i) :=
    e.toLinearEquiv.toAffineEquiv.intrinsicInterior_image (C i)
  have hbd (i : ι) : C' i \ intrinsicInterior ℝ (C' i) = e '' (C i \ intrinsicInterior ℝ (C i)) := by
    rw [hInt, Set.image_sdiff e.injective]
  let k (i : ι) : C i ≃ₜ C' i := e.toHomeomorph.image (C i)
  let t (i : ι) : T i ≃ₜ T' i := e.toHomeomorph.image (T i)
  let model' (i : ι) : C' i ≃ₜ T' i := (k i).symm.trans ((model i).trans (t i))
  have hk (i : ι) (y : C' i) : e ((k i).symm y).val = y.val :=
    congrArg Subtype.val ((k i).apply_symm_apply y)
  have hboundary' (i : ι) : C' i \ intrinsicInterior ℝ (C' i) = ⋃ j : D i, C' j.val := by
    rw [hbd, hboundary, Set.image_iUnion]
  have hsep' : ∀ i j, j ≠ i → rank j ≤ rank i →
      C' j ∩ C' i ⊆ C' i \ intrinsicInterior ℝ (C' i) := by
    intro i j hji hr
    rw [hbd]
    change (e '' C j) ∩ (e '' C i) ⊆ _
    rw [← Set.image_inter e.injective]
    exact Set.image_mono (hsep i j hji hr)
  have hTB' (i : ι) : (⋃ j : D i, T' j.val) ⊆ T' i := by
    change (⋃ j : D i, e '' T j.val) ⊆ e '' T i
    rw [← Set.image_iUnion]
    exact Set.image_mono (hTB i)
  have hTsep' : ∀ i j, j ≠ i → rank j ≤ rank i → T' j ∩ T' i ⊆ ⋃ q : D i, T' q.val := by
    intro i j hji hr
    change (e '' T j) ∩ (e '' T i) ⊆ ⋃ q : D i, e '' T q.val
    rw [← Set.image_inter e.injective, ← Set.image_iUnion]
    exact Set.image_mono (hTsep i j hji hr)
  have hmodel' (i : ι) (y : C' i) : y.val ∉ intrinsicInterior ℝ (C' i) ↔
      (model' i y).val ∈ ⋃ j : D i, T' j.val := by
    rw [hInt, ← hk i y]
    change e ((k i).symm y).val ∉ e '' intrinsicInterior ℝ (C i) ↔
      e (model i ((k i).symm y)).val ∈ ⋃ j : D i, e '' T j.val
    rw [← Set.image_iUnion]
    simpa only [Set.mem_image, e.injective.eq_iff, exists_eq_right] using hmodel i ((k i).symm y)
  have hJ' (i : ι) (z) : z ∈ (J i).realize ↔ ∃ y : C' i,
      (∀ j, z (Fin.castAdd n j) = y.val j) ∧ (∀ j, z (Fin.natAdd n j) = (model' i y).val j) := by
    rw [hJ]
    constructor
    · rintro ⟨x, hx, hy⟩
      refine ⟨k i x, hx, ?_⟩
      change ∀ j, z (Fin.natAdd n j) = e (model i ((k i).symm (k i x))).val j
      simpa only [(k i).symm_apply_apply] using hy
    · rintro ⟨y, hx, hy⟩
      exact ⟨(k i).symm y, fun j => (hx j).trans (congrArg (fun v => v j) (hk i y)).symm, hy⟩
  obtain ⟨K, hK, H, hmarks, G, hG⟩ := s2v_hardt6rb_modeled_cell_triangulation C' T' D rank hD
    (fun i => (hcompact i).image e.continuous) (fun i => (hconv i).linear_image e.toLinearMap)
    (fun i => (hne i).image e) hboundary' hsep' hTB' hTsep' model' hmodel'
    F (fun i => (hF i).trans (hbd i).symm) J hJ'
  refine ⟨K, hK, H, ?_, G, hG⟩
  intro i
  obtain ⟨R, hR, heq⟩ := hmarks i
  refine ⟨R, hR, ?_⟩
  rw [Set.image_sdiff e.injective, Set.image_iUnion]
  exact heq

end HodgeLean.Foundations.Program
