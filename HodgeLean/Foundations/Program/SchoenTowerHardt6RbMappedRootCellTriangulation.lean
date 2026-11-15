import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidRootCellTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellOpenCover
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbTriangulationHeightBaseChange
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientTargetGraphTransport
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbHeightBaseCellImage

/-! Coherent root cells acquire a common compatible triangulation in the original base and ambient coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_mapped_root_cell_triangulation {n : ℕ}
    (B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hB : B.faces.Finite)
    (r : B.faces → ℕ)
    (f : (s : B.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ s i, ContinuousOn (f s i) (convexHull ℝ (s.val : Set _)))
    (hfm : ∀ s x, x ∈ convexHull ℝ (s.val : Set _) → Monotone (fun i => f s i x))
    (hfs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) → StrictMono (fun i => f s i x))
    (ρ : ∀ s t : B.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρf : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set _) → f s i x = f t (ρ s t hts i) x)
    (g : (s : B.faces) → Fin (r s) → s2v_t11b_Formula (n + 1))
    (hg : ∀ s i z, z ∈ (g s i).realize ↔ ∃ x ∈ convexHull ℝ (s.val : Set _),
      (∀ j, z j.succ = x j) ∧ z 0 = f s i x)
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β B.space) (hβinj : Set.InjOn β B.space)
    (Gb : s2v_t11b_Formula (n + n))
    (hGb : ∀ z, z ∈ Gb.realize ↔ ∃ x ∈ B.space,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (v : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (Jv : s2v_t11b_Formula ((n + 1) + (n + 1)))
    (hJv : ∀ z, z ∈ Jv.realize ↔ ∃ y : EuclideanSpace ℝ (Fin (n + 1)),
      (∀ i, z (Fin.castAdd (n + 1) i) = y i) ∧ (∀ i, z (Fin.natAdd (n + 1) i) = v y i)) :
    ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      L.faces.Finite ∧ L.space = B.space ∧ ∃ parent : L.faces → B.faces,
      (∀ s, intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) ⊆
        intrinsicInterior ℝ (convexHull ℝ ((parent s).val : Set _))) ∧
      ∃ c : (s : L.faces) → s2v_hardt6rb_RootLabel (r (parent s)) → Set (EuclideanSpace ℝ (Fin (n + 1))),
      (∀ s a, c s a = v '' {z | ∃ x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)),
        (∀ i, z i.succ = β x i) ∧
        match a with
        | .inl i => z 0 = f (parent s) i x
        | .inr q => f (parent s) q.val.1 x < z 0 ∧ z 0 < f (parent s) q.val.2 x}) ∧
      ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))), K.faces.Finite ∧
        ∃ H : K.space ≃ₜ (⋃ i : (s : L.faces) × s2v_hardt6rb_RootLabel (r (parent s)), c i.1 i.2),
          (∀ s a, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin (n + 1)))),
            (↑R : Set _) ⊆ K.faces ∧ c s a = (fun x : K.space => (H x).val) ''
              {x : K.space | ∃ t ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑t : Set _))}) ∧
          ∃ G : s2v_t11b_Formula ((n + 1) + (n + 1)), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
            (∀ i, z (Fin.castAdd (n + 1) i) = x.val i) ∧ (∀ i, z (Fin.natAdd (n + 1) i) = (H x).val i) := by
  classical
  obtain ⟨e, he0, hes, _, _⟩ := s2v_hardt6rb_band_coordinate_equiv n
  obtain ⟨L, hL, hLB, parent, hHull, hInt, hparent, K, hK, H, hsel, G, hG⟩ :=
    s2v_hardt6rb_centroid_root_cell_triangulation B hB r f hfc hfm hfs ρ hρf g hg e he0 hes
  let I := (s : L.faces) × s2v_hardt6rb_RootLabel (r (parent s))
  let T : I → Set (EuclideanSpace ℝ (Fin n) × ℝ) := fun i => {p |
    p.1 ∈ convexHull ℝ (i.1.val : Set _) ∧ f (parent i.1) (s2v_hardt6rb_rootLabelLower i.2) p.1 ≤ p.2 ∧
    p.2 ≤ f (parent i.1) (s2v_hardt6rb_rootLabelUpper i.2) p.1}
  let O : I → Set (EuclideanSpace ℝ (Fin n) × ℝ) := fun i => {p |
    p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (i.1.val : Set _)) ∧
    match i.2 with
    | .inl a => p.2 = f (parent i.1) a p.1
    | .inr q => f (parent i.1) q.val.1 p.1 < p.2 ∧ p.2 < f (parent i.1) q.val.2 p.1}
  let U := ⋃ i, e '' T i
  let φ := fun z => e (β (e.symm z).1, (e.symm z).2)
  have hcover : (⋃ i, T i) = ⋃ i, O i :=
    s2v_hardt6rb_root_cell_open_cover L hL (fun s => r (parent s)) (fun s => f (parent s))
      (fun s x hx => hfm (parent s) x (hHull s hx)) (fun s x hx => hfs (parent s) x (hInt s hx))
      (fun s t hts => ρ (parent s) (parent t) (hparent s t hts))
      (fun s t hts a x hx => hρf (parent s) (parent t) (hparent s t hts) a x (hHull t hx))
      (fun s a => T ⟨s, a⟩) (fun s a => O ⟨s, a⟩) (fun _ _ => rfl)
      (fun s a => by cases a <;> rfl)
  have hU : U = ⋃ i, e '' O i := by
    change (⋃ i, e '' T i) = _
    rw [← Set.image_iUnion, hcover, Set.image_iUnion]
  have hbase : ∀ z ∈ U, (e.symm z).1 ∈ B.space := by
    intro z hz
    obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hz
    rw [e.symm_apply_apply, ← hLB]
    exact L.convexHull_subset_space i.1.property hp.1
  obtain ⟨k, Jk, hk, hJk⟩ := s2v_hardt6rb_triangulation_height_base_change K hK U H G hG
    B.space β hβ hβinj Gb hGb e he0 hes hbase
  obtain ⟨k', J, hk', hJ⟩ := s2v_hardt6rb_ambient_target_graph_transport K.space (φ '' U) k Jk hJk v Jv hJv
  let c (s : L.faces) (a : s2v_hardt6rb_RootLabel (r (parent s))) := v '' (φ '' (e '' O ⟨s, a⟩))
  have hc (s : L.faces) (a : s2v_hardt6rb_RootLabel (r (parent s))) :
      c s a = v '' {z | ∃ x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)),
        (∀ i, z i.succ = β x i) ∧
        match a with
        | .inl i => z 0 = f (parent s) i x
        | .inr q => f (parent s) q.val.1 x < z 0 ∧ z 0 < f (parent s) q.val.2 x} := by
    apply congrArg (fun S => v '' S)
    cases a with
    | inl a => exact s2v_hardt6rb_height_base_cell_image _ (fun x t => t = f (parent s) a x) β e he0 hes
    | inr q => exact s2v_hardt6rb_height_base_cell_image _ (fun x t => f (parent s) q.val.1 x < t ∧ t < f (parent s) q.val.2 x) β e he0 hes
  have hcU : (⋃ i : I, c i.1 i.2) = v '' (φ '' U) := by
    rw [hU, Set.image_iUnion, Set.image_iUnion]
  let H' := k'.trans (Homeomorph.setCongr hcU.symm)
  have hH' (x : K.space) : (H' x).val = v (φ (H x).val) := (hk' x).trans (congrArg v (hk x))
  refine ⟨L, hL, hLB, parent, hInt, c, hc, K, hK, H', ?_, J, hJ⟩
  intro s a
  obtain ⟨R, hR, heq⟩ := hsel ⟨s, a⟩
  refine ⟨R, hR, ?_⟩
  have heq' := congrArg (fun S => v '' (φ '' S)) heq
  cases a <;> simpa only [c, O, Set.image_image, Function.comp_def, ← hH'] using heq'

end HodgeLean.Foundations.Program
