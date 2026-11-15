import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineRootCellGeometry
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSharedRootBoundarySystem
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellModels
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineBandModelGraph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConvexCellBoundaryFormulas
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbModeledCellLinearTriangulation
import Mathlib.Data.Fintype.Sigma

/-! Coherent affine root models and actual endpoint graphs construct a common compatible root cell triangulation. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_coherent_root_cell_triangulation {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hL : L.faces.Finite)
    (r : L.faces → ℕ)
    (A : (s : L.faces) → Fin (r s) → (EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] ℝ))
    (f : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ s i, Continuous (A s i))
    (hfc : ∀ s i, ContinuousOn (f s i) (convexHull ℝ (s.val : Set _)))
    (hAm : ∀ s x, x ∈ convexHull ℝ (s.val : Set _) → Monotone (fun i => A s i x))
    (hfm : ∀ s x, x ∈ convexHull ℝ (s.val : Set _) → Monotone (fun i => f s i x))
    (hAs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) → StrictMono (fun i => A s i x))
    (hfs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) → StrictMono (fun i => f s i x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρA : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set _) → A s i x = A t (ρ s t hts i) x)
    (hρf : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set _) → f s i x = f t (ρ s t hts i) x)
    (g : (s : L.faces) → Fin (r s) → s2v_t11b_Formula (n + 1))
    (hg : ∀ s i z, z ∈ (g s i).realize ↔ ∃ x ∈ convexHull ℝ (s.val : Set _),
      (∀ j, z j.succ = x j) ∧ z 0 = f s i x)
    (e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (he0 : ∀ p, e p 0 = p.2) (hes : ∀ p i, e p i.succ = p.1 i) :
    let I := (s : L.faces) × s2v_hardt6rb_RootLabel (r s)
    let T : I → Set (EuclideanSpace ℝ (Fin n) × ℝ) := fun i => {p |
      p.1 ∈ convexHull ℝ (i.1.val : Set _) ∧ f i.1 (s2v_hardt6rb_rootLabelLower i.2) p.1 ≤ p.2 ∧
      p.2 ≤ f i.1 (s2v_hardt6rb_rootLabelUpper i.2) p.1}
    let O : I → Set (EuclideanSpace ℝ (Fin n) × ℝ) := fun i => {p |
      p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (i.1.val : Set _)) ∧
      match i.2 with
      | .inl a => p.2 = f i.1 a p.1
      | .inr q => f i.1 q.val.1 p.1 < p.2 ∧ p.2 < f i.1 q.val.2 p.1}
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))), K.faces.Finite ∧
      ∃ H : K.space ≃ₜ (⋃ i, e '' T i),
        (∀ i, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin (n + 1)))),
          (↑R : Set _) ⊆ K.faces ∧ e '' O i = (fun x : K.space => (H x).val) ''
            {x : K.space | ∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ G : s2v_t11b_Formula ((n + 1) + (n + 1)), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
          (∀ j, z (Fin.castAdd (n + 1) j) = x.val j) ∧
          (∀ j, z (Fin.natAdd (n + 1) j) = (H x).val j) := by
  classical
  intro I T O
  let C : I → Set (EuclideanSpace ℝ (Fin n) × ℝ) := fun i => {p |
    p.1 ∈ convexHull ℝ (i.1.val : Set _) ∧ A i.1 (s2v_hardt6rb_rootLabelLower i.2) p.1 ≤ p.2 ∧
      p.2 ≤ A i.1 (s2v_hardt6rb_rootLabelUpper i.2) p.1}
  letI : Fintype L.faces := hL.fintype
  letI (s : L.faces) : Fintype (s2v_hardt6rb_RootLabel (r s)) := Fintype.ofFinite _
  letI : Fintype I := inferInstance
  let rank : I → ℕ := fun i => 2 * i.1.val.card + s2v_hardt6rb_rootLabelStep i.2
  let D : I → Finset I := fun i => Finset.univ.filter (fun j => rank j < rank i ∧ C j ⊆ C i)
  have hD (i j : I) : j ∈ D i ↔ rank j < rank i ∧ C j ⊆ C i := by simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
  have hgeom (i : I) := s2v_hardt6rb_affine_root_cell_geometry L r A hA hAm hAs i.1 i.2
  have hsource := s2v_hardt6rb_root_cell_boundary_system L r (fun s i => A s i) hAm hAs ρ hρA
    (fun s a => C ⟨s, a⟩) (fun s a => intrinsicInterior ℝ (C ⟨s, a⟩)) (fun _ _ => rfl)
    (fun s a => (hgeom ⟨s, a⟩).2.2.2) D hD
  have hshared := s2v_hardt6rb_shared_root_boundary_system L r (fun s i => A s i) f hAm hAs hfm hfs ρ hρA hρf
    (fun s a => C ⟨s, a⟩) (fun s a => intrinsicInterior ℝ (C ⟨s, a⟩))
    (fun s a => T ⟨s, a⟩) (fun s a => O ⟨s, a⟩)
    (fun _ _ => rfl) (fun s a => (hgeom ⟨s, a⟩).2.2.2) (fun _ _ => rfl) (fun s a => by cases a <;> rfl) D hD
  have htarget (i : I) : T i \ O i = ⋃ j : D i, T j.val := hshared.2.1 i
  have hTB (i : I) : (⋃ j : D i, T j.val) ⊆ T i := by rw [← htarget]; exact Set.sdiff_subset
  have hTsep : ∀ i j : I, j ≠ i → rank j ≤ rank i → T j ∩ T i ⊆ ⋃ q : D i, T q.val := by
    intro i j hne hr
    rw [← htarget]
    exact hshared.2.2 i j hne hr
  have hmodels (i : I) := s2v_hardt6rb_root_cell_models L r f (fun s a => A s a) hfc
    (fun s a => (hA s a).continuousOn) hfm hAm hfs hAs ρ hρf hρA i.1 i.2
  choose model hmodelEq hmodelOpen using hmodels
  have hmodel (i : I) (x : C i) : x.val ∉ intrinsicInterior ℝ (C i) ↔
      (model i x).val ∈ ⋃ j : D i, T j.val := by
    rw [← htarget]
    change _ ↔ (model i x).val ∈ T i ∧ (model i x).val ∉ O i
    rw [and_iff_right (model i x).property]
    apply not_congr
    rw [(hgeom i).2.2.2]
    rcases i with ⟨s, a⟩
    cases a <;> exact hmodelOpen _ x
  obtain ⟨F, hF⟩ := s2v_hardt6rb_convex_cell_boundary_formulas e C D rank
    (fun i j hj => ((hD i j).mp hj).1) (fun i => (hgeom i).1) (fun i => (hgeom i).2.1)
    (fun i => (hgeom i).2.2.1) hsource.1 hsource.2
  have hgraphs (i : I) := s2v_hardt6rb_affine_band_model_graph i.1.val
    (A i.1 (s2v_hardt6rb_rootLabelLower i.2)) (A i.1 (s2v_hardt6rb_rootLabelUpper i.2))
    (f i.1 (s2v_hardt6rb_rootLabelLower i.2)) (f i.1 (s2v_hardt6rb_rootLabelUpper i.2))
    (g i.1 (s2v_hardt6rb_rootLabelLower i.2)) (g i.1 (s2v_hardt6rb_rootLabelUpper i.2))
    (hg i.1 _) (hg i.1 _) (model i) (hmodelEq i) e he0 hes (Fin.castAdd (n + 1)) (Fin.natAdd (n + 1))
  choose J hJ using hgraphs
  obtain ⟨K, hK, H, hmarks, G, hG⟩ := s2v_hardt6rb_modeled_cell_linear_triangulation e C T D rank
    (fun i j hj => ((hD i j).mp hj).1) (fun i => (hgeom i).1) (fun i => (hgeom i).2.1)
    (fun i => (hgeom i).2.2.1) hsource.1 hsource.2 hTB hTsep model hmodel F hF J hJ
  refine ⟨K, hK, H, ?_, G, hG⟩
  intro i
  have hOT : O i ⊆ T i := by
    rintro p ⟨hp, ho⟩
    refine ⟨intrinsicInterior_subset hp, ?_⟩
    rcases i with ⟨s, a⟩
    cases a with
    | inl a => exact ⟨ho.ge, ho.le⟩
    | inr q => exact ⟨ho.1.le, ho.2.le⟩
  have heq : T i \ (⋃ j : D i, T j.val) = O i := by
    rw [← htarget]
    ext p
    simp only [Set.mem_sdiff]
    exact ⟨fun hp => by by_contra hn; exact hp.2 ⟨hp.1, hn⟩,
      fun hp => ⟨hOT hp, fun hn => hn.2 hp⟩⟩
  simpa only [heq] using hmarks i

end HodgeLean.Foundations.Program
