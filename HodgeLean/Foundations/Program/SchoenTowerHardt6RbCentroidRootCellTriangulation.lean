import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCoherentRootCellTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidAffineRoots
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbEndpointGraphRestriction

/-! Centroid subdivision constructs the affine models needed for a common root cell triangulation. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_root_cell_triangulation {n : ℕ}
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
    (e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (he0 : ∀ p, e p 0 = p.2) (hes : ∀ p i, e p i.succ = p.1 i) :
    ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      L.faces.Finite ∧ L.space = B.space ∧ ∃ parent : L.faces → B.faces,
      (∀ s, convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) ⊆
        convexHull ℝ ((parent s).val : Set _)) ∧
      (∀ s, intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) ⊆
        intrinsicInterior ℝ (convexHull ℝ ((parent s).val : Set _))) ∧
      (∀ s t, t.val ⊆ s.val → (parent t).val ⊆ (parent s).val) ∧
    let I := (s : L.faces) × s2v_hardt6rb_RootLabel (r (parent s))
    let T : I → Set (EuclideanSpace ℝ (Fin n) × ℝ) := fun i => {p |
      p.1 ∈ convexHull ℝ (i.1.val : Set _) ∧ f (parent i.1) (s2v_hardt6rb_rootLabelLower i.2) p.1 ≤ p.2 ∧
      p.2 ≤ f (parent i.1) (s2v_hardt6rb_rootLabelUpper i.2) p.1}
    let O : I → Set (EuclideanSpace ℝ (Fin n) × ℝ) := fun i => {p |
      p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (i.1.val : Set _)) ∧
      match i.2 with
      | .inl a => p.2 = f (parent i.1) a p.1
      | .inr q => f (parent i.1) q.val.1 p.1 < p.2 ∧ p.2 < f (parent i.1) q.val.2 p.1}
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))), K.faces.Finite ∧
      ∃ H : K.space ≃ₜ (⋃ i, e '' T i),
        (∀ i, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin (n + 1)))),
          (↑R : Set _) ⊆ K.faces ∧ e '' O i = (fun x : K.space => (H x).val) ''
            {x : K.space | ∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ G : s2v_t11b_Formula ((n + 1) + (n + 1)), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
          (∀ j, z (Fin.castAdd (n + 1) j) = x.val j) ∧
          (∀ j, z (Fin.natAdd (n + 1) j) = (H x).val j) := by
  classical
  obtain ⟨L, hL, hLB, parent, _, hHull, hInt, hparent, A, hA, _, hAm, hAs, hρA⟩ :=
    s2v_hardt6rb_centroid_affine_roots B hB r f hfm hfs ρ hρf
  let R : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r (parent s)) → Fin (r (parent t)) :=
    fun s t hts => ρ (parent s) (parent t) (hparent s t hts)
  have hgraphs (s : L.faces) (i : Fin (r (parent s))) :
      ∃ H : s2v_t11b_Formula (n + 1), ∀ z, z ∈ H.realize ↔ ∃ x ∈ convexHull ℝ (s.val : Set _),
        (∀ j, z j.succ = x j) ∧ z 0 = f (parent s) i x := by
    obtain ⟨F, hF⟩ := s2v_hardt6rb_finite_convexHull_formula
      (s.val : Set (EuclideanSpace ℝ (Fin n))) s.val.finite_toSet
    obtain ⟨H, hH⟩ := s2v_hardt6rb_endpoint_graph_restriction _ (f (parent s) i)
      (g (parent s) i) (hg (parent s) i) F (fun x hx => hHull s (hF ▸ hx))
    exact ⟨H, fun z => by simpa only [hF] using hH z⟩
  choose H hH using hgraphs
  refine ⟨L, hL, hLB, parent, hHull, hInt, hparent, ?_⟩
  obtain ⟨K, hK, k, hmarks, G, hG⟩ := s2v_hardt6rb_coherent_root_cell_triangulation L hL (fun s => r (parent s)) A (fun s => f (parent s))
    hA (fun s i => (hfc (parent s) i).mono (hHull s))
    hAm (fun s x hx => hfm (parent s) x (hHull s hx))
    hAs (fun s x hx => hfs (parent s) x (hInt s hx)) R
    (fun s t hts i x hx => hρA s t hts (hparent s t hts) i hx)
    (fun s t hts i x hx => hρf (parent s) (parent t) (hparent s t hts) i x (hHull t hx))
    H hH e he0 hes
  intro I T O
  refine ⟨K, hK, k, ?_, G, hG⟩
  rintro ⟨s, a⟩
  cases a <;> exact hmarks _

end HodgeLean.Foundations.Program
