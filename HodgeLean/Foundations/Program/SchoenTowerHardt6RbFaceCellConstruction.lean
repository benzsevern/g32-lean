import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMappedCellFormula
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRefinedCellClosure
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceFormula

/-! Actual endpoint data on a base face construct its nonempty Boolean cell and exact closure. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_cell_construction {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β L.space)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (s : L.faces) (graph : Bool) (l u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hl : ContinuousOn l (convexHull ℝ (↑s.val : Set _)))
    (hu : ContinuousOn u (convexHull ℝ (↑s.val : Set _)))
    (hlu : ∀ x ∈ convexHull ℝ (↑s.val : Set _), l x ≤ u x)
    (hgraph : graph = true → ∀ x ∈ convexHull ℝ (↑s.val : Set _), l x = u x)
    (hband : graph = false → ∀ x ∈ intrinsicInterior ℝ
      (convexHull ℝ (↑s.val : Set _)), l x < u x)
    (G : s2v_t11b_Formula (n + n))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ L.space,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (J : s2v_t11b_Formula ((n + 1) + (n + 1)))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
      (∀ i, z (Fin.castAdd (n + 1) i) = x i) ∧
      (∀ i, z (Fin.natAdd (n + 1) i) = e x i))
    (gl gu : s2v_t11b_Formula (n + 1))
    (hgl : ∀ z, z ∈ gl.realize ↔ ∃ x ∈ convexHull ℝ (↑s.val : Set _),
      z 0 = l x ∧ (∀ i, z i.succ = x i))
    (hgu : ∀ z, z ∈ gu.realize ↔ ∃ x ∈ convexHull ℝ (↑s.val : Set _),
      z 0 = u x ∧ (∀ i, z i.succ = x i)) :
    ∃ c : s2v_t11b_Formula (n + 1), c.realize.Nonempty ∧
      c.realize = e '' {z | ∃ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s.val : Set _)),
        (∀ i, z i.succ = β x i) ∧
        (if graph then z 0 = l x else l x < z 0 ∧ z 0 < u x)} ∧
      closure c.realize = e '' {z | ∃ x ∈ convexHull ℝ (↑s.val : Set _),
        (∀ i, z i.succ = β x i) ∧ l x ≤ z 0 ∧ z 0 ≤ u x} := by
  obtain ⟨U, hU⟩ := s2v_hardt6rb_open_face_formula s.val (L.indep s.property)
  have hsub : U.realize ⊆ convexHull ℝ (↑s.val : Set _) := by
    rw [hU]
    exact intrinsicInterior_subset
  have restrict (f : EuclideanSpace ℝ (Fin n) → ℝ) (F : s2v_t11b_Formula (n + 1))
      (hF : ∀ z, z ∈ F.realize ↔ ∃ x ∈ convexHull ℝ (↑s.val : Set _),
        z 0 = f x ∧ (∀ i, z i.succ = x i)) :
      ∃ R : s2v_t11b_Formula (n + 1), ∀ z, z ∈ R.realize ↔ ∃ x : U.realize,
        (∀ i, z i.succ = x.val i) ∧ z 0 = f x.val := by
    refine ⟨F.inter (s2v_hardt1_rename Fin.succ U), ?_⟩
    intro z
    change (z ∈ F.realize ∧ z ∈ (s2v_hardt1_rename Fin.succ U).realize) ↔ _
    rw [hF, s2v_hardt1_realize_rename]
    constructor
    · rintro ⟨⟨x, hx, ht, hz⟩, hbase⟩
      have he : WithLp.toLp 2 (fun i : Fin n => z i.succ) = x := by ext i; exact hz i
      rw [he] at hbase
      exact ⟨⟨x, hbase⟩, hz, ht⟩
    · rintro ⟨x, hz, ht⟩
      refine ⟨⟨x.val, hsub x.property, ht, hz⟩, ?_⟩
      have he : WithLp.toLp 2 (fun i : Fin n => z i.succ) = x.val := by ext i; exact hz i
      rw [he]
      exact x.property
  obtain ⟨R, hR⟩ := restrict l gl hgl
  obtain ⟨S, hS⟩ := restrict u gu hgu
  obtain ⟨c, hc⟩ := s2v_hardt6rb_mapped_cell_formula L.space U
    (hsub.trans (L.convexHull_subset_space s.property))
    (fun x => l x.val) (fun x => u x.val) R S hR hS β G hG e J hJ graph
  have hmodel : c.realize = e '' {z | ∃ x ∈ intrinsicInterior ℝ
      (convexHull ℝ (↑s.val : Set _)), (∀ i, z i.succ = β x i) ∧
      (if graph then z 0 = l x else l x < z 0 ∧ z 0 < u x)} := by
    rw [hc]
    congr 1
    ext z
    exact ⟨fun ⟨x, hx, ht⟩ => ⟨x.val, hU ▸ x.property, hx, ht⟩,
      fun ⟨x, hx, hz, ht⟩ => ⟨⟨x, hU.symm ▸ hx⟩, hz, ht⟩⟩
  refine ⟨c, ?_, hmodel,
    s2v_hardt6rb_refined_cell_closure L β hβ e s graph l u hl hu hlu hgraph hband c.realize hmodel⟩
  have hne : (convexHull ℝ (↑s.val : Set (EuclideanSpace ℝ (Fin n)))).Nonempty :=
    (L.nonempty_of_mem_faces s.property).to_set.mono (subset_convexHull ℝ _)
  obtain ⟨x, hx⟩ := hne.intrinsicInterior (convex_convexHull ℝ _)
  let t := if graph then l x else (l x + u x) / 2
  let z : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.cons t (fun i => β x i))
  refine ⟨e z, hmodel ▸ ⟨z, ⟨x, hx, fun _ => rfl, ?_⟩, rfl⟩⟩
  cases graph
  · have hlt := hband rfl x hx
    change l x < (l x + u x) / 2 ∧ (l x + u x) / 2 < u x
    constructor <;> linarith
  · rfl

end HodgeLean.Foundations.Program
