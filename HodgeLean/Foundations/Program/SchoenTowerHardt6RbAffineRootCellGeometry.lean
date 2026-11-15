import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellLabels
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactAmbientBand
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConvexAffineBand
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineBandInterior
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineGraphInterior
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidIntrinsic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Actual affine root cells are nonempty compact convex carriers with their prescribed intrinsic interiors. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_root_cell_geometry {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) (r : L.faces → ℕ)
    (A : (s : L.faces) → Fin (r s) → (E →ᵃ[ℝ] ℝ))
    (hA : ∀ s i, Continuous (A s i))
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set E) → Monotone (fun i => A s i x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) →
      StrictMono (fun i => A s i x))
    (s : L.faces) (a : s2v_hardt6rb_RootLabel (r s)) :
    let C : Set (E × ℝ) := {p | p.1 ∈ convexHull ℝ (s.val : Set E) ∧
      A s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧
      p.2 ≤ A s (s2v_hardt6rb_rootLabelUpper a) p.1}
    IsCompact C ∧ Convex ℝ C ∧ C.Nonempty ∧
      intrinsicInterior ℝ C = {p : E × ℝ |
        p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ∧
        match a with
        | .inl i => p.2 = A s i p.1
        | .inr q => A s q.val.1 p.1 < p.2 ∧ p.2 < A s q.val.2 p.1} := by
  dsimp only
  have ho : ∀ x ∈ convexHull ℝ (s.val : Set E),
      A s (s2v_hardt6rb_rootLabelLower a) x ≤ A s (s2v_hardt6rb_rootLabelUpper a) x :=
    fun x hx => hm s x hx (s2v_hardt6rb_root_label_endpoints a).1
  have hx := s2v_hardt6rb_centroid_intrinsic s.val (L.nonempty_of_mem_faces s.property)
  refine ⟨s2v_hardt6rb_compact_ambient_band _ (s.val.finite_toSet.isCompact_convexHull ℝ)
    _ _ (hA s _).continuousOn (hA s _).continuousOn ho,
    s2v_hardt6rb_convex_affine_band _ (convex_convexHull ℝ _) _ _,
    ⟨(s.val.centroid ℝ id, A s (s2v_hardt6rb_rootLabelLower a) (s.val.centroid ℝ id)),
      intrinsicInterior_subset hx, le_rfl, ho _ (intrinsicInterior_subset hx)⟩, ?_⟩
  cases a with
  | inl i =>
    have he : {p : E × ℝ | p.1 ∈ convexHull ℝ (s.val : Set E) ∧ A s i p.1 ≤ p.2 ∧ p.2 ≤ A s i p.1} =
        {p : E × ℝ | p.1 ∈ convexHull ℝ (s.val : Set E) ∧ p.2 = A s i p.1} := by
      ext p
      exact and_congr Iff.rfl ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
    change intrinsicInterior ℝ {p : E × ℝ | p.1 ∈ convexHull ℝ (s.val : Set E) ∧
      A s i p.1 ≤ p.2 ∧ p.2 ≤ A s i p.1} = _
    rw [he]
    exact s2v_hardt6rb_affine_graph_interior _ (convex_convexHull ℝ _) (A s i)
  | inr q =>
    exact s2v_hardt6rb_affine_band_interior _ (convex_convexHull ℝ _) _ _ (hA s _) (hA s _) ho
      ⟨_, intrinsicInterior_subset hx, hs s _ hx (by have hq := q.property; change q.val.1.val < q.val.2.val; omega)⟩

end HodgeLean.Foundations.Program
