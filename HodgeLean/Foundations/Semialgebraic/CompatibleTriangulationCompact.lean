import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactCompatibleTriangulation

/-! Compact forward-graph triangulation below the full pair interfaces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation

/-- Compact compatible triangulation.
Source: Coste, An Introduction to Semialgebraic Geometry (2002), Theorem 4.4; source declaration s2v_hardt6rb_compact_compatible_triangulation. -/
theorem compact_triangulation (n : ℕ) : ∀ {m : ℕ}
    (f : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (b : Fin m → s2v_t11b_Formula n),
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ f.realize,
        (∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑S : Set _) ⊆ K.faces ∧
          f.realize ∩ (b j).realize = (fun x : K.space => (h x).val) ''
            {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ G : s2v_t11b_Formula (n + n), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
          (∀ i, z (Fin.castAdd n i) = x.val i) ∧
          (∀ i, z (Fin.natAdd n i) = (h x).val i) := by
  exact s2v_hardt6rb_compact_compatible_triangulation n

end Semialgebraic.CompatibleTriangulation
