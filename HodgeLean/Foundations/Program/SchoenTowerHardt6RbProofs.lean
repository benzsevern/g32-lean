import HodgeLean.Foundations.Semialgebraic.CompatibleTriangulationCompact
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphs

/-! Fresh compatible compact triangulation interface.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compatible_triangulation_aux {n m : ℕ}
    (f : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ f.realize,
        (∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑S : Set _) ⊆ K.faces ∧
          f.realize ∩ (b j).realize =
            (fun x : K.space => (h x).val) ''
              {x : K.space | ∃ s ∈ S,
                x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ g : s2v_t11b_Formula (n + n),
          (∀ z, z ∈ g.realize ↔ ∃ x : K.space,
            (∀ i, z (Fin.castAdd n i) = x.val i) ∧
            (∀ i, z (Fin.natAdd n i) = (h x).val i)) ∧
          (∀ z : EuclideanSpace ℝ (Fin (n + n)),
            WithLp.toLp 2 (fun i =>
              Fin.addCases (fun j => z (Fin.natAdd n j))
                (fun j => z (Fin.castAdd n j)) i) ∈ g.realize ↔
              ∃ y : f.realize,
                (∀ i, z (Fin.castAdd n i) = y.val i) ∧
                (∀ i, z (Fin.natAdd n i) = (h.symm y).val i)) := by
  obtain ⟨K, hK, h, hmarks, g, hg⟩ :=
    Semialgebraic.CompatibleTriangulation.compact_triangulation n f hf b
  exact ⟨K, hK, h, hmarks, g, hg, s2v_hardt6rb_inverse_graph h g hg⟩

end HodgeLean.Foundations.Program
