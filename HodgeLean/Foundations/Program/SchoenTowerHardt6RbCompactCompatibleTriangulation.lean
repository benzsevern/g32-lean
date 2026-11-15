import HodgeLean.Foundations.Program.SchoenTowerHardt6RbTriangulationInduction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFinite

/-! Actual compact Boolean carriers have compatible finite geometric triangulations in every ambient dimension. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_compatible_triangulation (n : ℕ) : ∀ {m : ℕ}
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
  induction n with
  | zero =>
    intro m f hf b
    obtain ⟨K, hK, h, hmarks, G, hG, _⟩ := s2v_hardt6rb_finite_triangulation f (Set.toFinite _) b
    exact ⟨K, hK, h, hmarks, G, hG⟩
  | succ n ih =>
    intro m f hf b
    exact s2v_hardt6rb_triangulation_induction_step (fun {v} P hP D => ih P hP D) f hf b

end HodgeLean.Foundations.Program
