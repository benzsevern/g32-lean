import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRankedConvexCells
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactCellBoundaryAlternative

/-! Actual common finite geometric triangulation of a compact convex cell system with ranked boundaries. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_finite_convex_cell_triangulation {E ι : Type*} [DecidableEq E] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : ι → Set E) (D : ι → Finset ι) (rank : ι → ℕ)
    (hD : ∀ i j, j ∈ D i → rank j < rank i)
    (hcompact : ∀ i, IsCompact (C i)) (hconv : ∀ i, Convex ℝ (C i))
    (hne : ∀ i, (C i).Nonempty)
    (hboundary : ∀ i, C i \ intrinsicInterior ℝ (C i) = ⋃ j : D i, C j.val)
    (hsep : ∀ i j, j ≠ i → rank j ≤ rank i → C j ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i)) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = ⋃ i, C i ∧
      ∀ i, ∃ P : Geometry.SimplicialComplex ℝ E,
        P.faces.Finite ∧ P.space = C i ∧ P.faces ⊆ K.faces := by
  classical
  choose a ha using fun i => (hne i).intrinsicInterior (hconv i)
  exact s2v_hardt6rb_ranked_convex_cells C D rank hD hcompact hconv a ha hboundary hsep
    (fun i => s2v_hardt6rb_compact_cell_boundary_alternative (C i) (hcompact i) (a i) (ha i))

end HodgeLean.Foundations.Program
