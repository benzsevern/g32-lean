import HodgeLean.Foundations.Program.SchoenTransferC1a5BoundaryGeometryHelpers

/-! Probability coordinates on realized standard boundaries.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- The realized positive-dimensional boundary consists exactly of vectors with a zero coordinate.
Source: Mathlib StdSimplex.mem_range_map_iff and actual boundary face representatives. -/
lemma c1a5_boundary_coordinate_range (n : ℕ) :
    Set.range (fun y : SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet) ↦
      ⦋n + 1⦌.toTopHomeo (SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι y)) =
      setOf (fun p : StdSimplex ℝ (Fin (n + 2)) ↦ ∃ i : Fin (n + 2), p.weights i = 0) := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨i, s, hs⟩ := c1a5_boundary_realization_exists_face n y
    refine ⟨i, ?_⟩
    rw [← hs]
    exact (congrArg (fun q ↦ (⦋n + 1⦌.toTopHomeo q).weights i)
      (c1a5_boundary_coface_comp i s)).trans
        ((congrArg (fun v ↦ v.weights i)
          (SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) s)).trans
            (c1a5_coface_weight_zero i _))
  · rintro ⟨i, hi⟩
    obtain ⟨z, hz⟩ := c1a5_coface_lift i p hi
    let u := ⦋n⦌.toTopHomeo.symm z
    refine ⟨SSet.toTop.map (SSet.boundary.ι i) u, ?_⟩
    exact (congrArg ⦋n + 1⦌.toTopHomeo (c1a5_boundary_coface_comp i u)).trans
      ((SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) u).trans
        (by simpa only [u, Homeomorph.apply_symm_apply] using hz))

/-- Actual realization coordinates identify a boundary with the zero-coordinate subspace.
Source: Mathlib IsEmbedding.toHomeomorph and actual boundary coordinate range. -/
def c1a5_boundary_coordinate_homeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet) ≃ₜ
      {p : StdSimplex ℝ (Fin (n + 2)) // ∃ i : Fin (n + 2), p.weights i = 0} := by
  have he : Topology.IsEmbedding
      (fun y : SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet) ↦
        ⦋n + 1⦌.toTopHomeo (SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι y)) :=
    (SimplexCategory.toTopHomeo ⦋n + 1⦌).isEmbedding.comp
      (c1a5_boundary_realization_isClosedEmbedding (n + 1)).isEmbedding
  exact he.toHomeomorph.trans (Homeomorph.setCongr (c1a5_boundary_coordinate_range n))

example (n : ℕ) := c1a5_boundary_coordinate_homeomorph n

end HodgeLean.Foundations.Program
