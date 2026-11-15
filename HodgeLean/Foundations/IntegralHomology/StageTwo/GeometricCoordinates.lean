import HodgeLean.Foundations.IntegralHomology.StageTwo.SupportedDistribution
import HodgeLean.Foundations.IntegralHomology.StageTwo.CoordinateSpace
import HodgeLean.Foundations.IntegralHomology.StageTwo.GeometricFaces
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairVertexCoordinates

/-! Geometric vertex coordinates recover barycentric distributions.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Convexity
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem geometric_vertex_coordinates (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) :
    ∃ c : E → E → ℝ, ∀ (s : Finset E), s ∈ K.faces →
      ∀ (w : StdSimplex ℝ s) (b : E),
        c b (barycentricPoint (fun a : s => a.val) w) =
          (w.map (fun a : s => a.val)).weights b := by
  classical
  letI : LinearOrder E := linearOrderOfSTO WellOrderingRel
  obtain ⟨c, _, hc⟩ :=
    Semialgebraic.CompatibleTriangulation.Helpers.s2e_pair_vertex_coordinates K hK
  refine ⟨c, ?_⟩
  intro s hs w b
  let w' : stdSimplex ℝ s := ⟨fun a => w.weights a, w.nonneg, w.total_of_fintype⟩
  have h := hc b s hs w'
  change c b (∑ a : s, w.weights a • a.val) =
    (if hb : b ∈ s then w.weights ⟨b, hb⟩ else 0) at h
  change c b (barycentricPoint (fun a : s => a.val) w) =
    Finsupp.mapDomain (fun a : s => a.val) w.weights b
  rw [barycentricPoint, Finsupp.sum_fintype _ _ (by simp)]
  by_cases hb : b ∈ s
  · rw [dif_pos hb] at h
    exact h.trans (Finsupp.mapDomain_apply_of_injective Subtype.val_injective
      w.weights (⟨b, hb⟩ : s)).symm
  · rw [dif_neg hb] at h
    exact h.trans (Finsupp.mapDomain_of_notMem_range w.weights b (by
      rintro ⟨a, ha⟩
      exact hb (ha ▸ a.property))).symm

theorem indexed_geometric_coordinate_recovery [DecidableEq E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (v : Fin (n + 1) → E) (hv : Function.Injective v) :
    ∃ c : E → E → ℝ, ∀ (p : faceCoordinateSpace (indexedFaces K v)) (i : Fin (n + 1)),
      c (v i) (barycentricPoint v p.val) = p.val.weights i := by
  classical
  obtain ⟨c, hc⟩ := geometric_vertex_coordinates K hK
  refine ⟨c, ?_⟩
  intro p i
  obtain ⟨s, hs, hp⟩ := p.property
  obtain ⟨u, hu, hpoint⟩ := supported_distribution v p.val s hp
  have h := hc (s.image v) hs u (v i)
  rw [hpoint, hu] at h
  exact h.trans (Finsupp.mapDomain_apply_of_injective hv p.val.weights i)

end HodgeLean.Foundations.IntegralHomology.StageTwo
