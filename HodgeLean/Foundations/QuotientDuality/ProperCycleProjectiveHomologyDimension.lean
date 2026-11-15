import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveDimensionTriangulation
import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteComplexHomologyDimension

/-! # Ordinary homology above actual projective algebraic dimension -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Original projective complex schemes have zero ordinary rational homology above twice their actual algebraic dimension.
Source: properCycle_projective_dimension_triangulation; properCycle_finite_complex_homology_vanishes.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_homology_dimension_vanishes
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (d : ℕ)
    (hdim : topologicalKrullDim X.left ≤ d) (n : ℕ) (hn : 2*d < n) :
    Subsingleton (Homology ℚ (TopCat.of (ComplexPoint X)) n) := by
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  obtain ⟨a, K, hK, ⟨h⟩, hbound⟩ := properCycle_projective_dimension_triangulation X d hdim
  letI : LinearOrder (EuclideanSpace ℝ (Fin a)) := IsWellOrder.linearOrder WellOrderingRel
  have hvfinite : K.vertices.Finite :=
    Set.Finite.preimage (fun _ _ _ _ he => Finset.singleton_injective he) hK
  let V := hvfinite.toFinset
  have hV : ∀ b ∈ K.vertices, b ∈ V := fun b hb => hvfinite.mem_toFinset.mpr hb
  exact properCycle_homeomorph_homology_subsingleton
    (X := TopCat.of (ComplexPoint X)) (Y := TopCat.of K.space) h.symm n
      (properCycle_finite_complex_homology_vanishes K hK V hV (2*d) hbound n hn)

end HodgeLean.Foundations.QuotientDuality
