import HodgeLean.Foundations.QuotientDuality.PersistenceAmbientCollapseComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceFinitePatchAssembly

/-! Actual locus-collapse homology comparison on finite projective covers. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_finite_cover_closed_locus_collapse_homology_bijective
    (K : Type) [CommRing K] [Algebra ℚ K]
    (W B E : Over (Spec ↧ℂ)) [IsProjective B.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ W) [IsClosedImmersion j.left]
    (a : ComplexPoint W) (ha : a ∈ Set.range (Point.map j)) (n : ℕ) :
    Function.Bijective (relativeHomologyMap K n
      (persistenceCollapseLocusPairMap (Set.range (Point.map j)) a ha)) := by
  obtain ⟨P, hP, hAP, r, H, hfixed, hret⟩ :=
    persistence_finite_cover_closed_locus_ambient_deformation W B E β j
  exact persistence_ambient_collapse_relative_homology_bijective K _ P
    (isClosed_range_map_of_closedImmersion j) hP hAP r H hfixed hret a ha n

end HodgeLean.Foundations.QuotientDuality
