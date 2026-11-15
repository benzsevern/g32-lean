import HodgeLean.Foundations.QuotientDuality.ProperCycleProperBoundary
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Actual finite base neighborhoods for proper generically finite maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- A proper map with the specified generic image and positive generic residue degree is finite on an actual dense target neighborhood.
Source: Stacks Project, Tag 02UP; Hartshorne, Algebraic Geometry, exercise II.3.20.
HC no distance; AV milestone no distance. -/
lemma properCycle_generically_finite_base_open
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (hgeneric : f.left (genericPoint X.left) = genericPoint Y.left)
    (hdegree : 0 < a1p_degree f.left (genericPoint X.left)) :
    ∃ U : Y.left.Opens, genericPoint Y.left ∈ U ∧ Dense (U : Set Y.left) ∧ IsFinite (f.left ∣_ U) := by
  have hf : (f.left ⁻¹' ({genericPoint Y.left} : Set Y.left)).Finite := by
    apply (Set.finite_singleton (genericPoint X.left)).subset
    intro x hx
    change f.left x = genericPoint Y.left at hx
    change x = genericPoint X.left
    by_contra hn
    have hg := properCycle_generic_not_mem_image_boundary f hgeneric hdegree
      ({genericPoint X.left} : Set X.left)ᶜ (by simp)
    exact hg ⟨x, hn, hx⟩
  obtain ⟨U, hU, hfinite⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    f.left (genericPoint Y.left) hf
  exact ⟨U, hU, U.isOpen.dense ⟨genericPoint Y.left, hU⟩, hfinite⟩

/-- A proper map of integral schemes with the specified generic image is surjective on actual scheme points.
Source: Hartshorne, Algebraic Geometry, II.4, proper maps and specialization of the generic point.
HC no distance; AV milestone no distance. -/
lemma properCycle_proper_surjective_of_generic_image
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) [IsProper f.left]
    (hgeneric : f.left (genericPoint X.left) = genericPoint Y.left) : Surjective f.left := by
  constructor
  intro y
  exact (genericPoint_specializes y).mem_closed f.left.isClosedMap.isClosed_range
    ⟨genericPoint X.left, hgeneric⟩

end HodgeLean.Foundations.QuotientDuality
