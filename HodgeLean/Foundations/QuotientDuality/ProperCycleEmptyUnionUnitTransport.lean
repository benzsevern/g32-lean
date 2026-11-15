import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyUnionCapNormalization

/-! # Original empty-triad unit normalization under actual subspace equality
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original union-relative base normalization retains the specified relative projection under equality of the actual second subspace with the empty subspace.
Source: properCycle_empty_union_normalized_cap_unit; equality transport of relative singular homology.
HC no distance; AV milestone no distance. -/
theorem properCycle_empty_union_normalized_cap_unit_of_eq
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : B = ∅)
    (p : ℕ) (hp : Even p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) A) p) (hz : z ≠ 0) :
    letI : IsIso (relativeChainProjection ℚ (TopPair.ofSubset (X := X) B)) := by
      subst B
      exact properCycle_empty_relative_projection_isIso X
    let hBo : IsOpen B := by rw [hB]; exact isOpen_empty
    let G := HomologicalComplex.homologyMap
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) B)) 0
    cohomologyEquivDualHomology ℚ X 0 (unit (R := ℚ) X)
      ((inv G).hom (unionRelativeTriadCapCohomologyLinear ℚ X A B p 0
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hBo)
        (normalizedRelativeCoclass z hz)
        (relativeHomologyMap ℚ p (TopPair.ofSubsetHom (𝟙 X)
          (show A ⊆ A ∪ B from Set.subset_union_left)) z))) = 1 := by
  subst B
  exact properCycle_empty_union_normalized_cap_unit X A hA p hp z hz

end HodgeLean.Foundations.QuotientDuality
