import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeTransport

/-! # Actual real point-pair maps under original dimension equalities
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual equality-induced pair isomorphism for real coordinate spaces of equal finite dimension.
Source: CategoryTheory.eqToIso; AlgebraicTopology.Singular.puncturedPair.
HC no distance; AV milestone no distance. -/
def properCycle_real_dimension_pair_iso {i j : ℕ} (e : i = j) :
    puncturedPair ℝ i ≅ puncturedPair ℝ j :=
  eqToIso (congrArg (puncturedPair ℝ) e)

/-- The actual equality-induced real point-pair map is the literal dimension-preserving finite index map on ambient coordinates.
Source: properCycle_real_dimension_pair_iso; CategoryTheory.eqToIso.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_dimension_pair_coordinates {i j : ℕ} (e : i = j)
    (z : Fin i → ℝ) :
    TopPair.Hom.fst (properCycle_real_dimension_pair_iso e).hom z =
      (fun k : Fin j => z ⟨k.val, by omega⟩) := by
  subst j
  rfl

/-- The actual real dimension pair map and original degree cast retain the specified standard real local class.
Source: properCycle_real_dimension_pair_iso; AlgebraicTopology.Singular.relativeHomologyDegreeCast.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_dimension_standard_class {i j : ℕ} (e : i = j) :
    relativeHomologyDegreeCast e
      (relativeHomologyMap ℚ i (properCycle_real_dimension_pair_iso e).hom (standardLocalClass ℚ i)) =
      standardLocalClass ℚ j := by
  subst j
  change relativeHomologyMap ℚ i (𝟙 (puncturedPair ℝ i)) (standardLocalClass ℚ i) = _
  simp only [relativeHomologyMap_id, LinearMap.id_apply]

end HodgeLean.Foundations.QuotientDuality
