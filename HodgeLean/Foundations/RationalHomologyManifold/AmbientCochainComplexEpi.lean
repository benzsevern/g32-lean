import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainEpi
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Epimorphy of the actual ambient-to-local cochain complex restriction.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual ambient-to-local restriction is an epimorphism in the category of cochain presheaf complexes.
Source: Hatcher, Algebraic Topology, section 3.1; extension of cochains in every degree.
HC no distance; AV milestone no distance.
-/
theorem ambientCochainPresheafComplexRestriction_epi (X : TopCat.{0}) :
    Epi (ambientCochainPresheafComplexRestriction X) := by
  apply HomologicalComplex.epi_of_epi_f
  intro p
  exact ambientCochainPresheafRestriction_epi X p

#print axioms ambientCochainPresheafComplexRestriction_epi
end HodgeLean.Foundations.RationalHomologyManifold
