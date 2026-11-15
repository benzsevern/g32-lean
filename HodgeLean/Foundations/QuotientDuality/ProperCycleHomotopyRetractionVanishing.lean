import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveClosedNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleClosedSupportHomologyDimension
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-! # Ordinary homology vanishing in actual deformation neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual homotopy retraction onto a space with zero ordinary homology forces the original neighborhood homology to be zero in that degree.
Source: TopCat.Homotopy.singularChainComplexFunctorObjMap; homologyMap_comp.
HC no distance; AV milestone no distance. -/
theorem properCycle_homotopy_retraction_homology_vanishes
    {A U : TopCat.{0}} (j : A ⟶ U) (q : U ⟶ A)
    (H : TopCat.Homotopy (𝟙 U) (q ≫ j)) (n : ℕ)
    (hA : Subsingleton (Homology ℚ A n)) : Subsingleton (Homology ℚ U n) := by
  letI := hA
  have he : homologyMap ℚ n (𝟙 U) = homologyMap ℚ n (q ≫ j) :=
    congrArg ModuleCat.Hom.hom
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq n)
  have hz (z : Homology ℚ U n) : z = 0 := by
    have hq : homologyMap ℚ n q z = 0 := Subsingleton.elim _ _
    have hh := LinearMap.congr_fun he z
    simpa only [homologyMap_id, LinearMap.id_apply, homologyMap_comp,
      LinearMap.comp_apply, hq, map_zero] using hh
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end HodgeLean.Foundations.QuotientDuality
