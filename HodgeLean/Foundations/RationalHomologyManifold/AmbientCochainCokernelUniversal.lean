import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafCokernel

/-! The cokernel universal property of actual ambient-to-local cochain restriction.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual sheafified ambient restriction is the cokernel of the actual sheafified local zero-cochain inclusion.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; exact sheafification and the cokernel of an epimorphism's kernel.
HC no distance; AV milestone no distance.
-/
def ambientCochainSheafRestrictionIsCokernel (X : TopCat.{0}) :
    IsColimit (CokernelCofork.ofπ (ambientCochainSheafRestriction X)
      (ambientLocalZeroSheafInclusion_restriction X)) := by
  let F := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let r := ambientCochainPresheafComplexRestriction X
  letI : Epi r := ambientCochainPresheafComplexRestriction_epi X
  exact isColimitCoforkMapOfIsColimit' F (kernel.condition r)
    (Abelian.epiIsCokernelOfKernel _ (limit.isLimit (parallelPair r 0)))

#print axioms ambientCochainSheafRestrictionIsCokernel
/-- Every degree of the actual sheafified kernel inclusion is a monomorphism.
Source: Bredon, Sheaf Theory, second edition, I.1; left exactness of sheafification.
HC no distance; AV milestone no distance.
-/
theorem ambientLocalZeroSheafInclusion_mono (X : TopCat.{0}) (p : ℕ) :
    Mono ((ambientLocalZeroSheafInclusion X).f p) := by
  change Mono ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map
    ((kernel.ι (ambientCochainPresheafComplexRestriction X)).f p))
  infer_instance

#print axioms ambientLocalZeroSheafInclusion_mono
end HodgeLean.Foundations.RationalHomologyManifold
