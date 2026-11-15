import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationPointSurjective
import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeTargetRank

/-! # The supplied quotient arrow in canonical actual point coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual supplied quotient on point sections in the canonical unit-plus-free coordinates. -/
def conormalPresentationPointMap {X : Scheme.{0}} (k : ℕ) {M : X.Modules}
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M)
    (x : Spec (CommRingCat.of ℂ) ⟶ X) :
    (ℂ × (Fin k → ℂ)) →ₗ[ℂ]
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback x).obj M) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    ((Scheme.Modules.pullback x).map π)).hom.comp
      (conormalUnitFreeFibreCoordinates x k).symm.toLinearMap

/-- The supplied quotient in canonical point coordinates is surjective from
local freeness of the actual target. -/
theorem conormal_presentation_point_map_surjective {X : Scheme.{0}} (k : ℕ)
    {M : X.Modules} [M.IsLocallyFree]
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M) [Epi π]
    (x : Spec (CommRingCat.of ℂ) ⟶ X) :
    Function.Surjective (conormalPresentationPointMap k π x) := by
  exact (conormal_presentation_point_sections_surjective k π x).comp
    (conormalUnitFreeFibreCoordinates x k).symm.surjective

end HodgeLean.Foundations.Program.G32Native
