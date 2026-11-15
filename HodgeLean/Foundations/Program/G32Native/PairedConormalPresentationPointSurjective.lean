import HodgeLean.Foundations.Program.G32Native.PairedConormalPointQuotientSections
import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitFreeLocallyFree

/-! # Point-section surjectivity for the actual elementary presentation -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual elementary presentation is surjective on every complex-point
fibre using only local freeness of its supplied target. -/
theorem conormal_presentation_point_sections_surjective {X : Scheme.{0}} (k : ℕ)
    {M : X.Modules} [M.IsLocallyFree]
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M) [Epi π]
    (x : Spec (CommRingCat.of ℂ) ⟶ X) :
    Function.Surjective ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback x).map π)) := by
  letI : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)).IsLocallyFree :=
    conormal_unit_free_locallyFree X k
  exact conormal_locallyFree_point_quotient_sections_surjective π x

end HodgeLean.Foundations.Program.G32Native
