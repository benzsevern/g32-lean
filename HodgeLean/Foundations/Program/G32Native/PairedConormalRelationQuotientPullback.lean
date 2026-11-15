import HodgeLean.Foundations.Program.G32Native.PairedConormalRelationPullback
import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationPullback

/-! # The supplied relation remains in the kernel of the supplied pulled quotient -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles

/-- Source normalization and pullback retain the actual zero composition. -/
theorem conormal_relation_quotient_pullback {X Y : Scheme.{0}} (f : X ⟶ Y)
    (k : ℕ) {I : Y.Modules} {J : X.Modules} (u : J ⟶ (Scheme.Modules.pullback f).obj I)
    (a : I ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (b : I ⟶ SheafOfModules.free (R := Y.ringCatSheaf) (Fin k))
    (M : Y.Modules)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M)
    (hπ : HodgeLean.Foundations.NormalPresentation.relation a b ≫ π = 0) :
    HodgeLean.Foundations.NormalPresentation.relation
      (u ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackUnit f).hom)
      (u ≫ (Scheme.Modules.pullback f).map b ≫
        (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin k)).hom) ≫
      conormalPresentationPullback f k M π = 0 := by
  letI := conormal_scheme_pullback_additive f
  rw [conormal_relation_pullback_precomp, Category.assoc, Category.assoc,
    conormal_presentation_pullback_comp, hπ, CategoryTheory.Functor.map_zero, comp_zero]

#print axioms conormal_relation_quotient_pullback
end HodgeLean.Foundations.Program.G32Native
