import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitFreePullback

/-! # Canonical relation transport with an arbitrary supplied source map -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles

/-- Pullback of the actual relation commutes with any supplied map into
its pulled ideal source, retaining both literal components. -/
theorem conormal_relation_pullback_precomp {X Y : Scheme.{0}}
    (f : X ⟶ Y) (k : ℕ) {I : Y.Modules} {J : X.Modules}
    (u : J ⟶ (Scheme.Modules.pullback f).obj I)
    (a : I ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (b : I ⟶ SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) :
    HodgeLean.Foundations.NormalPresentation.relation
      (u ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackUnit f).hom)
      (u ≫ (Scheme.Modules.pullback f).map b ≫
        (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin k)).hom) =
    u ≫ (Scheme.Modules.pullback f).map
      (HodgeLean.Foundations.NormalPresentation.relation a b) ≫
        (conormalUnitFreePullbackIso f k).hom := by
  rw [conormal_unit_free_pullback_relation f k a b]
  apply biprod.hom_ext <;>
    simp only [HodgeLean.Foundations.NormalPresentation.relation,
      Category.assoc, biprod.lift_fst, biprod.lift_snd]

#print axioms conormal_relation_pullback_precomp
end HodgeLean.Foundations.Program.G32Native
