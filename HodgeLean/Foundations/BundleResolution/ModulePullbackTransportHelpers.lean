import HodgeLean.Foundations.BundleResolution.ModuleUnitPullbackHelpers

/-! # Coherent transport through actual module pullbacks

The canonical pullback composition comparisons satisfy associativity.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution

theorem i1_module_pullbackComp_assoc {W X Y Z : Scheme.{0}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app M) ≫
      (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app M =
    (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
      (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app M := by
  have h := congr($(SheafOfModules.pullback_assoc.{0}
    c.toRingCatSheafHom b.toRingCatSheafHom a.toRingCatSheafHom).hom.app M)
  exact h.symm
theorem i1_module_pullback_factorization_coherence {W V U X : Scheme.{0}}
    (a : W ⟶ V) (b : V ⟶ U) (u : U ⟶ X)
    (v : V ⟶ X) (w : W ⟶ U) (x : W ⟶ X)
    (hv : b ≫ u = v) (hw : a ≫ b = w) (hxv : a ≫ v = x) (hxu : w ≫ u = x)
    (M : X.Modules) :
    (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullbackComp b u).hom.app M ≫
          (Scheme.Modules.pullbackCongr hv).hom.app M) ≫
      (Scheme.Modules.pullbackComp a v).hom.app M ≫
        (Scheme.Modules.pullbackCongr hxv).hom.app M =
    (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback u).obj M) ≫
      (Scheme.Modules.pullbackCongr hw).hom.app ((Scheme.Modules.pullback u).obj M) ≫
        (Scheme.Modules.pullbackComp w u).hom.app M ≫
          (Scheme.Modules.pullbackCongr hxu).hom.app M := by
  subst v
  subst w
  subst x
  simpa only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, Functor.map_comp, Functor.map_id, Category.id_comp, Category.assoc] using
    i1_module_pullbackComp_assoc a b u M
end HodgeLean.Foundations.BundleResolution
