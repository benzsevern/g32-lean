import HodgeLean.Foundations.Program.G32Native.ConormalSectionEqualityNaturality
import HodgeLean.Foundations.BundleResolution.ModulePullbackTransportHelpers

/-! # Module sections through two factorizations of a scheme morphism -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

/-- Normalized sections respect the canonical comparison of two factorizations. -/
theorem moduleSection_factorization {W V U X : Scheme.{0}}
    (a : W ⟶ V) (b : V ⟶ U) (u : U ⟶ X)
    (v : V ⟶ X) (w : W ⟶ U) (x : W ⟶ X)
    (hv : b ≫ u = v) (hw : a ≫ b = w) (hxv : a ≫ v = x) (hxu : w ≫ u = x)
    (M : X.Modules)
    (s : SheafOfModules.unit.{0} U.ringCatSheaf ⟶ (Scheme.Modules.pullback u).obj M) :
    i1_module_sectionPullback a ((Scheme.Modules.pullback v).obj M)
        (i1_module_sectionPullback b ((Scheme.Modules.pullback u).obj M) s ≫
          (Scheme.Modules.pullbackComp b u).hom.app M ≫
            (Scheme.Modules.pullbackCongr hv).hom.app M) ≫
      (Scheme.Modules.pullbackComp a v).hom.app M ≫
        (Scheme.Modules.pullbackCongr hxv).hom.app M =
      i1_module_sectionPullback w ((Scheme.Modules.pullback u).obj M) s ≫
        (Scheme.Modules.pullbackComp w u).hom.app M ≫
          (Scheme.Modules.pullbackCongr hxu).hom.app M := by
  rw [conormalSection_pullback_map]
  simp only [Category.assoc]
  rw [i1_module_pullback_factorization_coherence a b u v w x hv hw hxv hxu M]
  rw [← reassoc_of% (i1_module_sectionPullback_comp a b ((Scheme.Modules.pullback u).obj M) s)]
  rw [reassoc_of% (conormalSection_pullback_congr hw ((Scheme.Modules.pullback u).obj M) s)]

end HodgeLean.Foundations.TubularEuler
