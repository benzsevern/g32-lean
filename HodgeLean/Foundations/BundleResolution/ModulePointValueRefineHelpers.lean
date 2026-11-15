import HodgeLean.Foundations.BundleResolution.ModulePointValueAlgebraHelpers
import HodgeLean.Foundations.BundleResolution.ModulePullbackTransportHelpers
/-! # Point specialization through nested factorizations

Actual pullback comparisons transport the same specialized section.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution

theorem i1_module_pointValue_factorization {V U X : Scheme.{0}}
    (a : Spec ↧ℂ ⟶ V) (b : V ⟶ U) (u : U ⟶ X)
    (v : V ⟶ X) (w : Spec ↧ℂ ⟶ U) (x : Spec ↧ℂ ⟶ X)
    (hv : b ≫ u = v) (hw : a ≫ b = w) (hxv : a ≫ v = x) (hxu : w ≫ u = x)
    (M : X.Modules)
    (s : SheafOfModules.unit U.ringCatSheaf ⟶ (Scheme.Modules.pullback u).obj M) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullbackComp a v).hom.app M ≫
          (Scheme.Modules.pullbackCongr hxv).hom.app M)
      (i1_module_pointValue ((Scheme.Modules.pullback v).obj M)
        (i1_module_sectionPullback b ((Scheme.Modules.pullback u).obj M) s ≫
          (Scheme.Modules.pullbackComp b u).hom.app M ≫
            (Scheme.Modules.pullbackCongr hv).hom.app M) a) =
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullbackComp w u).hom.app M ≫
          (Scheme.Modules.pullbackCongr hxu).hom.app M)
      (i1_module_pointValue ((Scheme.Modules.pullback u).obj M) s w) := by
  let F := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let N := (Scheme.Modules.pullback u).obj M
  let d := (Scheme.Modules.pullbackComp b u).hom.app M ≫
    (Scheme.Modules.pullbackCongr hv).hom.app M
  let tV := (Scheme.Modules.pullbackComp a v).hom.app M ≫
    (Scheme.Modules.pullbackCongr hxv).hom.app M
  let tU := (Scheme.Modules.pullbackComp w u).hom.app M ≫
    (Scheme.Modules.pullbackCongr hxu).hom.app M
  let p := (Scheme.Modules.pullbackComp a b).hom.app N
  let q := (Scheme.Modules.pullbackCongr hw).hom.app N
  let z := i1_module_pointValue ((Scheme.Modules.pullback b).obj N)
    (i1_module_sectionPullback b N s) a
  have hc : (Scheme.Modules.pullback a).map d ≫ tV = p ≫ q ≫ tU :=
    i1_module_pullback_factorization_coherence a b u v w x hv hw hxv hxu M
  have hp : F.map p z = i1_module_pointValue N s (a ≫ b) :=
    i1_module_pointValue_pullback_comp a b N s
  have hq : F.map q (i1_module_pointValue N s (a ≫ b)) = i1_module_pointValue N s w :=
    i1_module_pointValue_congr N s hw
  change F.map tV (i1_module_pointValue ((Scheme.Modules.pullback v).obj M)
    (i1_module_sectionPullback b N s ≫ d) a) = F.map tU (i1_module_pointValue N s w)
  rw [i1_module_pointValue_naturality]
  calc
    _ = F.map ((Scheme.Modules.pullback a).map d ≫ tV) z := rfl
    _ = F.map (p ≫ q ≫ tU) z := congrArg (fun t => F.map t z) hc
    _ = F.map tU (F.map q (F.map p z)) := rfl
    _ = F.map tU (F.map q (i1_module_pointValue N s (a ≫ b))) :=
      congrArg (fun y => F.map tU (F.map q y)) hp
    _ = F.map tU (i1_module_pointValue N s w) := congrArg (fun y => F.map tU y) hq
end HodgeLean.Foundations.BundleResolution
