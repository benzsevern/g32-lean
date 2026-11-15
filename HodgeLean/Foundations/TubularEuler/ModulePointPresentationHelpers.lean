import HodgeLean.Foundations.BundleResolution.ModulePointValueAlgebraHelpers

/-! # Actual module section values under the specified point presentation

The canonical module pullback comparison retains the point equality and section map.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem modulePointValue_naturality_presentation {X : Scheme.{0}}
    (M N : X.Modules) (f : M ⟶ N) (s : SheafOfModules.unit.{0} X.ringCatSheaf ⟶ M)
    (b b' : Spec (CommRingCat.of ℂ) ⟶ X) (h : b = b') :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr h).hom.app N)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map ((Scheme.Modules.pullback b).map f)
        (i1_module_pointValue M s b)) = i1_module_pointValue N (s ≫ f) b' := by
  have ht := congrArg (fun t => (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr h).hom.app N) t)
    (i1_module_pointValue_naturality s f b).symm
  exact ht.trans (i1_module_pointValue_congr N (s ≫ f) h)

#print axioms modulePointValue_naturality_presentation


end HodgeLean.Foundations.TubularEuler
