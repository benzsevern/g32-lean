import HodgeLean.Foundations.RationalHomologyManifold.ScalarModuleCycleClass
import HodgeLean.Foundations.RationalHomologyManifold.ExactHomologyLiftNormalization

/-! Actual rational cycle classes under forgetting the coefficient action.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Forgetting rational scalar structure retains the actual class of a specified cycle as the value at one of its scalar cycle morphism.
Source: Weibel, An Introduction to Homological Algebra, section 1.3; exact forgetful comparison on actual cycles.
HC no distance; AV milestone no distance.
-/
theorem scalarCycle_forget_class (S : ShortComplex (ModuleCat.{0} ℚ))
    (z : LinearMap.ker S.g.hom) :
    let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
    let k := ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ z.val)
    ((S.map F).liftCycles (F.map k)
      (by change F.map k ≫ F.map S.g = 0; rw [← F.map_comp, scalarModuleCycle_zero, F.map_zero]) ≫
        (S.map F).homologyπ) (1 : ℚ) =
          (S.mapHomologyIso F).inv (S.moduleCatHomologyClass z) := by
  dsimp only
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let k := ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ z.val)
  have h := ConcreteCategory.congr_hom
    (exactFunctor_cycle_class S F k (scalarModuleCycle_zero S z)) (1 : ℚ)
  simp only [ConcreteCategory.comp_apply] at h
  change (S.mapHomologyIso F).hom _ =
    (S.liftCycles k (scalarModuleCycle_zero S z) ≫ S.homologyπ) (1 : ℚ) at h
  rw [scalarModuleCycle_class] at h
  apply (ConcreteCategory.bijective_of_isIso (S.mapHomologyIso F).hom).1
  exact h.trans (ConcreteCategory.congr_hom (S.mapHomologyIso F).inv_hom_id
    (S.moduleCatHomologyClass z)).symm

#print axioms scalarCycle_forget_class
end HodgeLean.Foundations.RationalHomologyManifold
