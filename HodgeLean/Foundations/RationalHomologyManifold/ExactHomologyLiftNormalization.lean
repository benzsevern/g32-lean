import HodgeLean.Foundations.RationalHomologyManifold.ExactHomologyCycleNormalization

/-! Actual cycle representatives under exact functor comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Exact functor comparison of cycles carries the actual kernel lift to the lift of the mapped cycle morphism.
Source: Weibel, An Introduction to Homological Algebra, section 1.3; naturality of the kernel construction.
HC no distance; AV milestone no distance.
-/
theorem exactFunctor_cycle_lift {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {A : C}
    (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
    (S.map F).liftCycles (F.map k) (by change F.map k ≫ F.map S.g = 0; rw [← F.map_comp, hk, F.map_zero]) ≫
      (S.mapCyclesIso F).hom = F.map (S.liftCycles k hk) := by
  apply (cancel_mono (F.map S.iCycles)).mp
  simp only [Category.assoc, ShortComplex.mapCyclesIso_hom_iCycles,
    ShortComplex.liftCycles_i, ← F.map_comp]

#print axioms exactFunctor_cycle_lift
/-- The canonical homology comparison under an exact functor retains the actual class of a specified cycle morphism.
Source: Weibel, An Introduction to Homological Algebra, section 1.3; homology on cycle representatives.
HC no distance; AV milestone no distance.
-/
theorem exactFunctor_cycle_class {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {A : C}
    (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
    ((S.map F).liftCycles (F.map k) (by change F.map k ≫ F.map S.g = 0; rw [← F.map_comp, hk, F.map_zero]) ≫
      (S.map F).homologyπ) ≫ (S.mapHomologyIso F).hom =
        F.map (S.liftCycles k hk ≫ S.homologyπ) := by
  rw [Category.assoc, exactFunctor_homology_projection, ← Category.assoc,
    exactFunctor_cycle_lift, ← F.map_comp]

#print axioms exactFunctor_cycle_class
end HodgeLean.Foundations.RationalHomologyManifold
