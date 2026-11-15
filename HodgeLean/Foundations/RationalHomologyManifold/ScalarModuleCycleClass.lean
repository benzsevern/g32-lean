import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! Actual scalar cycle representatives of rational module homology classes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The scalar morphism of a specified actual rational cycle has zero differential.
Source: Weibel, An Introduction to Homological Algebra, section 1.2; cycles as the kernel of the differential.
HC no distance; AV milestone no distance.
-/
theorem scalarModuleCycle_zero (S : ShortComplex (ModuleCat.{0} ℚ))
    (z : LinearMap.ker S.g.hom) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ z.val) ≫ S.g = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change S.g.hom (r • z.val) = 0
  rw [map_smul, z.property, smul_zero]

#print axioms scalarModuleCycle_zero
/-- The actual class of a rational module cycle is the value at one of its scalar cycle morphism followed by the original homology projection.
Source: Weibel, An Introduction to Homological Algebra, section 1.2; the class of an explicit cycle.
HC no distance; AV milestone no distance.
-/
theorem scalarModuleCycle_class (S : ShortComplex (ModuleCat.{0} ℚ))
    (z : LinearMap.ker S.g.hom) :
    ((S.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ z.val))
      (scalarModuleCycle_zero S z)) ≫ S.homologyπ) (1 : ℚ) = S.moduleCatHomologyClass z := by
  let k := ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ z.val)
  have hl : S.liftCycles k (scalarModuleCycle_zero S z) (1 : ℚ) = S.moduleCatCyclesIso.inv z := by
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    have h₁ := ConcreteCategory.congr_hom (S.liftCycles_i k (scalarModuleCycle_zero S z)) (1 : ℚ)
    have h₂ := ConcreteCategory.congr_hom (S.moduleCatCyclesIso_inv_iCycles) z
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    have hk₁ : k (1 : ℚ) = z.val := by
      change (1 : ℚ) • z.val = z.val
      exact one_smul ℚ z.val
    exact h₁.trans (hk₁.trans h₂.symm)
  change S.homologyπ (S.liftCycles k (scalarModuleCycle_zero S z) (1 : ℚ)) = _
  rw [hl]
  exact ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π z

#print axioms scalarModuleCycle_class
end HodgeLean.Foundations.RationalHomologyManifold
