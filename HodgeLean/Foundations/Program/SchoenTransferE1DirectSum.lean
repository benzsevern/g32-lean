import Mathlib.Algebra.DirectSum.Module

/-! The single-component dependent direct sum. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped DirectSum

namespace HodgeLean.Foundations.Program

/-- A dependent direct sum with one index identifies with its actual component.
Source: Mathlib `DirectSum.component` and `DirectSum.lof`, the coproduct universal property. -/
def s4_e1_directSumUniqueEquiv
    {ι : Type*} [Unique ι] [DecidableEq ι] (R : Type*) [CommRing R]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    (⨁ i, M i) ≃ₗ[R] M default :=
  LinearEquiv.ofLinearMap (DirectSum.component R ι M default)
    (DirectSum.lof R ι M default)
    (by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, DirectSum.component.lof_self, LinearMap.id_apply])
    (by
      apply DirectSum.linearMap_ext R
      intro i
      have hi : i = default := Subsingleton.elim _ _
      subst i
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, DirectSum.component.lof_self, LinearMap.id_apply])

/-- On a component inclusion, the single-component equivalence returns that component.
Source: Mathlib `DirectSum.component.lof_self`. -/
theorem s4_e1_directSumUniqueEquiv_lof
    {ι : Type*} [Unique ι] [DecidableEq ι] (R : Type*) [CommRing R]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (x : M default) :
    s4_e1_directSumUniqueEquiv R M (DirectSum.lof R ι M default x) = x :=
  DirectSum.component.lof_self R default x

/-- The inverse of the single-component equivalence is the actual component inclusion.
Source: Mathlib `DirectSum.lof`, the coproduct inclusion. -/
theorem s4_e1_directSumUniqueEquiv_symm_apply
    {ι : Type*} [Unique ι] [DecidableEq ι] (R : Type*) [CommRing R]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (x : M default) :
    (s4_e1_directSumUniqueEquiv R M).symm x = DirectSum.lof R ι M default x := rfl

/-- A dependent direct sum over a subsingleton index identifies with a specified component.
Source: Mathlib `DirectSum.component` and `DirectSum.lof`. -/
def s4_e1_directSumSubsingletonEquiv
    {ι : Type*} [Subsingleton ι] [DecidableEq ι] (R : Type*) [CommRing R]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (i : ι) :
    (⨁ j, M j) ≃ₗ[R] M i :=
  LinearEquiv.ofLinearMap (DirectSum.component R ι M i) (DirectSum.lof R ι M i)
    (by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, DirectSum.component.lof_self, LinearMap.id_apply])
    (by
      apply DirectSum.linearMap_ext R
      intro j
      have hj : j = i := Subsingleton.elim _ _
      subst j
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, DirectSum.component.lof_self, LinearMap.id_apply])

#print axioms s4_e1_directSumUniqueEquiv
#print axioms s4_e1_directSumUniqueEquiv_lof
#print axioms s4_e1_directSumUniqueEquiv_symm_apply
#print axioms s4_e1_directSumSubsingletonEquiv
end HodgeLean.Foundations.Program
