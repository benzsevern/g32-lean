import HodgeLean.Foundations.QuotientDuality.RetainedCycleCohomologyRepresentatives

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

local instance (X : TopCat.{0}) : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) :=
  HasDerivedCategory.standard _

/-- The actual derived cap morphism attached to a singular cohomology class. -/
def retainedCohomologyDerivedCapAction (X : TopCat.{0}) (n : ℕ)
    (a : Cohomology ℚ X n) :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X) ⟶
      (DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X))⟦(n : ℤ)⟧ :=
  let φ := Classical.choose (HodgeLean.Foundations.Singular.cohomologyClass_surjective X n a)
  retainedDerivedCapAction X n φ.1 φ.2

/-- On every represented class the descended action is the original actual derived cap. -/
theorem retained_cohomology_derived_cap_on_class (X : TopCat.{0}) (n : ℕ)
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) n) :
    retainedCohomologyDerivedCapAction X n
      (HodgeLean.Foundations.Singular.cohomologyClass X n φ) =
        retainedDerivedCapAction X n φ.1 φ.2 := by
  unfold retainedCohomologyDerivedCapAction
  apply retained_derived_cap_eq_of_class_eq
  exact Classical.choose_spec (HodgeLean.Foundations.Singular.cohomologyClass_surjective X n
    (HodgeLean.Foundations.Singular.cohomologyClass X n φ))

/-- The actual derived cap action on singular cohomology is additive. -/
theorem retained_cohomology_derived_cap_add (X : TopCat.{0}) (n : ℕ)
    (a b : Cohomology ℚ X n) :
    retainedCohomologyDerivedCapAction X n (a + b) =
      retainedCohomologyDerivedCapAction X n a + retainedCohomologyDerivedCapAction X n b := by
  obtain ⟨φ, rfl⟩ := HodgeLean.Foundations.Singular.cohomologyClass_surjective X n a
  obtain ⟨ψ, rfl⟩ := HodgeLean.Foundations.Singular.cohomologyClass_surjective X n b
  have hm := map_add (HodgeLean.Foundations.Singular.cohomologyClass (R := ℚ) X n) φ ψ
  rw [← hm, retained_cohomology_derived_cap_on_class,
    retained_cohomology_derived_cap_on_class, retained_cohomology_derived_cap_on_class]
  exact retained_derived_cap_add X n φ.1 ψ.1 φ.2 ψ.2 (φ + ψ).2

/-- The actual cohomology-to-derived-cap construction as an additive map. -/
def retainedCohomologyDerivedCapAddHom (X : TopCat.{0}) (n : ℕ) :
    Cohomology ℚ X n →+
      (DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X) ⟶
        (DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X))⟦(n : ℤ)⟧) :=
  AddMonoidHom.mk' (retainedCohomologyDerivedCapAction X n)
    (retained_cohomology_derived_cap_add X n)

/-- The cohomology-level derived cap action transported through the specified orientation. -/
def retainedOrientedCohomologyDerivedCapAction (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : Homology ℚ X n) (ho : ∀ x, Function.Bijective (orientationLine X n c x))
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x))
    (p : ℕ) (a : Cohomology ℚ X p) :
    ((DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat X) 0).obj 𝓒(X; ℚ))⟦(n : ℤ)⟧ ⟶
      (((DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat X) 0).obj 𝓒(X; ℚ))⟦(n : ℤ)⟧)⟦(p : ℤ)⟧ :=
  (retainedDerivedOrientationIso X n c ho hv).inv ≫ retainedCohomologyDerivedCapAction X p a ≫
    (retainedDerivedOrientationIso X n c ho hv).hom⟦(p : ℤ)⟧'

/-- On represented classes the transported cohomology action is the original oriented cap action. -/
theorem retained_oriented_cohomology_derived_cap_on_class
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (c : Homology ℚ X n)
    (ho : ∀ x, Function.Bijective (orientationLine X n c x))
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x))
    (p : ℕ) (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p) :
    retainedOrientedCohomologyDerivedCapAction X n c ho hv p
      (HodgeLean.Foundations.Singular.cohomologyClass X p φ) =
        retainedOrientedDerivedCapAction X n c ho hv p φ.1 φ.2 := by
  unfold retainedOrientedCohomologyDerivedCapAction retainedOrientedDerivedCapAction
  rw [retained_cohomology_derived_cap_on_class]

end HodgeLean.Foundations.QuotientDuality
