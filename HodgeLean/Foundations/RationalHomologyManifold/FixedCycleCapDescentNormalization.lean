import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapDescent
import HodgeLean.Foundations.RationalHomologyManifold.HomotopyInitialCycles

/-! Normalization of actual descended cap on initial cocycles.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual fixed-cycle cap descends with literal equality on every ambient degree-zero cocycle morphism, in addition to the full cochain homotopy.
Source: Bredon, Sheaf Theory, second edition, VI.12; Weibel, An Introduction to Homological Algebra, section 1.4.
HC no distance; AV milestone no distance.
-/
theorem exists_fixedCycleCap_descent_initial (X : TopCat.{0}) [RegularSpace X] (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0)
    (I : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    [∀ p, Injective (I.X p)] (j : capTargetComplex X N ⟶ I) :
    ∃ d : singularCochainSheafComplex ℚ X ⟶ I,
      Nonempty (Homotopy (ambientFixedCycleCapComplexHom X N z hz ≫ j)
        (ambientCochainSheafRestriction X ≫ d)) ∧
      ∀ (S : TopCat.Sheaf AddCommGrpCat.{0} X)
        (u : S ⟶ (ambientCochainSheafComplex X).X 0),
        u ≫ (ambientCochainSheafComplex X).d 0 1 = 0 →
        u ≫ ambientCapTargetComponent X N z 0 ≫ j.f 0 =
          u ≫ (ambientCochainSheafRestriction X).f 0 ≫ d.f 0 := by
  obtain ⟨d, ⟨h⟩⟩ := exists_fixedCycleCap_descent X N z hz I j
  refine ⟨d, ⟨h⟩, fun S u hu => ?_⟩
  exact homotopy_initial_cocycles h u hu

#print axioms exists_fixedCycleCap_descent_initial
end HodgeLean.Foundations.RationalHomologyManifold
