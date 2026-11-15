import HodgeLean.Foundations.QuotientDuality.RetainedCycleOrientationSheaf

noncomputable section
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- The frozen local homology vanishing implies concentration of the actual relative-chain sheaf. -/
theorem retained_chain_sheaf_concentrated (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x)) :
    ∀ i : ℤ, i ≠ -(n : ℤ) →
      IsZero ((singularChainSheafCochainComplex ℚ X).homology i) := by
  apply singularChainSheafCochainHomology_concentrated ℚ X n
  intro j hj x
  letI := hv j hj x
  exact ModuleCat.isZero_of_subsingleton _

local instance (X : TopCat.{0}) : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) :=
  HasDerivedCategory.standard _

/-- The actual chain-sheaf derived orientation determined by the global class and the local hypotheses. -/
def retainedDerivedOrientationIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : Homology ℚ X n) (ho : ∀ x, Function.Bijective (orientationLine X n c x))
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x)) :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X) ≅
      ((DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat X) 0).obj
        𝓒(X; ℚ))⟦(n : ℤ)⟧ := by
  apply singularChainSheafDerivedOrientationIso ℚ X n ?_
    (retainedOrientationHomologySheafIso X n c ho).symm
  intro j hj x
  letI := hv j hj x
  exact ModuleCat.isZero_of_subsingleton _

end HodgeLean.Foundations.QuotientDuality
