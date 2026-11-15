import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_forget_enlarge (X : TopCat.{0}) {S T : Set X}
    (h : S ⊆ T) (n : ℕ) (a : CohomologyWithSupport ℚ X S n) :
    forgetSupport ℚ X T n (enlargeSupport ℚ X h n a) = forgetSupport ℚ X S n a := by
  have hc := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
    (supportInclusionPairMap X h)
  change relativeChainProjection ℚ (TopPair.ofSubset Tᶜ) ≫
      (relativeChainFunctor ℚ).map (supportInclusionPairMap X h) =
      ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map (𝟙 X) ≫
        relativeChainProjection ℚ (TopPair.ofSubset Sᶜ) at hc
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hc
  have hd := congrArg HomologicalComplex.linearDualMap hc
  rw [HomologicalComplex.linearDualMap_comp] at hd
  have hh := congrArg (fun f => HomologicalComplex.homologyMap f n) hd
  rw [HomologicalComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh a

theorem retained_absolute_sum_of_common_support (X : TopCat.{0})
    {I : Type} [Fintype I] {S₀ T : Set X} (S : I → Set X)
    (h₀ : S₀ ⊆ T) (hi : ∀ i, S i ⊆ T) (n : ℕ)
    (b : CohomologyWithSupport ℚ X S₀ n)
    (a : ∀ i, CohomologyWithSupport ℚ X (S i) n) (q : I → ℚ)
    (hsum : enlargeSupport ℚ X h₀ n b =
      ∑ i, q i • enlargeSupport ℚ X (hi i) n (a i)) :
    forgetSupport ℚ X S₀ n b = ∑ i, q i • forgetSupport ℚ X (S i) n (a i) := by
  have hh := congrArg (forgetSupport ℚ X T n) hsum
  rw [retained_forget_enlarge, map_sum] at hh
  simpa only [map_smul, retained_forget_enlarge] using hh

end HodgeLean.Foundations.QuotientDuality
