import HodgeConjecture.Mathlib.Topology.Category.TopPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexTriadModels
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! # Relative quotient comparisons under actual inclusions of supports
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual inclusions of subsets give inclusions of their literal singular image subcomplexes. -/
theorem properCycle_subset_subcomplex_mono (X : TopCat.{0}) {S T : Set X} (h : S ⊆ T) :
    subsetSingularSubcomplex X S ≤ subsetSingularSubcomplex X T := by
  intro n s hs
  rw [mem_subsetSingularSubcomplex_iff] at hs ⊢
  intro t
  exact h (hs t)

/-- The original subcomplex quotient comparison commutes with the actual inclusion map of relative pairs. -/
theorem properCycle_subset_subcomplex_relative_naturality (X : TopCat.{0})
    {S T : Set X} (h : S ⊆ T) :
    properCycle_subcomplex_quotient_map (properCycle_subset_subcomplex_mono X h) ≫
        (properCycle_subset_subcomplex_relative_iso X T).hom =
      (properCycle_subset_subcomplex_relative_iso X S).hom ≫
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom (𝟙 X) h) := by
  apply (cancel_epi (cokernel.π
    (SSet.chainComplexMap (subsetSingularSubcomplex X S).ι (ModuleCat.of ℚ ℚ)))).mp
  rw [← Category.assoc, properCycle_subcomplex_quotient_projection,
    properCycle_subset_subcomplex_relative_projection, ← Category.assoc,
    properCycle_subset_subcomplex_relative_projection,
    TopPair.Homotopy.relativeChainProjection_naturality]
  change relativeChainProjection ℚ (TopPair.ofSubset (X := X) T) =
    (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map (𝟙 X)) ≫ _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end HodgeLean.Foundations.QuotientDuality
