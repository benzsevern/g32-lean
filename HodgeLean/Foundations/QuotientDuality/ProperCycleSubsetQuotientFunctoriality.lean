import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexQuotientFunctoriality
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexRelativeNaturality

/-! # Actual subset relative quotients under maps of ambient spaces
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A continuous map preserving actual subsets preserves their literal singular image subcomplexes.
Source: Hatcher, Algebraic Topology, section 2.1, functorial singular simplices; mem_subsetSingularSubcomplex_iff.
HC no distance; AV milestone no distance. -/
theorem properCycle_subset_subcomplex_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set X) (T : Set Y) (h : Set.MapsTo f S T) :
    subsetSingularSubcomplex X S ≤ (subsetSingularSubcomplex Y T).preimage (TopCat.toSSet.map f) := by
  intro n σ hσ
  change (TopCat.toSSet.map f).app n σ ∈ (subsetSingularSubcomplex Y T).obj n
  rw [mem_subsetSingularSubcomplex_iff] at hσ ⊢
  intro t
  exact h (hσ t)

/-- The induced ambient quotient map agrees with the original relative chain map through the specified subset comparisons.
Source: properCycle_subcomplex_quotient_morphism_projection; properCycle_subset_subcomplex_relative_projection; TopPair.Homotopy.relativeChainProjection_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_subset_quotient_morphism_relative_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set X) (T : Set Y) (h : Set.MapsTo f S T) :
    properCycle_subcomplex_quotient_morphism (TopCat.toSSet.map f)
        (subsetSingularSubcomplex X S) (subsetSingularSubcomplex Y T)
        (properCycle_subset_subcomplex_map f S T h) ≫
        (properCycle_subset_subcomplex_relative_iso Y T).hom =
      (properCycle_subset_subcomplex_relative_iso X S).hom ≫
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f h) := by
  apply (cancel_epi (cokernel.π
    (SSet.chainComplexMap (subsetSingularSubcomplex X S).ι (ModuleCat.of ℚ ℚ)))).mp
  rw [← Category.assoc, properCycle_subcomplex_quotient_morphism_projection, Category.assoc,
    properCycle_subset_subcomplex_relative_projection, ← Category.assoc,
    properCycle_subset_subcomplex_relative_projection,
    TopPair.Homotopy.relativeChainProjection_naturality]
  rfl

end HodgeLean.Foundations.QuotientDuality
