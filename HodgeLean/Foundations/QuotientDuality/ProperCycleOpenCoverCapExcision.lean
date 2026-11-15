import HodgeLean.Foundations.QuotientDuality.ProperCycleSmallCoverExcision
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexCapExcision

/-! # Actual cap bijectivity through open-cover excision -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original cap on an actual open-cover quotient transfers to the full singular subcomplex of the union, using subdivision on both sides of the cap square.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative subdivision and cap naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_cover_cap_bijective
    {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Set X) (S : Set X)
    (hAo : IsOpen A) (hUo : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = S)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ (subsetSingularSubcomplex X A).ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0)
    (hc : Function.Bijective (properCycle_subcomplex_cap_homology_map
      (subsetSingularSubcomplex X A) (coverSmallSingularSubcomplex X U) p q hp φ hA hφ).hom) :
    Function.Bijective (properCycle_subcomplex_cap_homology_map
      (subsetSingularSubcomplex X A) (subsetSingularSubcomplex X S) p q hp φ hA hφ).hom := by
  let hUS := properCycle_small_cover_le_subset X U S
    (fun i => (Set.subset_iUnion U i).trans hcover.le)
  letI : QuasiIso (properCycle_subcomplex_quotient_map hUS) :=
    properCycle_small_cover_quotient_quasiIso X U S hUo hcover
  letI : QuasiIso (properCycle_subcomplex_quotient_map
      (sup_le_sup_left hUS (subsetSingularSubcomplex X A))) :=
    properCycle_fixed_open_cover_quotient_quasiIso X A U S hAo hUo hcover
  exact properCycle_subcomplex_cap_bijective_of_inclusion _ _ _ hUS p q hp φ hA hφ
    (ConcreteCategory.bijective_of_isIso _) (ConcreteCategory.bijective_of_isIso _) hc

end HodgeLean.Foundations.QuotientDuality
