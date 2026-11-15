import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVCapConnecting

/-! # Original quotient caps through relative small-chain comparisons -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original quotient cap on homology commutes with the literal maps enlarging its second subcomplex in every output degree.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_cap_homology_inclusion
    {K : SSet.{0}} (A T U : K.Subcomplex) (hTU : T ≤ U) (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    properCycle_subcomplex_cap_homology_map A T p q hp φ hA hφ ≫
        HomologicalComplex.homologyMap (properCycle_subcomplex_quotient_map hTU) q =
      HomologicalComplex.homologyMap
          (properCycle_subcomplex_quotient_map (sup_le_sup_left hTU A)) (p + q) ≫
        properCycle_subcomplex_cap_homology_map A U p q hp φ hA hφ := by
  unfold properCycle_subcomplex_cap_homology_map
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    properCycle_even_subcomplex_cap_inclusion, HomologicalComplex.homologyMap_comp,
    ← Category.assoc, ← properCycle_cap_tail_homology_map_naturality, Category.assoc]

/-- Bijectivity of the original quotient cap transfers through actual bijective relative homology comparison maps.
Source: Hatcher, Algebraic Topology, section 3.3, cap naturality and small-chain excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_cap_bijective_of_inclusion
    {K : SSet.{0}} (A T U : K.Subcomplex) (hTU : T ≤ U) (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0)
    (hS : Function.Bijective (HomologicalComplex.homologyMap
      (properCycle_subcomplex_quotient_map (sup_le_sup_left hTU A)) (p + q)).hom)
    (hT : Function.Bijective (HomologicalComplex.homologyMap
      (properCycle_subcomplex_quotient_map hTU) q).hom)
    (hc : Function.Bijective (properCycle_subcomplex_cap_homology_map A T p q hp φ hA hφ).hom) :
    Function.Bijective (properCycle_subcomplex_cap_homology_map A U p q hp φ hA hφ).hom := by
  apply (Function.Bijective.of_comp_iff _ hS).mp
  change Function.Bijective ((HomologicalComplex.homologyMap
    (properCycle_subcomplex_quotient_map (sup_le_sup_left hTU A)) (p + q) ≫
      properCycle_subcomplex_cap_homology_map A U p q hp φ hA hφ).hom)
  rw [← properCycle_subcomplex_cap_homology_inclusion]
  exact hT.comp hc

end HodgeLean.Foundations.QuotientDuality
