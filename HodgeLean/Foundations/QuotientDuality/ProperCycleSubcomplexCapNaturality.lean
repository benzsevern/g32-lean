import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexCap

/-! # Original quotient cap under enlargement of the second subcomplex -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual quotient cap commutes with the original quotient maps for an inclusion of second subcomplexes.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_cap_inclusion
    {K : SSet.{0}} (A T U : K.Subcomplex) (hTU : T ≤ U) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0) :
    properCycle_subcomplex_cap_hom A T p q φ hA ≫
        (properCycle_subcomplex_quotient_map hTU).f q =
      (properCycle_subcomplex_quotient_map (sup_le_sup_left hTU A)).f (p + q) ≫
        properCycle_subcomplex_cap_hom A U p q φ hA := by
  have hT := congrArg (fun m => m.f q) (properCycle_subcomplex_quotient_projection hTU)
  have hS := congrArg (fun m => m.f (p + q))
    (properCycle_subcomplex_quotient_projection (sup_le_sup_left hTU A))
  rw [HomologicalComplex.comp_f] at hT hS
  apply Cofork.IsColimit.hom_ext
    (properCycle_subcomplex_quotient_component_cokernel (A ⊔ T) (p + q))
  change (cokernel.π (SSet.chainComplexMap (A ⊔ T).ι (ModuleCat.of ℚ ℚ))).f (p + q) ≫
      (properCycle_subcomplex_cap_hom A T p q φ hA ≫ _) =
    (cokernel.π (SSet.chainComplexMap (A ⊔ T).ι (ModuleCat.of ℚ ℚ))).f (p + q) ≫
      ((properCycle_subcomplex_quotient_map (sup_le_sup_left hTU A)).f (p + q) ≫ _)
  rw [← Category.assoc, properCycle_subcomplex_cap_projection,
    Category.assoc, hT, ← Category.assoc, hS, properCycle_subcomplex_cap_projection]

/-- The actual even quotient cap chain maps form a commuting square under enlargement of the second subcomplex.
Source: Hatcher, Algebraic Topology, section 3.3, chain naturality of the cap product.
HC no distance; AV milestone no distance. -/
lemma properCycle_even_subcomplex_cap_inclusion
    {K : SSet.{0}} (A T U : K.Subcomplex) (hTU : T ≤ U) (p : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    properCycle_even_subcomplex_cap_chain_map A T p hp φ hA hφ ≫
        properCycle_subcomplex_quotient_map hTU =
      HomologicalComplex.restrictionMap
          (properCycle_subcomplex_quotient_map (sup_le_sup_left hTU A))
          (properCycle_cap_tail_embedding p) ≫
        properCycle_even_subcomplex_cap_chain_map A U p hp φ hA hφ := by
  apply HomologicalComplex.hom_ext
  intro q
  exact properCycle_subcomplex_cap_inclusion A T U hTU p q φ hA

end HodgeLean.Foundations.QuotientDuality
