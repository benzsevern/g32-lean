import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportSuspension

/-! # Actual right chain comparisons for arbitrary real support suspensions
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal identity point map sends the original union of half-ray complements to the zero-slice complement.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_real_half_ray_support_union.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_union_to_zero_pair (Y : TopCat.{0}) (T : Set Y) :
    TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      ({z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ∪ {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ) ⟶
    TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ :=
  TopPair.ofSubsetHom (𝟙 _)
    (fun _ hz => (properCycle_real_half_ray_support_union Y T) ▸ hz)

/-- The actual right support comparison is the original triad-to-union chain map followed by the literal zero-slice pair map.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_subset_union_subcomplex_triad_iso; triadToUnionRelativeChainMap.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_right_chain_map (Y : TopCat.{0}) (T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_subcomplex_quotient_sequence P Q).X₃ ⟶
      (relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := X) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) :=
  (properCycle_subset_union_subcomplex_triad_iso (TopCat.of (ℝ × Y))
    {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ).hom ≫
    triadToUnionRelativeChainMap ℚ (TopCat.of (ℝ × Y))
      {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ ≫
    (relativeChainFunctor ℚ).map (properCycle_real_support_union_to_zero_pair Y T)

/-- The actual right support chain comparison retains precisely the literal ambient projection to the zero-slice complement pair.
Source: properCycle_subset_union_subcomplex_triad_projection; triadRelativeChainProjection_triadToUnionRelativeChainMap; relativeChainProjection_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_right_chain_projection (Y : TopCat.{0}) (T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    cokernel.π (SSet.chainComplexMap (P ⊔ Q).ι (ModuleCat.of ℚ ℚ)) ≫
        properCycle_real_support_right_chain_map Y T =
      relativeChainProjection ℚ (TopPair.ofSubset (X := X) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) := by
  dsimp only
  rw [properCycle_real_support_right_chain_map, ← Category.assoc,
    properCycle_subset_union_subcomplex_triad_projection, ← Category.assoc,
    triadRelativeChainProjection_triadToUnionRelativeChainMap,
    TopPair.Homotopy.relativeChainProjection_naturality]
  change (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
    (𝟙 (TopCat.of (ℝ × Y)))) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Original open-triad right excision is induced by the specified actual right support chain map.
Source: properCycle_subset_union_quotient_homology_iso; properCycle_real_support_right_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_right_iso_homology (Y : TopCat.{0}) (T : Set Y)
    (hT : IsClosed T) (n : ℕ) :
    (properCycle_real_support_right_iso Y T hT n).hom =
      HomologicalComplex.homologyMap (properCycle_real_support_right_chain_map Y T) n := by
  dsimp only [properCycle_real_support_right_iso, id_eq,
    properCycle_subset_union_quotient_homology_iso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, asIso_hom, HomologicalComplex.homologyFunctor]
  simp only [← HomologicalComplex.homologyMap_comp, Category.assoc]
  unfold properCycle_real_support_right_chain_map
  congr 1

end HodgeLean.Foundations.QuotientDuality
