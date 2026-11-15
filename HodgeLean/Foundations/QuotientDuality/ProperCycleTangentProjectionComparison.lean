import HodgeLean.Foundations.QuotientDuality.ProperCycleProductTangentHomology

/-! # Literal tangential projection in the original product cap target
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal first projection is the actual map from the product tangential support-complement pair to its intrinsic point-complement pair.
Source: Hatcher, Algebraic Topology, section 2.1, maps of relative pairs.
HC no distance; AV milestone no distance. -/
def properCycle_product_tangent_projection_pair
    (E F : Type) [TopologicalSpace E] [Zero E] [TopologicalSpace F] :
    TopPair.ofSubset (X := TopCat.of (E × F)) {z | z.1 = 0}ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of E) ({0} : Set E)ᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (fun _ h => h)

/-- The frozen swap-and-contraction target comparison has exactly the homology map of the literal first projection.
Source: properCycle_product_tangent_local_homology_iso; properCycle_product_support_homology_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_product_tangent_local_homology_projection
    (E : Type) [TopologicalSpace E] [Zero E]
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) :
    (properCycle_product_tangent_local_homology_iso E F n).hom =
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_product_tangent_projection_pair E F)) n := by
  let e : TopPair.ofSubset (X := TopCat.of (E × F)) {z | z.1 = 0}ᶜ ≅
      TopPair.ofSubset (X := TopCat.of (F × E)) (Prod.snd ⁻¹' ({0} : Set E)ᶜ) :=
    TopPair.isoOfSubset (Homeomorph.prodComm E F) (fun _ => Iff.rfl)
  have hp : e.hom ≫ properCycle_product_support_projection F (TopCat.of E) {0} =
      properCycle_product_tangent_projection_pair E F := by
    ext z : 2 <;> rfl
  dsimp only [properCycle_product_tangent_local_homology_iso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom]
  change HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map e.hom) n ≫
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
      (properCycle_product_support_projection F (TopCat.of E) {0})) n = _
  rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp, hp]

end HodgeLean.Foundations.QuotientDuality
