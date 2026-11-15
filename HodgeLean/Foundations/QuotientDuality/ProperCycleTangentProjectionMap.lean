import HodgeLean.Foundations.QuotientDuality.ProperCycleProductTangentHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleContractibleFactorProjection

/-! # Literal tangential projection in the original product point comparison
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original tangential local homology isomorphism is induced by the actual first projection of the product support pair.
Source: properCycle_product_tangent_local_homology_iso; properCycle_product_support_homology_iso.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_tangent_local_homology_iso_map
    (E : Type) [TopologicalSpace E] [Zero E]
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) :
    (properCycle_product_tangent_local_homology_iso E F n).hom.hom =
      relativeHomologyMap ℚ n
        (properCycle_factor_projection_pair (TopCat.of E) (TopCat.of F) ({0} : Set E)ᶜ) := by
  let e : TopPair.ofSubset (X := TopCat.of (E × F)) {z | z.1 = 0}ᶜ ≅
      TopPair.ofSubset (X := TopCat.of (F × E)) (Prod.snd ⁻¹' ({0} : Set E)ᶜ) :=
    TopPair.isoOfSubset (Homeomorph.prodComm E F) (fun _ => Iff.rfl)
  have he : e.hom ≫ properCycle_product_support_projection F (TopCat.of E) {0} =
      properCycle_factor_projection_pair (TopCat.of E) (TopCat.of F) ({0} : Set E)ᶜ := by
    ext z : 2 <;> rfl
  change (relativeHomologyMap ℚ n (properCycle_product_support_projection F (TopCat.of E) {0})).comp
    (relativeHomologyMap ℚ n e.hom) = _
  rw [← relativeHomologyMap_comp, he]

end HodgeLean.Foundations.QuotientDuality
