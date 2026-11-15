import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTripleExact

/-! # Actual support shrinking after vanishing of the ordinary supported restriction -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Vanishing of the actual supported pullback to the smaller support's complement gives an exact lift on that smaller support.
Source: Hatcher, Algebraic Topology, section 3.1, exactness for nested supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_supported_descent_of_restriction_zero
    (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ)
    (a : CohomologyWithSupport ℚ X T n)
    (ha : cohomologyWithSupportMap ℚ n (TopPair.ofSubset Sᶜ).map T a = 0) :
    ∃ b : CohomologyWithSupport ℚ X S n, enlargeSupport ℚ X hST n b = a := by
  let hAB : Tᶜ ⊆ Sᶜ := Set.compl_subset_compl.mpr hST
  let P := properCycle_nested_pair X Tᶜ Sᶜ hAB
  let Q := TopPair.ofSubset ((TopPair.ofSubset Sᶜ).map ⁻¹' T)ᶜ
  let j : P ⟶ Q := TopPair.ofHom (𝟙 _)
    (TopCat.ofHom ⟨fun a => ⟨⟨a.1, hAB a.2⟩, a.2⟩,
      ((continuous_subtype_val.subtype_mk _).subtype_mk _)⟩) (by ext; rfl)
  have hj : j ≫ preimageSupportPairMap (TopPair.ofSubset Sᶜ).map T =
      properCycle_relative_triple_first X Tᶜ Sᶜ hAB := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext x <;> rfl
  apply properCycle_supported_descent_of_complement_zero X S T hST n a
  rw [← hj, relativeCohomologyMap_comp]
  change relativeCohomologyMap ℚ n j
    (cohomologyWithSupportMap ℚ n (TopPair.ofSubset Sᶜ).map T a) = 0
  rw [ha, map_zero]

end HodgeLean.Foundations.QuotientDuality
