import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalization

/-! # Literal supported restriction on a one-point space and equality of global supports -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Any actual neighborhood of the point detects the original supported class on a one-point space.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1, maps of relative pairs.
HC no distance; AV milestone no distance. -/
lemma properCycle_subsingleton_neighborhood_restriction_injective
    (X : TopCat.{0}) [Subsingleton X] (S W : Set X) (x : X) (hx : x ∈ W) (n : ℕ) :
    Function.Injective (relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap W S)) := by
  have hW (y : X) : y ∈ W := by rw [Subsingleton.elim y x]; exact hx
  let g : TopPair.ofSubset Sᶜ ⟶ neighborhoodSupportComplementPair W S :=
    TopPair.ofHom (TopCat.ofHom ⟨fun y => ⟨y, hW y⟩, by fun_prop⟩)
      (TopCat.ofHom ⟨fun y => ⟨⟨y.1, hW y.1⟩, y.2⟩, by fun_prop⟩) (by ext; rfl)
  have hg : g ≫ a3b4_neighborhoodPairMap W S = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
  intro a b hab
  have hh := congrArg (relativeCohomologyMap ℚ n g) hab
  simpa only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hg,
    relativeCohomologyMap_id, LinearMap.id_apply] using hh

/-- Equal literal supports make the original enlargement map surjective.
Source: Hatcher, Algebraic Topology, section 3.1, functoriality of relative cohomology.
HC no distance; AV milestone no distance. -/
lemma properCycle_equal_support_enlargement_surjective
    (X : TopCat.{0}) (S T : Set X) (hST : S ⊆ T) (h : S = T) (n : ℕ) :
    Function.Surjective (enlargeSupport ℚ X hST n) := by
  subst T
  have hm : supportInclusionPairMap X hST = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
  intro a
  refine ⟨a, ?_⟩
  simp only [enlargeSupport, hm, relativeCohomologyMap_id, LinearMap.id_apply]

end HodgeLean.Foundations.QuotientDuality
