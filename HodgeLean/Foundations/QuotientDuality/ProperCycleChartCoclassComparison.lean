import HodgeLean.Foundations.QuotientDuality.ProperCycleChartOrientationComparison
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # The original chart normal coclass through actual product support pairs -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual restricted chart is a map from the original neighborhood support-complement pair to the literal zero-normal product support pair.
Source: Fulton, Intersection Theory, section 19.1; Hatcher, Algebraic Topology, section 3.1, normal projection pairs.
HC no distance; AV milestone no distance. -/
def properCycle_chart_normal_support_pair_map
    {M : TopCat.{0}} (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin d → ℂ))) (S : Set M)
    (hS : ∀ z ∈ e.source, z ∈ S ↔ (e z).2 = 0)
    (W : Set M) (hW : W ⊆ e.source) :
    neighborhoodSupportComplementPair W S ⟶
      TopPair.ofSubset (X := TopCat.of (E × (Fin d → ℂ))) (Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))ᶜ) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun w => e w.1, (e.continuousOn.mono hW).domRestrict⟩)
    (fun w hw hz => hw ((hS w.1 (hW w.2)).mpr hz))

/-- The actual restricted chart followed by the literal product normal projection is the original chart normal projection pair map.
Source: Fulton, Intersection Theory, section 19.1; Hatcher, Algebraic Topology, section 3.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_normal_support_pair_projection
    {M : TopCat.{0}} (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin d → ℂ))) (S : Set M)
    (hS : ∀ z ∈ e.source, z ∈ S ↔ (e z).2 = 0)
    (W : Set M) (hW : W ⊆ e.source) :
    properCycle_chart_normal_support_pair_map E d e S hS W hW ≫
        properCycle_product_support_projection E (TopCat.of (Fin d → ℂ)) {0} =
      chartNormalProjectionPair E d e S hS W hW := by
  ext z : 2 <;> rfl

/-- The original chart normal projection coclass is exactly pullback of the original projected standard normal coclass along the actual restricted chart support map.
Source: Fulton, Intersection Theory, section 19.1; Hatcher, Algebraic Topology, section 3.1, relative pullback composition.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_normal_coclass_product
    {M : TopCat.{0}} (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin d → ℂ))) (S : Set M)
    (hS : ∀ z ∈ e.source, z ∈ S ↔ (e z).2 = 0)
    (W : Set M) (hW : W ⊆ e.source) :
    relativeCohomologyMap ℚ (2 * d) (properCycle_chart_normal_support_pair_map E d e S hS W hW)
        (relativeCohomologyMap ℚ (2 * d)
          (properCycle_product_support_projection E (TopCat.of (Fin d → ℂ)) {0})
          (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
            (standardComplexLocalClass_ne_zero_for_chart d))) =
      chartNormalProjectionCoclass E d e S hS W hW := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    properCycle_chart_normal_support_pair_projection]
  rfl

end HodgeLean.Foundations.QuotientDuality
