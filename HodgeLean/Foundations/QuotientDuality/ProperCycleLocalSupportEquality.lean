import HodgeLean.Adapters.SupportedCycleClassesLocal

/-! # Literal support-change injectivity when the supports agree on the actual neighborhood -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Two-sided inclusion of the actual supports on a neighborhood makes the literal relative support-change pullback injective.
Source: Hatcher, Algebraic Topology, section 3.1, functoriality of relative cohomology.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_support_map_injective
    {M : Type} [TopologicalSpace M] (V S T : Set M) (n : ℕ)
    (hST : ∀ x ∈ V, x ∈ S → x ∈ T) (hTS : ∀ x ∈ V, x ∈ T → x ∈ S) :
    Function.Injective (relativeCohomologyMap ℚ n (SupportedCycleClasses.localSupportMap V S T hST)) := by
  have hc : SupportedCycleClasses.localSupportMap V T S hTS ≫
      SupportedCycleClasses.localSupportMap V S T hST = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext x <;> rfl
  intro a b hab
  have hh := congrArg (relativeCohomologyMap ℚ n
    (SupportedCycleClasses.localSupportMap V T S hTS)) hab
  simpa only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hc,
    relativeCohomologyMap_id, LinearMap.id_apply] using hh

end HodgeLean.Foundations.QuotientDuality
