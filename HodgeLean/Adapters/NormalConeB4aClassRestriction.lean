import HodgeLean.Adapters.NormalConeB4aClassLocal
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # Refinement of the local normalization neighborhoods

The existence witnesses in the frozen normalization predicate can be refined
to a common neighborhood. This gives the local zero restrictions needed by
the uniqueness argument.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular

/-- Restricting an ambient supported class in two steps agrees with direct restriction. -/
theorem a3b4a_classLocal_restriction_comp
    {M : Type} [TopologicalSpace M] {W V : Set M} (S : Set M)
    (hWV : W ⊆ V) (n : ℕ)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of M) Sᶜ) n) :
    relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap hWV S)
      (relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap V S) β) =
        relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap W S) β := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  rfl

/-- A local normal-coclass equality persists after shrinking its neighborhood. -/
theorem a3b4a_classLocal_normalization_mono
    {M : Type} [TopologicalSpace M] {r c : ℕ}
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    {W V : Set M} (hWV : W ⊆ V) (hV : V ⊆ e.source)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of M) Sᶜ) (2 * c))
    (m : ℚ)
    (hβ : relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap V S) β =
      m • chartNormalProjectionCoclass (Fin r → ℂ) c e S hS V hV) :
    relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap W S) β =
      m • chartNormalProjectionCoclass (Fin r → ℂ) c e S hS W (hWV.trans hV) := by
  rw [← a3b4a_classLocal_restriction_comp S hWV (2 * c) β, hβ, map_smul,
    chartNormalProjectionCoclass_restrict]

/-- Two normalized classes have a difference that vanishes on a neighborhood
of each point tested by a holomorphic flattening chart. -/
theorem a3b4a_classLocal_difference_vanishes
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (β β' : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) (hβ' : a3b4_IsCycleClass q γ c β')
    (r : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0)
    (x : ComplexPoint (Over.mk q)) (hx : x ∈ e.source)
    (hxS : x ∈ a3b4_cycleSupport q γ) (he : a3b4_IsHolChart q e) :
    ∃ W : Set (ComplexPoint (Over.mk q)), W ⊆ e.source ∧ IsOpen W ∧ x ∈ W ∧
      relativeCohomologyMap ℚ (2 * c)
        (a3b4_neighborhoodPairMap W (a3b4_cycleSupport q γ)) (β - β') = 0 := by
  obtain ⟨V, hV, hVo, hxV, hVβ⟩ := hβ r e hS x hx hxS he
  obtain ⟨V', hV', hV'o, hxV', hV'β'⟩ := hβ' r e hS x hx hxS he
  refine ⟨V ∩ V', Set.inter_subset_left.trans hV, hVo.inter hV'o, ⟨hxV, hxV'⟩, ?_⟩
  rw [map_sub,
    a3b4a_classLocal_normalization_mono e _ hS Set.inter_subset_left hV β _ hVβ,
    a3b4a_classLocal_normalization_mono e _ hS Set.inter_subset_right hV' β' _ hV'β',
    sub_self]

end HodgeLean.Adapters
