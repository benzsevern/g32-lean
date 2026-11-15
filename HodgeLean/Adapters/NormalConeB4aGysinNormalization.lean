import HodgeLean.Adapters.NormalConeB4aClassNormalization

/-! # Detecting cycle normalization by normal-disk evaluation

A local numerical intersection calculation suffices: evaluate on the canonical
normal homology generator, then use the one-dimensional normal cohomology group.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular

/-- Normal-generator evaluations determine the chart normalization of a supported class. -/
theorem a3b4a_gysin_cycleClass_of_normal_evaluation
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (heval : ∀ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ)))
      (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0)
      (x : ComplexPoint (Over.mk q)) (hx : x ∈ e.source)
      (hxS : x ∈ a3b4_cycleSupport q γ), a3b4_IsHolChart q e →
      relativeCohomologyEquivDualHomology ℚ _ (2 * c)
        (relativeCohomologyMap ℚ (2 * c)
          (a3b4_neighborhoodPairMap
            (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx) (a3b4_cycleSupport q γ)) β)
        (flattenedSupportNormalClass (Fin r → ℂ) c e x hx
          (a3b4_cycleSupport q γ) hS ((hS x hx).mp hxS)) = a3b4_multiplicity q γ x) :
    a3b4_IsCycleClass q γ c β := by
  intro r e hS x hx hxS he
  refine ⟨flattenedSupportNeighborhood (Fin r → ℂ) c e x hx,
    flattenedSupportNeighborhood_subset_source (Fin r → ℂ) c e x hx,
    (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx).isOpen,
    mem_flattenedSupportNeighborhood (Fin r → ℂ) c e x hx, ?_⟩
  exact a3b4a_classLocal_eq_smul_normalCoclass e (a3b4_cycleSupport q γ) hS x hx hxS
    _ _ (heval r e hS x hx hxS he)

end HodgeLean.Adapters
