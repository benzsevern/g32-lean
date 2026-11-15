import HodgeLean.Adapters.NormalConeB4aGysinNormalDisk
import HodgeLean.Adapters.NormalConeB4aGysinNormalization

/-! # Normal evaluations of normalized cycle classes

Chart normalization and evaluation on fixed normal generators are equivalent.
The forward direction uses excision to pass from the normalization neighborhood
to the prescribed flattened-support neighborhood.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular

/-- A normalized cycle class evaluates to its multiplicity on every normal generator. -/
theorem a3b4a_gysin_normal_evaluation_of_cycleClass
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) (r : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0)
    (x : ComplexPoint (Over.mk q)) (hx : x ∈ e.source)
    (hxS : x ∈ a3b4_cycleSupport q γ) (he : a3b4_IsHolChart q e) :
    relativeCohomologyEquivDualHomology ℚ _ (2 * c)
      (relativeCohomologyMap ℚ (2 * c)
        (a3b4_neighborhoodPairMap
          (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx) (a3b4_cycleSupport q γ)) β)
      (flattenedSupportNormalClass (Fin r → ℂ) c e x hx
        (a3b4_cycleSupport q γ) hS ((hS x hx).mp hxS)) = a3b4_multiplicity q γ x := by
  obtain ⟨W, hWe, hWo, hxW, hWβ⟩ := hβ r e hS x hx hxS he
  exact a3b4a_gysin_normal_evaluation_of_local_normalization e _ hS x hx
    ((hS x hx).mp hxS) β _ W hWo hxW hWe hWβ

end HodgeLean.Adapters
