import HodgeLean.Adapters.NormalConeB4aClassRegularGluing

/-! # Extending the regular normalized class

Route: the regular boundary has two vanishing supported degrees. Its
restriction bijection lifts the glued class to the original cycle-support pair.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace

/-- A cycle whose components have codimension at least `c` has an ambient
supported class normalized at every point outside the regular boundary. -/
theorem a3b4a_classRegular_extension
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ) :
    ∃ β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c),
      ∀ (x : ComplexPoint (Over.mk q)), x ∈ a3b4_cycleSupport q γ →
      x.underlying ∉ a3b4a_classRegularBoundary q γ c →
      ∀ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
        ((Fin r → ℂ) × (Fin c → ℂ))) (he : a3b4_IsHolChart q e)
        (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0),
        x ∈ e.source → ∃ (W : Opens (a3b4_an q))
          (hWe : (W : Set (a3b4_an q)) ⊆ e.source), x ∈ W ∧
          relativeCohomologyMap ℚ (2 * c)
            (a3b4_neighborhoodPairMap (W : Set (a3b4_an q)) (a3b4_cycleSupport q γ)) β =
          a3b4_multiplicity q γ x •
            chartNormalProjectionCoclass (Fin r → ℂ) c e (a3b4_cycleSupport q γ) hS W hWe := by
  let B := a3b4a_classRegularBoundary q γ c
  let U : Opens (a3b4_an q) := (B.preimage
    (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))).compl
  obtain ⟨b, hb⟩ := a3b4a_classRegular_normalCoclass_glue q γ c hc
  obtain ⟨β, hβ⟩ := (a3b4a_classCycle_restriction_bijective_of_boundary_codimension
    q γ c B (a3b4a_classRegularBoundary_le q γ c)
    (a3b4a_classRegularBoundary_coheight q γ c hc)).2 b
  refine ⟨β, ?_⟩
  intro x hxS hxB r e he hS hx
  obtain ⟨W, hWU, hWe, hxW, heq⟩ := hb x hxS hxB r e he hS hx
  refine ⟨W, hWe, hxW, ?_⟩
  exact (a3b4a_classLocal_restriction_comp (a3b4_cycleSupport q γ) hWU (2 * c) β).symm.trans
    ((congrArg (relativeCohomologyMap ℚ (2 * c)
      (neighborhoodSupportInclusionPairMap hWU (a3b4_cycleSupport q γ))) hβ).trans heq)

end HodgeLean.Adapters
