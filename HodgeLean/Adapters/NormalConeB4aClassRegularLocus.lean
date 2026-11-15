import HodgeLean.Adapters.NormalConeB4aClassRegularBoundaryCodimension

/-! # The regular locus has one smooth component at each support point

Route: choose a component containing the point. The three boundary exclusions
respectively give smoothness, the exact coheight, and separation from every
other component.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- A support point outside the finite boundary lies on one smooth component
of exact codimension `c` and on no other cycle component. -/
theorem a3b4a_classRegularBoundary_unique_component
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (z : Z) (hz : z ∈ a3b4a_classAlgebraicSupport q γ)
    (hzB : z ∉ a3b4a_classRegularBoundary q γ c) :
    ∃ x ∈ γ.support, Order.coheight x = c ∧ z ∈ closure ({x} : Set Z) ∧
      z ∉ reducedClosedSingularRemainder q ⟨closure {x}, isClosed_closure⟩ ∧
      ∀ y ∈ γ.support, y ≠ x → z ∉ closure ({y} : Set Z) := by
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
  have hsing : z ∉ reducedClosedSingularRemainder q ⟨closure {x}, isClosed_closure⟩ := by
    intro hs
    exact hzB ((a3b4a_classRegularBoundary_mem q γ c z).mpr ⟨x, hx, Or.inl hs⟩)
  have hhigh : ¬ (c : ℕ∞) < Order.coheight x := by
    intro hlt
    have hle : ((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight x := by
      simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr hlt
    exact hzB ((a3b4a_classRegularBoundary_mem q γ c z).mpr
      ⟨x, hx, Or.inr (Or.inl ⟨hle, hzx⟩)⟩)
  refine ⟨x, hx, le_antisymm (le_of_not_gt hhigh) (hc x hx), hzx, hsing, ?_⟩
  intro y hy hxy hzy
  exact hzB ((a3b4a_classRegularBoundary_mem q γ c z).mpr
    ⟨x, hx, Or.inr (Or.inr ⟨y, hy, Ne.symm hxy, hzx, hzy⟩)⟩)

end HodgeLean.Adapters
