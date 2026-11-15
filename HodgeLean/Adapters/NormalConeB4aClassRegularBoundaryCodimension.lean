import HodgeLean.Adapters.NormalConeB4aClassRegularBoundary
import HodgeLean.Adapters.NormalConeB4aClassIntersection
import Mathlib.Order.SuccPred.ENat

/-! # Codimension bounds and component separation off the regular boundary

Route: use the finite boundary's membership description. Each of its three
kinds of points has codimension at least one higher. Outside the boundary,
a support point lies on a unique smooth component of the requested codimension.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The finite regular boundary raises the lower component codimension by one. -/
theorem a3b4a_classRegularBoundary_coheight
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (z : Z) (hz : z ∈ a3b4a_classRegularBoundary q γ c) :
    ((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
  obtain ⟨x, hx, hsing | hhigh | hinter⟩ :=
    (a3b4a_classRegularBoundary_mem q γ c z).mp hz
  · exact a3b4a_classComponent_boundary_coheight q x c (hc x hx) z hsing
  · exact hhigh.1.trans (Order.coheight_anti
      (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hhigh.2)))
  · obtain ⟨y, hy, hxy, hzx, hzy⟩ := hinter
    exact a3b4a_classComponent_intersection_coheight Z c x y z hxy (hc x hx) (hc y hy) hzx hzy

end HodgeLean.Adapters
