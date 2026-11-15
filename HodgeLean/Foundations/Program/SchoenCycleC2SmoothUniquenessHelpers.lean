import HodgeLean.Adapters.NormalConeB4aClassUniqueBoundary
import HodgeLean.Adapters.NormalConeB4aClassRegularBoundaryCharts
import HodgeLean.Adapters.NormalConeB4aClassRegularBoundaryCodimension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- On a smooth ambient scheme local complex normalization determines the
supported cycle class under the component codimension bound. -/
theorem s2e_cycleClass_unique_smooth
    {Z : Scheme.{0}} (q : Z ⟶ Spec ↧ℂ) [Smooth q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) (k : ℕ)
    (hcodim : ∀ ξ ∈ γ.support, (k : ℕ∞) ≤ Order.coheight ξ)
    (c d : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * k))
    (hc : a3b4_IsCycleClass q γ k c) (hd : a3b4_IsCycleClass q γ k d) : c = d := by
  exact a3b4a_cycleClass_unique_of_regularBoundary q γ k hcodim
    (a3b4a_classRegularBoundary q γ k)
    (a3b4a_classRegularBoundary_le q γ k)
    (a3b4a_classRegularBoundary_coheight q γ k hcodim)
    (fun x hx hxB => a3b4a_classRegularBoundary_charts q γ k hcodim x hx hxB) c d hc hd

end HodgeLean.Foundations.Program
