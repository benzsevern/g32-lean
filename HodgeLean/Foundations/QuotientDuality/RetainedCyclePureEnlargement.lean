import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinatesInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinateNaturality

/-! Detection through literal inclusions of pure middle supports. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Enlargement between pure middle cycle carriers is injective under the supplied ambient orientation. -/
lemma retained_pure_support_enlarge_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ δ : AlgebraicCycle X.left ℚ)
    (hcγ : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (hcδ : ∀ ξ ∈ δ.support, Order.coheight ξ = k)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hv : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x)) :
    Function.Injective (enlargeSupport ℚ (a3b4_an X.hom) h (2*k)) := by
  classical
  intro a b hab
  have ha := properCycle_cap_coordinates_enlarge X k hk hdim γ δ hcγ hcδ h c a
  have hb := properCycle_cap_coordinates_enlarge X k hk hdim γ δ hcγ hcδ h c b
  rw [hab] at ha
  have he := ha.symm.trans hb
  apply properCycle_cap_coordinates_injective X k hk hdim γ hcγ c ho hv
  funext ξ
  have hh := congrFun he ξ.val
  change (if h : ξ.val ∈ γ.support then
      properCycle_cap_coordinates X k hk hdim γ hcγ c a ⟨ξ.val, h⟩ else 0) =
    (if h : ξ.val ∈ γ.support then
      properCycle_cap_coordinates X k hk hdim γ hcγ c b ⟨ξ.val, h⟩ else 0) at hh
  simpa only [dite_eq_left ξ.property] using hh

end HodgeLean.Foundations.QuotientDuality
