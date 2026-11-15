import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveSupportCapInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalCollarCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicCodimension

/-! # Injectivity of the literal original middle cycle support cap
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal original middle support cap is injective on every original pure cycle support from the specified ambient point-line and concentration data, including supports in the singular locus.
Source: properCycle_projective_algebraic_support_cap_injective; properCycle_closed_support_dimension_le_of_coheight; properCycle_original_collar_cap.
HC no distance; AV milestone no distance. -/
lemma properCycle_original_support_cap_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (hlocal : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hvan : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x)) :
    Function.Injective (properCycle_original_support_cap X γ k c) := by
  letI : LocallyOfFiniteType X.hom := inferInstance
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  have hS := properCycle_closed_support_dimension_le_of_coheight X
    (a3b4a_classAlgebraicSupport X.hom γ) k
    (a3b4a_classAlgebraicSupport_coheight X.hom γ k (fun ξ hξ => (hc ξ hξ).ge))
  rw [hdim, show 2*k-k = k by omega] at hS
  have h := properCycle_projective_algebraic_support_cap_injective X
    (a3b4a_classAlgebraicSupport X.hom γ) k hS
    (properCycle_original_support_collar X γ) (2*k) ⟨k, by omega⟩ c hlocal hvan
  change Function.Injective ((properCycle_original_support_collar X γ).cap
    (a3b4a_classSupport_isClosed X.hom γ) (2*k) (2*k) c) at h
  rw [properCycle_original_collar_cap] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
