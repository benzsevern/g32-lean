import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothGenericNeighborhood
import HodgeLean.Adapters.NormalConeB4aClassRegularLocus

/-! # Actual generic smooth component opens separated from every other prime
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original pure middle component has an actual affine smooth generic open whose whole image avoids every other original component.
Source: EGA IV, 17.5.1, generic smoothness; Fulton, Intersection Theory, section 1.5, separation of pure prime supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_isolated_component_smooth_open
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (ξ : X.left) (hξ : ξ ∈ γ.support) :
    ∃ W : (properCycle_component_over X ξ).left.Opens, IsAffineOpen W ∧
      genericPoint (properCycle_component_over X ξ).left ∈ W ∧
      SmoothOfRelativeDimension k (openScheme (properCycle_component_over X ξ) W).hom ∧
      ∀ z : (properCycle_component_over X ξ).left, z ∈ W →
        ∀ η ∈ γ.support, η ≠ ξ →
          (properCycle_component_over_inclusion X ξ).left z ∉ closure ({η} : Set X.left) := by
  classical
  let V := properCycle_component_over X ξ
  let i := properCycle_component_over_inclusion X ξ
  let B := a3b4a_classRegularBoundary X.hom γ k
  have hlow : ∀ η ∈ γ.support, (k : ℕ∞) ≤ Order.coheight η := by
    intro η hη
    rw [hc η hη]
  have hξB : ξ ∉ B := by
    intro hB
    have h := a3b4a_classRegularBoundary_coheight X.hom γ k hlow ξ hB
    rw [hc ξ hξ] at h
    have hn : ¬ (((k+1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)) := by
      exact_mod_cast (show ¬ (k+1 ≤ k) by omega)
    exact hn h
  let U : V.left.Opens := i.left ⁻¹ᵁ B.compl
  have hgU : genericPoint V.left ∈ U := by
    change cycleComponentι X.left ξ (genericPoint (cycleComponent X.left ξ)) ∉ B
    rw [properCycle_component_generic_point]
    exact hξB
  have hVDim : topologicalKrullDim V.left = (k : ℕ) :=
    properCycle_middle_component_dimension X k hdim ξ (hc ξ hξ)
  have hdV : TopologicalSpace.dim V.left = k := by
    unfold TopologicalSpace.dim
    rw [hVDim]
    rfl
  obtain ⟨W, hW, hgW, hWU, hs⟩ := properCycle_smooth_affine_generic_neighborhood V k hdV U hgU
  refine ⟨W, hW, hgW, hs, ?_⟩
  intro z hzW η hη hn hzη
  have hzB : i.left z ∉ B := hWU hzW
  have hzξ : i.left z ∈ closure ({ξ} : Set X.left) := by
    rw [← range_cycleComponentι]
    exact ⟨z, rfl⟩
  exact hzB ((a3b4a_classRegularBoundary_mem X.hom γ k (i.left z)).mpr
    ⟨ξ, hξ, Or.inr (Or.inr ⟨η, hη, hn.symm, hzξ, hzη⟩)⟩)

end HodgeLean.Foundations.QuotientDuality
