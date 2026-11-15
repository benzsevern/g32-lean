import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalizedCapIntrinsicPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinatePointDetection
import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalCollarCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportPointValues
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity

/-! # Literal coefficients of originally normalized classes on centered component charts
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- On a centered original holomorphic component chart, the actual cap coordinate of an originally normalized class is its literal cycle coefficient.
Source: properCycle_normalized_cap_intrinsic_point; properCycle_cap_coordinate_point_detection; a3b4a_classMultiplicity_eq_component.
HC no distance; AV milestone no distance. -/
lemma properCycle_normalized_chart_coordinate
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdimX : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hcodim : ∀ η ∈ γ.support, Order.coheight η = k)
    (ξ : X.left) (hξ : ξ ∈ γ.support)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin k → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)))
    (hOr : (O : Set (a3b4_cycleSupport X.hom γ)) ⊆
      Set.range (properCycle_component_support_map X γ ξ hξ))
    (hOe : ∀ s ∈ O, s.val ∈ e.source)
    (y : ComplexPoint (properCycle_component_over X ξ))
    (hy : properCycle_component_support_map X γ ξ hξ y ∈ O)
    (hcenter : e (properCycle_component_support_map X γ ξ hξ y).val = (0, 0))
    (hother : ∀ η ∈ γ.support, η ≠ ξ →
      (properCycle_component_support_map X γ ξ hξ y).val.underlying ∉ closure ({η} : Set X.left))
    (a : s2e_supportedClass X γ k) (ha : a3b4_IsCycleClass X.hom γ k a)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) :
    let z := properCycle_component_support_map X γ ξ hξ y
    let L : ((Fin k → ℂ) × (Fin k → ℂ)) ≃L[ℂ] (Fin (k+k) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
    let degree := eqToIso (congrArg (fun n => orientationGroup (a3b4_an X.hom) n z.val)
      (show 2*(k+k) = 2*k+2*k by omega))
    localOrientation (a3b4_an X.hom) (2*k+2*k) c z.val = degree.hom.hom
      (localClassOfChart (k+k) φ z.val ⟨hOe z hy, Set.mem_univ _⟩) →
    properCycle_cap_coordinates X k hk hdimX γ hcodim c a ⟨ξ, hξ⟩ = γ ξ := by
  dsimp only
  intro hc
  let z := properCycle_component_support_map X γ ξ hξ y
  have hdim := properCycle_middle_component_dimension X k hdimX ξ (hcodim ξ hξ)
  have hp := properCycle_normalized_cap_intrinsic_point X γ ξ hξ k hdim
    (properCycle_original_support_collar X γ) e hflat he O hOr hOe y hy hcenter a ha c hc
  rw [properCycle_original_collar_cap] at hp
  have hzξ : z.val.underlying ∈ closure ({ξ} : Set X.left) := by
    have hz : z ∈ Set.range (properCycle_component_support_map X γ ξ hξ) := ⟨y, rfl⟩
    rw [properCycle_component_support_map_range] at hz
    exact hz
  have hm := a3b4a_classMultiplicity_eq_component X.hom γ ξ hξ z.val hzξ hother
  rw [hm] at hp
  obtain ⟨b, hsrc, hhol, hval⟩ := properCycle_component_flat_holomorphic_chart
    X γ ξ hξ k k e hflat he O hOr hOe y hy
  have hyb : y ∈ b.source := by rw [hsrc]; exact hy
  have hn := properCycle_intrinsic_support_component_point_ne_zero X γ ξ hξ k hdim b hhol y hyb hother
  exact properCycle_cap_coordinate_point_detection X k hk hdimX γ hcodim c a ⟨ξ, hξ⟩ z hother (γ ξ) hn hp

end HodgeLean.Foundations.QuotientDuality
