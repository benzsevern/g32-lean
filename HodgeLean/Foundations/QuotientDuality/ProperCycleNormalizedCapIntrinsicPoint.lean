import HodgeLean.Foundations.QuotientDuality.ProperCycleChartCapIntrinsicPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalizedCollarNeighborhood

/-! # Original normalized classes and actual intrinsic component cap values
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_normalizedCapIntrinsicPoint_t2
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : T2Space (ComplexPoint X) := f4_t2Space X

local instance properCycle_normalizedCapIntrinsicPoint_an_t2
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : T2Space (a3b4_an X.hom) := f4_t2Space X

/-- Original cycle-class normalization gives the actual intrinsic component cap point value on each original centered holomorphic component chart, retaining the literal cycle multiplicity and the specified ambient orientation.
Source: properCycle_normalized_collar_neighborhood; properCycle_chart_cap_intrinsic_point.
HC no distance; AV milestone no distance. -/
lemma properCycle_normalized_cap_intrinsic_point
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (ξ : X.left) (hξ : ξ ∈ γ.support)
    (k : ℕ) (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (k : ℕ))
    (C : ProperCycleSupportCollar (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ))
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
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
      (C.cap (a3b4a_classSupport_isClosed X.hom γ) (2*k) (2*k) c a) z =
      (a3b4_multiplicity X.hom γ z.val * properCycle_standard_complex_cap_scalar k k) •
        localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
          (properCycle_intrinsic_component_on_support X γ ξ hξ k hdim) z := by
  dsimp only
  intro hc
  let z := properCycle_component_support_map X γ ξ hξ y
  obtain ⟨W, hWe, hzW, hWN, hR, hWa⟩ := properCycle_normalized_collar_neighborhood
    X γ k a ha C k e hflat he z.val (hOe z hy) z.property
  exact properCycle_chart_cap_intrinsic_point X γ ξ hξ k k hdim C e hflat he
    O hOr hOe y hy W hWe hWN hR hzW hcenter (a3b4_multiplicity X.hom γ z.val) a hWa c hc

end HodgeLean.Foundations.QuotientDuality
