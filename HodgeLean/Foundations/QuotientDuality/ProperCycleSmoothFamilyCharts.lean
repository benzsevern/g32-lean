import HodgeLean.Foundations.QuotientDuality.ProperCycleFamilyRegularBoundary
import HodgeLean.Adapters.NormalConeB4aClassRegularBoundaryCharts
import HodgeLean.Adapters.NormalConeB4aGysinBridge2PrescribedChart

/-! # Actual regular-point normal chart coverage for smooth ambient finite families -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- In a smooth ambient scheme, the constructed common boundary supplies actual normal charts of active representatives at every remaining active point.
Source: Fulton, Intersection Theory, section 19.1, normal coordinates at regular component points.
HC no distance; AV milestone no distance. -/
lemma properCycle_smooth_family_regular_chart_cover
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] [Smooth X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ) (k : ℕ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ)
    (x : ComplexPoint X)
    (hxT : x ∈ ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i))
    (hxB : x.underlying ∉ properCycle_family_regular_boundary X γ q k) :
    ∃ (i : I), q i ≠ 0 ∧ ∃ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ))),
      (∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom (γ i) ↔ (e y).2 = 0) ∧
      a3b4_IsHolChart X.hom e ∧ x ∈ e.source ∧ x ∈ a3b4_cycleSupport X.hom (γ i) := by
  obtain ⟨i, ξ, hi, hξ, hc, hxξ, hreg, hother⟩ :=
    properCycle_family_regular_boundary_isolation X γ q k hcodim x hxT hxB
  obtain ⟨r, e, hxe, he, hflat⟩ :=
    a3b4a_classComponent_exists_holomorphic_flattening_local X k ξ hc x hxξ hreg
  obtain ⟨W, hWe, hxW, hW⟩ := a3b4a_classSupport_local_eq_component X.hom (γ i) ξ hξ x
    (hother i) (⟨e.source, e.open_source⟩ : Opens (ComplexPoint X)) hxe
  let V : Opens (ComplexPoint X) := W
  let e' := e.restrOpen (V : Set (ComplexPoint X)) V.isOpen
  refine ⟨i, hi, r, e', ?_, ?_, ⟨hxe, hxW⟩, ?_⟩
  · intro y hy
    exact (hW y hy.2).trans (hflat y hy.1)
  · exact a3b4g_isHolChart_restrOpen e he (V : Set (ComplexPoint X)) V.isOpen
  · exact Set.mem_iUnion₂.mpr ⟨ξ, hξ, hxξ⟩

end HodgeLean.Foundations.QuotientDuality
