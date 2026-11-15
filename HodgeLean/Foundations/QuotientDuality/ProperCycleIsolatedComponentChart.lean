import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentOpen
import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothGenericNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenHolomorphicChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothHolomorphicChart
import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected
import HodgeLean.Adapters.NormalConeB4aClassRegularLocus

/-! # Actual isolated intrinsic holomorphic points of original pure cycle components
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original pure middle component has an actual holomorphic intrinsic chart point outside every other original component, without ambient smoothness.
Source: EGA IV, 17.5.1, generic smoothness; Fulton, Intersection Theory, section 1.5, separation of pure prime components.
HC no distance; AV milestone no distance. -/
lemma properCycle_isolated_component_holomorphic_point
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (ξ : X.left) (hξ : ξ ∈ γ.support) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint (properCycle_component_over X ξ)) (Fin k → ℂ),
      (∀ i, (f4_analytification (properCycle_component_over X ξ)).IsHolFun
        (fun z : e.source => e z i)) ∧
      ∃ y : ComplexPoint (properCycle_component_over X ξ), y ∈ e.source ∧
        ∀ η ∈ γ.support, η ≠ ξ →
          (Point.map (properCycle_component_over_inclusion X ξ) y).underlying ∉
            closure ({η} : Set X.left) := by
  classical
  let V := properCycle_component_over X ξ
  obtain ⟨W, hW, hgW, hs, hotherW⟩ :=
    properCycle_isolated_component_smooth_open X k hdim γ hc ξ hξ
  let Y := openScheme V W
  letI : Nonempty W := ⟨⟨genericPoint V.left, hgW⟩⟩
  letI : Nonempty Y.left := inferInstanceAs (Nonempty W.toScheme)
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion W.ι
  letI : IsAffine Y.left := hW
  letI : SmoothOfRelativeDimension k Y.hom := hs
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth k Y.hom
  letI : QuasiCompact Y.hom := inferInstance
  letI : IsSeparated Y.hom := inferInstance
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  letI := AlgebraicGeometry.ComplexPoint.connectedSpace Y
  obtain ⟨y₀⟩ := (inferInstance : Nonempty (ComplexPoint Y))
  obtain ⟨e, he, hsource, _⟩ := properCycle_holomorphic_vector_chart_open_transport V W k
    (localChart Y k y₀) (properCycle_smooth_local_chart_holomorphic Y k y₀)
  let y := Point.map (openInclusion V W) y₀
  have hy : y ∈ e.source := by
    rw [hsource]
    exact ⟨y₀, mem_localChart_source Y k y₀, rfl⟩
  refine ⟨e, he, y, hy, ?_⟩
  intro η hη hn
  exact hotherW y.underlying y₀.underlying.property η hη hn

end HodgeLean.Foundations.QuotientDuality
