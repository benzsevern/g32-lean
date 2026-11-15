import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalizedChartCoordinate
import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialCenteredHolomorphic
import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedChartPiece
import HodgeLean.Foundations.QuotientDuality.ProperCycleFlattenedChartDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleCompressedHolomorphicChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexOrientationDegree

/-! # Original normalization determines literal actual cap coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_normalizedCapCoordinates_t2
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : T2Space (ComplexPoint X) := f4_t2Space X

local instance properCycle_normalizedCapCoordinates_an_t2
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : T2Space (a3b4_an X.hom) := f4_t2Space X

/-- Original cycle-class normalization determines every literal actual cap coordinate under the original component-chart and ambient complex-orientation hypotheses.
Source: properCycle_normalized_chart_coordinate; properCycle_flattened_chart_tangent_dimension; properCycle_complex_orientation_degree.
HC no distance; AV milestone no distance. -/
lemma properCycle_normalized_cap_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (c : Homology ℚ (a3b4_an X.hom) (2*(2*k)))
    (hvan : ∀ j : ℕ, j ≠ 2*(2*k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (hcomplex : ∀ (e : OpenPartialHomeomorph (ComplexPoint X) (Fin (2*k) → ℂ)),
      (∀ i, (f4_analytification X).IsHolFun (fun z : e.source => e z i)) →
      ∀ (x : ComplexPoint X) (hx : x ∈ e.source),
        localOrientation (a3b4_an X.hom) (2*(2*k)) c x = localClassOfChart (2*k) e x hx)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (hcharts : ∀ η ∈ γ.support, ∃ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
      (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0),
      a3b4_IsHolChart X.hom e ∧ ∃ z : ComplexPoint X,
        z ∈ e.source ∧ z ∈ a3b4_cycleSupport X.hom γ ∧
        Point.underlying z ∈ closure {η} ∧
        ∀ ζ ∈ γ.support, Point.underlying z ∈ closure {ζ} → ζ = η)
    (a : s2e_supportedClass X γ k) (ha : a3b4_IsCycleClass X.hom γ k a) :
    properCycle_cap_coordinates X k hk hdim γ hc
      ((eqToIso (congrArg (fun j => Homology ℚ (a3b4_an X.hom) j)
        (show 2*(2*k) = 2*k+2*k by omega))).hom.hom c) a = (fun ξ => γ ξ.val) := by
  funext ξ
  obtain ⟨r, e, hflat, he, x, hx, hxS, hxξ, hother⟩ := hcharts ξ.val ξ.property
  have hr := properCycle_flattened_chart_tangent_dimension (a3b4_an X.hom) k r hvan e x hx
  subst r
  let b := properCycle_tangential_centered_chart k k e (e x).1
  have hb := properCycle_tangential_centered_chart_data k k e (e x).1
  have hxb : x ∈ b.source := by rw [hb.1]; exact hx
  have hflatb : ∀ z ∈ b.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (b z).2 = 0 := by
    intro z hz
    have hz' : z ∈ e.source := hb.1 ▸ hz
    change z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0
    exact hflat z hz'
  have hcenter : b x = (0, 0) := by
    change ((e x).1 - (e x).1, (e x).2) = (0, 0)
    rw [sub_self, (hflat x hx).mp hxS]
  have hholb := properCycle_tangential_centered_chart_holomorphic X k k e he (e x).1
  have havoid : ∀ η ∈ γ.support, η ≠ ξ.val → x.underlying ∉ closure ({η} : Set X.left) := by
    intro η hη hne hxη
    exact hne (hother η hη hxη)
  obtain ⟨y, hy, O, hOr, hOe, hyO⟩ := properCycle_isolated_chart_piece
    X γ ξ.val ξ.property b x hxb hxS hxξ havoid
  have hcentery : b (properCycle_component_support_map X γ ξ.val ξ.property y).val = (0, 0) := by
    rw [hy]
    exact hcenter
  have havoidy : ∀ η ∈ γ.support, η ≠ ξ.val →
      (properCycle_component_support_map X γ ξ.val ξ.property y).val.underlying ∉ closure ({η} : Set X.left) := by
    rw [hy]
    exact havoid
  let L : ((Fin k → ℂ) × (Fin k → ℂ)) ≃L[ℂ] (Fin (k+k) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  let φ := b.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hφ := properCycle_compressed_holomorphic_chart X k k b hholb
  have hpoint := properCycle_complex_orientation_degree X k c hcomplex (k+k) (by omega)
    φ hφ (properCycle_component_support_map X γ ξ.val ξ.property y).val
    ⟨hOe _ hyO, Set.mem_univ _⟩
  exact properCycle_normalized_chart_coordinate X k hk hdim γ hc ξ.val ξ.property
    b hflatb hholb O hOr hOe y hyO hcentery havoidy a ha _ hpoint

end HodgeLean.Foundations.QuotientDuality
