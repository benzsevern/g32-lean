import HodgeLean.Foundations.QuotientDuality.ProperCycleCenteredCoordinatesNormalization
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalizedCapCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialCenteredCoclass

/-! # Actual cap coordinates imply original cycle class normalization
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Literal actual cap coordinates imply the original all-chart cycle-class normalization under the original ambient concentration and complex orientation hypotheses.
Source: properCycle_centered_coordinates_normalization; properCycle_flattened_chart_tangent_dimension; properCycle_complex_orientation_degree; properCycle_tangential_centered_coclass.
HC no distance; AV milestone no distance. -/
lemma properCycle_coordinates_normalized
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
    (a : s2e_supportedClass X γ k)
    (hcoords : properCycle_cap_coordinates X k hk hdim γ hc
      ((eqToIso (congrArg (fun j => Homology ℚ (a3b4_an X.hom) j)
        (show 2*(2*k) = 2*k+2*k by omega))).hom.hom c) a = (fun ξ => γ ξ.val)) :
    a3b4_IsCycleClass X.hom γ k a := by
  intro r e hflat x hx hxS he
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  have hr := properCycle_flattened_chart_tangent_dimension (a3b4_an X.hom) k r hvan e x hx
  subst r
  let b := properCycle_tangential_centered_chart k k e (e x).1
  have hb := properCycle_tangential_centered_chart_data k k e (e x).1
  have hxb : x ∈ b.source := by rw [hb.1]; exact hx
  have hflatb : ∀ z ∈ b.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (b z).2 = 0 := by
    intro z hz
    change z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0
    exact hflat z (hb.1 ▸ hz)
  have hcenter : b x = (0, 0) := by
    change ((e x).1 - (e x).1, (e x).2) = (0, 0)
    rw [sub_self, (hflat x hx).mp hxS]
  have hholb := properCycle_tangential_centered_chart_holomorphic X k k e he (e x).1
  let L : ((Fin k → ℂ) × (Fin k → ℂ)) ≃L[ℂ] (Fin (k+k) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  let φ := b.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hφ := properCycle_compressed_holomorphic_chart X k k b hholb
  have hpoint := properCycle_complex_orientation_degree X k c hcomplex (k+k) (by omega)
    φ hφ x ⟨hxb, Set.mem_univ _⟩
  obtain ⟨W, hWb, hWo, hxW, hnorm⟩ := properCycle_centered_coordinates_normalization
    X k hk hdim γ hc _ a hcoords b hflatb hholb x hxb hxS hcenter hpoint
  have hWe : W ⊆ e.source := fun z hz => hb.1 ▸ hWb hz
  rw [properCycle_tangential_centered_coclass k k e (e x).1
    (a3b4_cycleSupport X.hom γ) hflat hflatb W hWe hWb] at hnorm
  exact ⟨W, hWe, hWo, hxW, hnorm⟩

end HodgeLean.Foundations.QuotientDuality
