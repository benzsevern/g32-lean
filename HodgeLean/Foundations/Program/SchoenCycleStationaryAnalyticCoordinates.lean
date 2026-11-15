import HodgeLean.Foundations.Program.SchoenCycleNativeSectionDifferential
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Analytic coordinates along stationary regular-section curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
namespace HodgeLean.Foundations.Program

/-- Vanishing derivatives on regular sections give vanishing derivative in any
analytic coordinate expressed in the native chart.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors and local coordinates. -/
theorem s2e_stationary_regular_curve_analytic_coordinate
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (b : ℂ → ComplexPoint B) (hb : ContinuousAt b 0)
    (hregular : ∀ U : B.left.Opens, (b 0).underlying ∈ U →
      ∀ a : Γ(B.left, U), AnalyticAt ℂ (fun t => Point.evaluate U a (b t)) 0)
    (hstationary : ∀ U : B.left.Opens, (b 0).underlying ∈ U →
      ∀ a : Γ(B.left, U), deriv (fun t => Point.evaluate U a (b t)) 0 = 0)
    (E : ComplexPoint B → ℂ)
    (hE : AnalyticAt ℂ (fun z : Fin n → ℂ =>
      E ((localChart B n (b 0)).symm (localChart B n (b 0) (b 0) + z))) 0) :
    HasDerivAt (fun t => E (b t)) 0 0 := by
  let C := localChart B n (b 0)
  let D := localEtaleCoordinates B n (b 0)
  have hp : (b 0).underlying ∈ D.ambientCoordinateOpen := by
    have h := mem_coordinateNeighborhood_of_mem_localChart_source B n (b 0) (b 0)
      (mem_localChart_source B n (b 0))
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      Point.overOpen, Set.mem_setOf_eq] using h
  have hs : ∀ᶠ t in 𝓝 (0 : ℂ), b t ∈ C.source :=
    hb (C.open_source.mem_nhds (mem_localChart_source B n (b 0)))
  have hC : HasDerivAt (fun t => C (b t)) (0 : Fin n → ℂ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have hi := (hregular D.ambientCoordinateOpen hp (D.ambientCoordinateSection i)).differentiableAt.hasDerivAt
    rw [hstationary D.ambientCoordinateOpen hp (D.ambientCoordinateSection i)] at hi
    apply hi.congr_of_eventuallyEq
    filter_upwards [hs] with t ht
    exact localChart_apply_component_eq_evaluate B n (b 0) (b t) ht i
  have hF : HasDerivAt (fun t => C (b t) - C (b 0)) (0 : Fin n → ℂ) 0 :=
    hC.sub_const _
  have hE' : DifferentiableAt ℂ (fun z : Fin n → ℂ =>
      E (C.symm (C (b 0) + z))) (C (b 0) - C (b 0)) := by
    simpa only [sub_self] using hE.differentiableAt
  have hh := hE'.hasFDerivAt.comp_hasDerivAt 0 hF
  simp only [sub_self, map_zero] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hs] with t ht
  change E (b t) = E (C.symm (C (b 0) + (C (b t) - C (b 0))))
  have heq : C (b 0) + (C (b t) - C (b 0)) = C (b t) := by abel
  rw [heq, C.left_inv ht]

end HodgeLean.Foundations.Program
