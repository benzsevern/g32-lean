import HodgeLean.Foundations.TubularEuler.AffineIdealDifferentialHelpers
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! # Original immersion equations annihilate the original tangent map

Regular ideal sections vanish on the actual image of the immersion. Their
chart derivatives therefore vanish on its actual coordinate derivative.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology Filter
namespace HodgeLean.Foundations.TubularEuler

/-- Differentiating an original immersion-ideal section along the immersion
annihilates its actual coordinate derivative.
Source: Hartshorne, Algebraic Geometry, II.8, conormal sequence; chain rule.
HC no distance; AV milestone no distance. -/
theorem affineIdealDifferential_comp_immersion_derivative_zero
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d m : ℕ) [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension m Y.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (S : (Fin m → ℂ) →L[ℂ] (Fin d → ℂ))
    (hS : HasFDerivAt (fun b => (chartAt (Fin d → ℂ) z)
        (Point.map j ((chartAt (Fin m → ℂ) x).symm b))) S
      ((chartAt (Fin m → ℂ) x) x))
    (u : RingHom.ker (j.left.app A).hom) :
    (affineIdealDifferential X Y j d A hA x hx z hz u).comp S = 0 := by
  let a := chartAt (Fin m → ℂ) x
  let b := chartAt (Fin d → ℂ) z
  have ha : x ∈ a.source := mem_chart_source _ x
  have hxinv : a.symm (a x) = x := a.left_inv ha
  let f := fun t : Fin m → ℂ => Point.map j (a.symm t)
  have hf : ContinuousAt f (a x) :=
    (Point.continuous_map j).continuousAt.comp (a.symm.continuousAt (a.map_source ha))
  have hfsource : ∀ᶠ t in 𝓝 (a x), f t ∈ b.source := by
    apply hf.eventually
    apply b.open_source.mem_nhds
    simpa only [f, hxinv] using hz
  have heq : (fun t : Fin m → ℂ => Point.evaluate A u.val (b.symm (b (f t))))
      =ᶠ[𝓝 (a x)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hfsource] with t ht
    rw [b.left_inv ht, Point.evaluate_map]
    change Point.evaluate (j.left ⁻¹ᵁ A) (j.left.app A u.val) (a.symm t) = 0
    rw [u.property]
    simp [Point.evaluate]
  have hd := actualStalkDifferential_hasFDerivAt_section X d z (Point.map j x) hz A hx u.val
  have hbase : b (f (a x)) = b (Point.map j x) := by simp only [f, hxinv]
  have hd' : HasFDerivAt (fun t => Point.evaluate A u.val (b.symm t))
      (affineIdealDifferential X Y j d A hA x hx z hz u) (b (f (a x))) := by
    rw [hbase]
    exact hd
  have hc := hd'.comp (a x) hS
  have hzero : HasFDerivAt (fun _ : Fin m → ℂ => (0 : ℂ)) (0 : (Fin m → ℂ) →L[ℂ] ℂ) (a x) :=
    hasFDerivAt_const _ _
  exact (hc.congr_of_eventuallyEq heq.symm).unique hzero

#print axioms affineIdealDifferential_comp_immersion_derivative_zero

end HodgeLean.Foundations.TubularEuler
