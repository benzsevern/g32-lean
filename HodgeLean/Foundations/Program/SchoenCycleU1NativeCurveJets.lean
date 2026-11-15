import HodgeLean.Foundations.Program.SchoenCycleU1LocalizedJets
import HodgeLean.Foundations.Program.SchoenCycleU1NativeCoordinates

/-! # Native coordinate curves and their regular section jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open Point
namespace HodgeLean.Foundations.Program

/-- The actual native inverse-chart curve in its one-dimensional coordinate.
Source: HodgeConjecture, `localChart`, native complex curve charts. -/
def s2e_u1_nativeCurve (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    (p : ComplexPoint Z) (t : ℂ) : ComplexPoint Z :=
  (localChart Z 1 p).symm (fun i => localChart Z 1 p p i + t)

/-- The native coordinate curve has the specified base point.
Source: HodgeConjecture, `mem_localChart_source`; Mathlib, inverse-chart identity. -/
theorem s2e_u1_nativeCurve_zero
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z) :
    s2e_u1_nativeCurve Z p 0 = p := by
  simpa only [s2e_u1_nativeCurve, add_zero] using
    (localChart Z 1 p).left_inv (mem_localChart_source Z 1 p)

/-- Every regular section on any neighbourhood of the base point has an
actual analytic evaluation along the native coordinate curve.
Source: HodgeConjecture, `analyticAt_localChart_symm_evaluate` and `isOpen_overOpen`. -/
theorem s2e_u1_nativeCurve_regular_sections
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z)
    (U : Z.left.Opens) (hp : p.underlying ∈ U) :
    (∀ᶠ t : ℂ in 𝓝 0, (s2e_u1_nativeCurve Z p t).underlying ∈ U) ∧
      ∀ s : Γ(Z.left, U), AnalyticAt ℂ
        (fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)) 0 := by
  let a : ℂ → (Fin 1 → ℂ) := fun t i => localChart Z 1 p p i + t
  have ha : AnalyticAt ℂ a 0 := by
    apply AnalyticAt.pi
    intro i
    exact analyticAt_const.add analyticAt_id
  have ha0 : a 0 = localChart Z 1 p p := by ext i; exact add_zero _
  have ht : a 0 ∈ (localChart Z 1 p).target := by
    rw [ha0]
    exact (localChart Z 1 p).map_source (mem_localChart_source Z 1 p)
  have hc : ContinuousAt (s2e_u1_nativeCurve Z p) 0 :=
    ((localChart Z 1 p).continuousAt_symm ht).comp ha.continuousAt
  have hU : ∀ᶠ t : ℂ in 𝓝 0, s2e_u1_nativeCurve Z p t ∈ overOpen U := by
    apply hc.eventually
    apply (isOpen_overOpen U).mem_nhds
    simpa only [s2e_u1_nativeCurve_zero, overOpen, Set.mem_setOf_eq] using hp
  refine ⟨by simpa only [overOpen, Set.mem_setOf_eq] using hU, ?_⟩
  intro s
  have hbase : (localChart Z 1 p).symm (a 0) ∈ overOpen U := by
    change s2e_u1_nativeCurve Z p 0 ∈ overOpen U
    simpa only [s2e_u1_nativeCurve_zero, overOpen, Set.mem_setOf_eq] using hp
  exact (analyticAt_localChart_symm_evaluate Z 1 p ht U s hbase).comp ha

/-- The defining regular coordinate has derivative one on the actual native curve.
Source: HodgeConjecture, `localChart`; Mathlib, inverse-chart identity and derivative of identity. -/
theorem s2e_u1_nativeCurve_coordinate_derivative
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z) :
    deriv (fun t => Point.evaluate
      (localEtaleCoordinates Z 1 p).ambientCoordinateOpen
      ((localEtaleCoordinates Z 1 p).ambientCoordinateSection 0)
      (s2e_u1_nativeCurve Z p t)) 0 = 1 := by
  let a : ℂ → (Fin 1 → ℂ) := fun t i => localChart Z 1 p p i + t
  have ha : AnalyticAt ℂ a 0 := by
    apply AnalyticAt.pi
    intro i
    exact analyticAt_const.add analyticAt_id
  have ha0 : a 0 = localChart Z 1 p p := by ext i; exact add_zero _
  have ht0 : a 0 ∈ (localChart Z 1 p).target := by
    rw [ha0]
    exact (localChart Z 1 p).map_source (mem_localChart_source Z 1 p)
  have ht : ∀ᶠ t : ℂ in 𝓝 0, a t ∈ (localChart Z 1 p).target :=
    ha.continuousAt.eventually ((localChart Z 1 p).open_target.mem_nhds ht0)
  have he : (fun t => Point.evaluate
      (localEtaleCoordinates Z 1 p).ambientCoordinateOpen
      ((localEtaleCoordinates Z 1 p).ambientCoordinateSection 0)
      (s2e_u1_nativeCurve Z p t)) =ᶠ[𝓝 0]
        (fun t => localChart Z 1 p p 0 + t) := by
    filter_upwards [ht] with t ht
    exact s2e_u1_native_inverse_chart_regular_coordinate Z p (a t) ht
  rw [he.deriv_eq]
  exact ((hasDerivAt_id (0 : ℂ)).const_add (localChart Z 1 p p 0)).deriv

end HodgeLean.Foundations.Program
