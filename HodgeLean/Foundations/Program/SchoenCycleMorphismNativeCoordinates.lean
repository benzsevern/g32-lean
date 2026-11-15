import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap
import HodgeLean.Foundations.Program.SchoenCycleNativeGermComparison

/-! # Centered native coordinates of an actual complex morphism -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
namespace HodgeLean.Foundations.Program

/-- A scheme morphism has analytic centered coordinates, and its native target
chart reconstructs the actual image germ.
Source: HodgeConjecture, `analyticAt_localChart_symm_map`. -/
theorem s2e_morphism_native_centered_coordinates
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) (p : ComplexPoint X) :
    let C := localChart X d p
    let D := localChart Y e (Point.map f p)
    let F := fun z : Fin d → ℂ => D (Point.map f (C.symm (C p + z))) - D (Point.map f p)
    AnalyticAt ℂ F 0 ∧ F 0 = 0 ∧
      (∀ᶠ z in 𝓝 0, D.symm (D (Point.map f p) + F z) = Point.map f (C.symm (C p + z))) := by
  dsimp only
  let C := localChart X d p
  let D := localChart Y e (Point.map f p)
  have hp := mem_localChart_source X d p
  have hfp := mem_localChart_source Y e (Point.map f p)
  have hpoint : Point.map f (C.symm (C p)) = Point.map f p := by rw [C.left_inv hp]
  have hm : Point.map f (C.symm (C p)) ∈ D.source := by rw [hpoint]; exact hfp
  have ha := analyticAt_localChart_symm_map X Y f d e p (C.map_source hp) hm
  have ha' : AnalyticAt ℂ (fun z : Fin d → ℂ => D (Point.map f (C.symm (C p + z)))) 0 :=
    ha.comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero _)
  refine ⟨ha'.sub analyticAt_const, ?_, ?_⟩
  · rw [add_zero, hpoint, sub_self]
  · have ht : Tendsto (fun z : Fin d → ℂ => Point.map f (C.symm (C p + z)))
        (𝓝 0) (𝓝 (Point.map f p)) :=
      (Point.continuous_map f).continuousAt.tendsto.comp (s2e_centered_native_chart_tendsto X d p)
    filter_upwards [ht (D.open_source.mem_nhds hfp)] with z hz
    have hh : D (Point.map f p) +
        (D (Point.map f (C.symm (C p + z))) - D (Point.map f p)) =
          D (Point.map f (C.symm (C p + z))) := by abel
    rw [hh, D.left_inv hz]

end HodgeLean.Foundations.Program
