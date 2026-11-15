import HodgeLean.Foundations.Program.SchoenCycleNativeSectionDifferential
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap

/-! # Pullback compatibility of native differentials -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Differentiating the actual pullback of a regular section agrees with composition by the native tangent map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_native_section_differential_pullback
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) (p : ComplexPoint X) (V : Y.left.Opens)
    (hp : (Point.map f p).underlying ∈ V) (s : Γ(Y.left, V)) :
    fderiv ℂ (fun z : Fin d → ℂ =>
      Point.evaluate (f.left ⁻¹ᵁ V) (f.left.app V s)
        ((ComplexPoint.localChart X d p).symm
          (ComplexPoint.localChart X d p p + z))) 0 =
      (fderiv ℂ (fun w : Fin e → ℂ => Point.evaluate V s
        ((ComplexPoint.localChart Y e (Point.map f p)).symm
          (ComplexPoint.localChart Y e (Point.map f p) (Point.map f p) + w))) 0).comp
      (fderiv ℂ (fun z : Fin d → ℂ =>
        ComplexPoint.localChart Y e (Point.map f p)
          (Point.map f ((ComplexPoint.localChart X d p).symm
            (ComplexPoint.localChart X d p p + z)))) 0) := by
  let C := ComplexPoint.localChart X d p
  let D := ComplexPoint.localChart Y e (Point.map f p)
  let G := fun z : Fin d → ℂ => D (Point.map f (C.symm (C p + z)))
  let F := fun w : Fin e → ℂ => Point.evaluate V s (D.symm w)
  have hC : p ∈ C.source := ComplexPoint.mem_localChart_source X d p
  have hD : Point.map f p ∈ D.source := ComplexPoint.mem_localChart_source Y e _
  have hct : AnalyticAt ℂ (fun z : Fin d → ℂ => C p + z) 0 :=
    analyticAt_const.add analyticAt_id
  have hG0 : G 0 = D (Point.map f p) := by
    dsimp only [G]
    rw [add_zero, C.left_inv hC]
  have hG : AnalyticAt ℂ G 0 := by
    have hg := ComplexPoint.analyticAt_localChart_symm_map X Y f d e p
      (C.map_source hC) (by
        change Point.map f (C.symm (C p)) ∈ D.source
        rw [C.left_inv hC]
        exact hD)
    have hg' : AnalyticAt ℂ (fun w => D (Point.map f (C.symm w)))
        ((fun z : Fin d → ℂ => C p + z) 0) := by
      simpa only [add_zero] using hg
    exact hg'.comp hct
  have hF : AnalyticAt ℂ F (D (Point.map f p)) := by
    apply ComplexPoint.analyticAt_localChart_symm_evaluate Y e _ (D.map_source hD) V s
    change D.symm (D (Point.map f p)) ∈ Point.overOpen V
    rw [D.left_inv hD]
    exact hp
  have hCy : ContinuousAt (fun z : Fin d → ℂ => Point.map f (C.symm (C p + z))) 0 := by
    have hc : ContinuousAt C.symm ((fun z : Fin d → ℂ => C p + z) 0) := by
      simpa only [add_zero] using C.continuousAt_symm (C.map_source hC)
    exact (Point.continuous_map f).continuousAt.comp (hc.comp hct.continuousAt)
  have hsource : Point.map f (C.symm (C p + (0 : Fin d → ℂ))) ∈ D.source := by
    simpa only [add_zero, C.left_inv hC] using hD
  have hmem : ∀ᶠ z : Fin d → ℂ in 𝓝 0,
      Point.map f (C.symm (C p + z)) ∈ D.source :=
    hCy (D.open_source.mem_nhds hsource)
  have heq : (fun z : Fin d → ℂ =>
      Point.evaluate (f.left ⁻¹ᵁ V) (f.left.app V s) (C.symm (C p + z))) =ᶠ[𝓝 0]
      F ∘ G := by
    filter_upwards [hmem] with z hz
    rw [← Point.evaluate_map f V s]
    change Point.evaluate V s (Point.map f (C.symm (C p + z))) =
      Point.evaluate V s (D.symm (D (Point.map f (C.symm (C p + z)))))
    rw [D.left_inv hz]
  have hF' : DifferentiableAt ℂ F (G 0) := by
    rw [hG0]
    exact hF.differentiableAt
  change fderiv ℂ (fun z : Fin d → ℂ =>
    Point.evaluate (f.left ⁻¹ᵁ V) (f.left.app V s) (C.symm (C p + z))) 0 = _
  rw [heq.fderiv_eq, fderiv_comp 0 hF' hG.differentiableAt, hG0]
  change (fderiv ℂ F (D (Point.map f p))).comp (fderiv ℂ G 0) =
    (fderiv ℂ (fun w : Fin e → ℂ => F (D (Point.map f p) + w)) 0).comp (fderiv ℂ G 0)
  rw [fderiv_comp_add_left, add_zero]

end HodgeLean.Foundations.Program
