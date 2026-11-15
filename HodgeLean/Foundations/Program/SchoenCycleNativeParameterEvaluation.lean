import HodgeLean.Foundations.Program.SchoenCycleNativeCurveParameter
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold

/-! # Actual regular parameter sections in the chosen native chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- On the chosen native chart source, the actual ambient centered regular
section evaluates to the native chart coordinate difference.
Source: HodgeConjecture, AlgebraicGeometry.ComplexPoint.localChart_apply_of_mem;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_native_chart_centered_section_evaluate
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (p q : ComplexPoint X) (hq : q ∈ (ComplexPoint.localChart X 1 p).source) :
    let D := localEtaleCoordinates X 1 p.underlying
    let pU := ComplexPoint.asOpenPoint X D.neighborhood p D.mem
    Point.evaluate D.ambientCoordinateOpen (s2e_native_ambient_centered_section X p.underlying D pU) q =
      ComplexPoint.localChart X 1 p q 0 - ComplexPoint.localChart X 1 p p 0 := by
  let D := localEtaleCoordinates X 1 p.underlying
  let pU := ComplexPoint.asOpenPoint X D.neighborhood p D.mem
  have hqU : q ∈ Point.overOpen D.neighborhood :=
    ComplexPoint.mem_coordinateNeighborhood_of_mem_localChart_source X 1 p q hq
  let qU := ComplexPoint.asOpenPoint X D.neighborhood q hqU
  have hmapq : Point.map (ComplexPoint.openInclusion X D.neighborhood) qU = q := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X D.neighborhood q hqU
  have hchartq : ComplexPoint.localChart X 1 p q = D.analyticCoordinates qU :=
    ComplexPoint.localChart_apply_of_mem X 1 p q hq
  have hchartp : ComplexPoint.localChart X 1 p p = D.analyticCoordinates pU :=
    ComplexPoint.localChart_apply_of_mem X 1 p p (ComplexPoint.mem_localChart_source X 1 p)
  have h := s2e_native_ambient_centered_section_evaluate X p.underlying D pU qU
  rw [hmapq, ← hchartq, ← hchartp] at h
  exact h

/-- The native regular parameter has an actual section representative whose
evaluations agree with the centered chosen chart coordinate.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8;
HodgeConjecture, AlgebraicGeometry.ComplexPoint.localChart_apply_of_mem. -/
theorem s2e_native_curve_parameter_regular_chart
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] (p : ComplexPoint X) :
    ∃ (U : X.left.Opens) (hp : p.underlying ∈ U) (s : Γ(X.left, U)),
      X.left.presheaf.germ U p.underlying hp s = s2e_native_curve_parameter X p ∧
      ∀ q ∈ (ComplexPoint.localChart X 1 p).source,
        Point.evaluate U s q =
          ComplexPoint.localChart X 1 p q 0 - ComplexPoint.localChart X 1 p p 0 := by
  let D := localEtaleCoordinates X 1 p.underlying
  let pU := ComplexPoint.asOpenPoint X D.neighborhood p D.mem
  have hp : p.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using D.mem
  refine ⟨D.ambientCoordinateOpen, hp, s2e_native_ambient_centered_section X p.underlying D pU,
    rfl, ?_⟩
  intro q hq
  exact s2e_native_chart_centered_section_evaluate X p q hq

/-- A centered chart coordinate evaluates to the scalar parameter along the
centered inverse-chart line near its origin.
Source: Mathlib, OpenPartialHomeomorph.right_inv and openness of chart targets. -/
theorem s2e_centered_chart_evaluation
    {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (p : M) (hp : p ∈ e.source) (f : M → ℂ)
    (hf : ∀ q ∈ e.source, f q = e q 0 - e p 0) :
    (fun z : ℂ => f (e.symm (e p + fun _ : Fin 1 => z))) =ᶠ[nhds 0] (fun z => z) := by
  have hcont : Continuous (fun z : ℂ => e p + fun _ : Fin 1 => z) :=
    continuous_const.add (continuous_pi fun _ => continuous_id)
  have ht : ∀ᶠ z : ℂ in nhds 0, e p + (fun _ : Fin 1 => z) ∈ e.target := by
    have hT : Filter.Tendsto (fun z : ℂ => e p + fun _ : Fin 1 => z) (nhds 0) (nhds (e p)) := by
      have hzero : e p + (fun _ : Fin 1 => (0 : ℂ)) = e p := by
        funext i
        exact add_zero (e p i)
      simpa only [hzero] using hcont.tendsto (0 : ℂ)
    exact hT (e.open_target.mem_nhds (e.map_source hp))
  filter_upwards [ht] with z hz
  rw [hf _ (e.symm.map_source hz), e.right_inv hz]
  simp

/-- An actual regular representative of the native curve parameter evaluates
to the scalar coordinate on the centered native inverse chart near zero.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8; Mathlib,
OpenPartialHomeomorph.right_inv. -/
theorem s2e_native_curve_parameter_centered_chart
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] (p : ComplexPoint X) :
    ∃ (U : X.left.Opens) (hp : p.underlying ∈ U) (s : Γ(X.left, U)),
      X.left.presheaf.germ U p.underlying hp s = s2e_native_curve_parameter X p ∧
      (fun z : ℂ => Point.evaluate U s
        ((ComplexPoint.localChart X 1 p).symm
          (ComplexPoint.localChart X 1 p p + fun _ : Fin 1 => z))) =ᶠ[nhds 0] (fun z => z) := by
  obtain ⟨U, hp, s, hs, hf⟩ := s2e_native_curve_parameter_regular_chart X p
  refine ⟨U, hp, s, hs, ?_⟩
  exact s2e_centered_chart_evaluation (ComplexPoint.localChart X 1 p) p
    (ComplexPoint.mem_localChart_source X 1 p) (Point.evaluate U s) hf

end HodgeLean.Foundations.Program
