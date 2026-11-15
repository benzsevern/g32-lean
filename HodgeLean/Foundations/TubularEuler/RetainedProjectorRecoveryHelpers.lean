import HodgeLean.Foundations.TubularEuler.ProjectorPointRecoveryHelpers
import HodgeLean.Foundations.TubularEuler.ImmersionSectionRecoveryHelpers
import HodgeLean.Foundations.TubularEuler.QuasiProjectiveChartFormulaHelpers
import HodgeLean.Foundations.TubularEuler.LocalLeftInverseDerivativeHelpers

/-! # Recovery of retained source coordinates from the literal projector

Lifted regular coordinate sections give a real analytic local left inverse.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology Filter
open AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
open scoped ContDiff
namespace HodgeLean.Foundations.TubularEuler

theorem retained_projector_local_leftInverse
    (X : Over (Spec ↧ℂ)) (d N : ℕ) [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (z : ComplexPoint X) (a : Fin d → ℂ)
    (ha : a ∈ (localChart X d z).target) :
    ∃ R : (Fin (N+1) → Fin (N+1) → ℂ) → (Fin d → ℂ),
      ContDiffAt ℝ ω R (quasiProjectiveProjector e ((localChart X d z).symm a)) ∧
      (fun b => R (quasiProjectiveProjector e ((localChart X d z).symm b))) =ᶠ[𝓝 a] id := by
  classical
  let C := localChart X d z
  let D := localEtaleCoordinates X d z
  let q : ComplexPoint X := C.symm a
  have hqC : q ∈ C.source := C.map_target ha
  have hqV : q ∈ Point.overOpen D.ambientCoordinateOpen := by
    have hmem := mem_coordinateNeighborhood_of_mem_localChart_source X d z q hqC
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  obtain ⟨U, hqU, r, hr⟩ := immersion_local_evaluation_lifts X
    (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))) e
    D.ambientCoordinateOpen D.ambientCoordinateSection q hqV
  obtain ⟨⟨v, hv⟩, hvq⟩ := surjective_vectorToComplexPoint (Point.map e q)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hqi : Point.map e q ∈ Point.overOpen (s2e_standardProjectiveAffineOpen i).1 := by
    rw [← hvq]
    exact (s2e_standardProjectiveAffineOpen_mem_iff v hv i).mpr hi
  let R : (Fin (N+1) → Fin (N+1) → ℂ) → Fin d → ℂ :=
    fun M j => Point.evaluate U (r j) (projectorRecoveredPoint i M)
  have hrec := projectorRecoveredPoint_projective N (Point.map e q) i hqi
  have hdiag := projectiveProjector_diagonal_ne_zero N (Point.map e q) i hqi
  refine ⟨R, ?_, ?_⟩
  · apply contDiffAt_pi.mpr
    intro j
    apply projector_recovered_section_contDiffAt i _ hdiag U (r j)
    change projectorRecoveredPoint i (projectiveHermitianProjector N (Point.map e q)) ∈
      Point.overOpen U
    rw [hrec]
    exact hqU
  · have hpcont : ContinuousAt (fun b => Point.map e (C.symm b)) a :=
      (Point.continuous_map e).continuousAt.comp (C.continuousAt_symm ha)
    have hnU : ∀ᶠ b in 𝓝 a, Point.map e (C.symm b) ∈ Point.overOpen U :=
      hpcont ((Point.isOpen_overOpen U).mem_nhds hqU)
    have hni : ∀ᶠ b in 𝓝 a, Point.map e (C.symm b) ∈
        Point.overOpen (s2e_standardProjectiveAffineOpen i).1 :=
      hpcont ((Point.isOpen_overOpen _).mem_nhds hqi)
    filter_upwards [C.open_target.mem_nhds ha, hnU, hni] with b hb hbU hbi
    ext j
    change Point.evaluate U (r j)
      (projectorRecoveredPoint i (projectiveHermitianProjector N (Point.map e (C.symm b)))) = b j
    rw [projectorRecoveredPoint_projective N _ i hbi, hr _ hbU j]
    rw [← localChart_apply_component_eq_evaluate X d z (C.symm b) (C.map_target hb) j]
    exact congrFun (C.right_inv hb) j

theorem retained_projector_derivative_injective
    (X : Over (Spec ↧ℂ)) (d N : ℕ) [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (z : ComplexPoint X) (a : Fin d → ℂ)
    (ha : a ∈ (localChart X d z).target) :
    Function.Injective (fderiv ℝ
      (fun b => quasiProjectiveProjector e ((localChart X d z).symm b)) a) := by
  obtain ⟨R, hR, he⟩ := retained_projector_local_leftInverse X d N e z a ha
  obtain ⟨c, L, hc, hformula⟩ := retained_projector_ratio_chart_formula X d N e z a ha
  have hp : ContDiffAt ℝ ω
      (fun b => quasiProjectiveProjector e ((localChart X d z).symm b)) a :=
    (L.contDiff.contDiffAt.comp a
      ((affineHermitianProjector_contDiff N).contDiffAt.comp a hc)).congr_of_eventuallyEq hformula
  exact localLeftInverse_fderiv_injective _ R a
    (hp.differentiableAt (by simp)) (hR.differentiableAt (by simp)) he

end HodgeLean.Foundations.TubularEuler
