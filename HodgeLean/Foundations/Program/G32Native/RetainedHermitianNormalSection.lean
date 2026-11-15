import HodgeLean.Foundations.Program.G32Native.RetainedMetricNormalVector
import HodgeLean.Foundations.Program.G32Native.HermitianMetricNormalLinearity

/-! # A complex linear metric normal section on the original fibre

The supplied chart metric and retained affine differential fix this section.
Its quotient is the original dual-conormal fibre, without a new presentation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- The metric representatives of the original normal functionals form an
injective complex linear section with the actual evaluation and kernel equations.
Source: Hartshorne, Algebraic Geometry, II.8, dual conormal sequence;
Hermitian orthogonal complements and `hermitianMetricRepresentativeLinearMap`.
HC no distance; AV milestone no distance. -/
theorem retained_hermitian_normal_section
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (g : ChartHermitianMetric (ComplexPoint X) d)
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (hD : Function.Injective (retainedAffineConormalDifferential X Y j d A hA x hx z hz)) :
    ∃ L : i1_normalFibre j.left x →ₗ[ℂ] (Fin d → ℂ), Function.Injective L ∧
      (∀ n a, retainedAffineConormalDifferential X Y j d A hA x hx z hz a (L n) = n a) ∧
      (∀ n w, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j x)) (L n) w = 0) := by
  let D := retainedAffineConormalDifferential X Y j d A hA x hx z hz
  let T : (Fin d → ℂ) →ₗ[ℂ] i1_normalFibre j.left x :=
    ((ContinuousLinearMap.coeLM ℂ).comp D).flip
  have hT : Function.Surjective T := by
    intro n
    obtain ⟨v, hv⟩ := injective_covector_evaluation_surjective D hD n
    exact ⟨v, LinearMap.ext hv⟩
  let G : LinearMap.BilinForm ℝ (Fin d → ℂ) :=
    (ContinuousLinearMap.coeLM ℝ).comp
      (g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j x))).toLinearMap
  have hp := (chartAt (Fin d → ℂ) z).map_source hz
  let L := hermitianMetricRepresentativeLinearMap G (g.symmetric z _ hp)
    (g.positive z _ hp) (g.hermitian z _ hp) T hT
  have hL (n : i1_normalFibre j.left x) : T (L n) = n ∧
      ∀ w, T w = 0 → G (L n) w = 0 :=
    positiveMetricRepresentative_spec G (g.symmetric z _ hp) (g.positive z _ hp)
      (T.restrictScalars ℝ) hT n
  refine ⟨L, ?_, ?_, ?_⟩
  · intro n m hnm
    calc n = T (L n) := (hL n).1.symm
         _ = T (L m) := congrArg T hnm
         _ = m := (hL m).1
  · intro n a
    exact LinearMap.congr_fun (hL n).1 a
  · intro n w hw
    exact (hL n).2 w (LinearMap.ext hw)

#print axioms retained_hermitian_normal_section

end HodgeLean.Foundations.TubularEuler
