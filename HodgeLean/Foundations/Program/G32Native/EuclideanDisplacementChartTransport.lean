import HodgeLean.Foundations.Program.G32Native.ComplexRealManifoldRegularity
import HodgeLean.Foundations.Program.G32Native.PartialChartDifferentialTransport
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Chart independence of differentiated Euclidean displacement -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- Differentiating the specified Euclidean map in two ambient charts uses
exactly the real coordinate-change derivative that transports metric normals.
Source: `partialChart_differential_transport`,
`ComplexPoint.analyticAt_localChart_transition`, and
`contMDiffOn_chart_symm`. -/
theorem euclidean_displacement_chart_derivative_transport
    (X : Over (Spec ↧ℂ)) (d n : ℕ) [SmoothOfRelativeDimension d X.hom]
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (z z' p : ComplexPoint X)
    (hp : p ∈ (chartAt (Fin d → ℂ) z).source)
    (hp' : p ∈ (chartAt (Fin d → ℂ) z').source) :
    fderiv ℝ (fun c => emb ((chartAt (Fin d → ℂ) z).symm c))
      ((chartAt (Fin d → ℂ) z) p) =
    (fderiv ℝ (fun c => emb ((chartAt (Fin d → ℂ) z').symm c))
      ((chartAt (Fin d → ℂ) z') p)).comp
      (fderiv ℝ (fun c => (chartAt (Fin d → ℂ) z')
        ((chartAt (Fin d → ℂ) z).symm c)) ((chartAt (Fin d → ℂ) z) p)) := by
  have hcoords (a : ComplexPoint X) (ha : p ∈ (chartAt (Fin d → ℂ) a).source) :
      DifferentiableAt ℝ (fun c => emb ((chartAt (Fin d → ℂ) a).symm c))
        ((chartAt (Fin d → ℂ) a) p) := by
    have hchart : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
        (chartAt (Fin d → ℂ) a).symm ((chartAt (Fin d → ℂ) a) p) :=
      (contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := a)).contMDiffAt
        ((chartAt (Fin d → ℂ) a).open_target.mem_nhds
          ((chartAt (Fin d → ℂ) a).map_source ha))
    exact (hemb.contMDiffAt.comp _ (contMDiffAt_real_of_complex hchart)).contDiffAt.differentiableAt
      (by simp)
  have hsource : (chartAt (Fin d → ℂ) z) p ∈
      ((chartAt (Fin d → ℂ) z).symm.trans (chartAt (Fin d → ℂ) z')).source := by
    refine ⟨(chartAt (Fin d → ℂ) z).map_source hp, ?_⟩
    change (chartAt (Fin d → ℂ) z).symm ((chartAt (Fin d → ℂ) z) p) ∈
      (chartAt (Fin d → ℂ) z').source
    rwa [(chartAt (Fin d → ℂ) z).left_inv hp]
  have htrans := (ComplexPoint.analyticAt_localChart_transition X d z z' hsource).differentiableAt.restrictScalars ℝ
  exact partialChart_differential_transport _ _ p hp hp' emb _ _ _
    (hcoords z hp).hasFDerivAt (hcoords z' hp').hasFDerivAt htrans.hasFDerivAt

#print axioms euclidean_displacement_chart_derivative_transport
end HodgeLean.Foundations.TubularEuler
