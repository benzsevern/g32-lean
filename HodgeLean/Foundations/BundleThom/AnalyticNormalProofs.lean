import HodgeLean.Foundations.BundleThom.AnalyticNormalDefs
import HodgeLean.Foundations.BundleThom.NormalAtlasConstructionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers

/-! # Analytification of the normal bundle

The topologies are fixed by local algebraic evaluation, before the bundle
existence obligation is stated. No characteristic class belongs to the data.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

variable {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)

private local instance (x : ComplexPoint Q) : TopologicalSpace (i1_normalFibre j x) :=
  i1_normalFibreTopology j x
private local instance : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Bundle atlas on the actual dual fibres with their algebraic evaluation topology.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8; Bott–Tu, §6. -/
structure I1AnalyticNormal where
  /-- Local product charts for the fixed total topology. -/
  fiberBundle : FiberBundle (Fin k → ℂ) (i1_normalFibre j)
  /-- The same charts have complex linear transitions. -/
  vectorBundle : letI := fiberBundle; VectorBundle ℂ (Fin k → ℂ) (i1_normalFibre j)

/-- Analytification of the dual of the smooth immersion's conormal sheaf.
Source: Hartshorne, Algebraic Geometry, II.8; Bott–Tu, §6, complex bundles. -/
theorem i1_analyticNormal_exists_aux
    (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [IsClosedImmersion j] [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV] : Nonempty (I1AnalyticNormal j k) := by
  let frames := i1_smoothConormalFrameAt j k sV hj
  exact ⟨⟨i1_normalFiberBundle j k frames, i1_normalVectorBundle j k frames⟩⟩

example (N : I1AnalyticNormal j k) :
    FiberBundle (Fin k → ℂ) (i1_normalFibre j) := N.fiberBundle

end HodgeLean.Foundations.BundleThom
