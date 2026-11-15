import HodgeLean.Foundations.BundleThom.AnalyticNormalProofs
import HodgeLean.Foundations.BundleThom.Thom

/-! # Euler operation for the analytic dual conormal

The normal bundle uses the fixed local-section topology. Its Euler class uses
its own zero section and does not refer to an immersion-supported class.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

variable {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)
private local instance (x : ComplexPoint Q) : TopologicalSpace (i1_normalFibre j x) :=
  i1_normalFibreTopology j x
private local instance : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

variable (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
variable [IsClosedImmersion j] [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) sV]

/-- The analytic complex normal atlas selected for the actual conormal dual.
Source: Hartshorne, Algebraic Geometry, II.8; Bott–Tu, §6. -/
def i1_analyticNormal : I1AnalyticNormal j k :=
  Classical.choice (i1_analyticNormal_exists_aux j k sV hj)

/-- Euler of the actual analytic normal, by its own zero-section pullback.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Euler class. -/
def i1_normalBundleEuler [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)] :
    Cohomology ℚ (TopCat.of (ComplexPoint Q)) (2 * k) := by
  let N := i1_analyticNormal j k sV hj
  letI := N.fiberBundle
  letI := N.vectorBundle
  exact i1_bundleEuler k (i1_normalFibre j)

example : FiberBundle (Fin k → ℂ) (i1_normalFibre j) :=
  (i1_analyticNormal j k sV hj).fiberBundle

example [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)] :
    Cohomology ℚ (TopCat.of (ComplexPoint Q)) (2 * k) :=
  i1_normalBundleEuler j k sV hj

end HodgeLean.Foundations.BundleThom
