import HodgeLean.Foundations.Program.G32Native.CanonicalAbelOverlapComparison
import HodgeLean.Foundations.Program.G32Native.CanonicalConormalLocalEquation
import HodgeLean.Foundations.Program.G32Native.CanonicalPeriodDerivativeUniqueness
import HodgeLean.Foundations.Program.G32Native.ConormalEvaluationContinuity
import HodgeLean.Foundations.Program.G32Native.CoefficientInverseContinuity
import HodgeLean.Foundations.Program.G32Native.CoherentPeriodForward

/-! # Evaluation topology comparison for coherent local period lifts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle Filter Topology
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Local analytic period lifts with the same quotient germs induce the dual
locally free module topology in their coefficient coordinates.
Source: Bourbaki, General Topology, I §2 (initial topologies);
Lee, Introduction to Smooth Manifolds, 2nd ed., ch. 10 (vector bundle charts).
Proof plan: use a local conormal frame, differentiate quotient-germ equality
on overlaps, and identify the two evaluation topologies in that frame.
The local functions are arbitrary; no Abel sum or base point is required. -/
theorem coherent_period_lifts_evaluation_topology_aux (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (hanalytic : ∀ x : ComplexPoint G.Q, AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hoverlap : ∀ x : ComplexPoint G.Q, ∃ U : Set (ComplexPoint G.W),
      IsOpen U ∧ Point.map G.ι x ∈ U ∧
      ∀ y : ComplexPoint G.Q, Point.map G.ι y ∈ U →
        (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
          =ᶠ[𝓝 (Point.map G.ι y)]
        (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w)))
    (hgeom : ∀ x : ComplexPoint G.Q,
      LinearMap.ker (canonicalAbelDifferential G F x) = LinearMap.range
        (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
          (localChart G.Q G.k x x)).toLinearMap ∧
      ∀ v, canonicalAbelDifferential G F x v (g32n_homogeneousLine G.k G.eQ x).rep = 0) :
    let E := fun x => (canonicalConormalFibreEquiv G x).trans
        (g32n_normalCoefficientEquiv G.W G.Q G.ι G.k G.eQ x
          (canonicalAbelDifferential G F x) (hgeom x).1.le (hgeom x).2)
    @Continuous
        (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
        (TotalSpace (Fin G.k → ℂ)
          (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
        (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k) (coefficientTotalTopology G)
        (fun z => ⟨z.proj, E z.proj z.2⟩) ∧
    @Continuous
        (TotalSpace (Fin G.k → ℂ)
          (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
        (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
        (coefficientTotalTopology G) (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k)
        (fun z => ⟨z.proj, (E z.proj).symm z.2⟩) := by
  let E := fun x => (canonicalConormalFibreEquiv G x).trans
      (g32n_normalCoefficientEquiv G.W G.Q G.ι G.k G.eQ x
        (canonicalAbelDifferential G F x) (hgeom x).1.le (hgeom x).2)
  have hforward :
    @Continuous
        (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
        (TotalSpace (Fin G.k → ℂ)
          (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
        (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k) (coefficientTotalTopology G)
        (fun z => ⟨z.proj, E z.proj z.2⟩) := by
    exact coherentPeriodLifts_forward_continuous G F hanalytic hoverlap hgeom
  exact ⟨hforward, canonicalCoefficientEquiv_inverse_continuous G E hforward⟩

#print axioms coherent_period_lifts_evaluation_topology_aux
end HodgeLean.Foundations.Program.G32Native
