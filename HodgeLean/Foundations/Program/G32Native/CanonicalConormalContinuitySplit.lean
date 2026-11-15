import HodgeLean.Foundations.Program.G32Native.CoherentPeriodEvaluationTopology

/-! # Derivative-normalized conormal comparison through the continuity split -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native.ContinuitySplit

/-- The original conormal comparison assembled from local lift overlap and
locally free evaluation topology comparison.
Source: Voisin, Hodge Theory and Complex Algebraic Geometry I, 7.1. -/
theorem canonical_conormal_comparison_aux (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (hF : ∀ x : ComplexPoint G.Q,
      AnalyticAt ℂ (F x)
        (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)) ∧
      ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
        Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
        canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
          ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i))
    (hgeom : ∀ x : ComplexPoint G.Q,
      LinearMap.ker (canonicalAbelDifferential G F x) = LinearMap.range
        (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
          (localChart G.Q G.k x x)).toLinearMap ∧
      ∀ v, canonicalAbelDifferential G F x v (g32n_homogeneousLine G.k G.eQ x).rep = 0) :
    ∃ e : ∀ x : ComplexPoint G.Q,
        canonicalNormalFibre G x ≃ₗ[ℂ] canonicalNormalComplement G x,
      (∀ (x : ComplexPoint G.Q) (ν : canonicalNormalFibre G x)
        (U : G.W.left.Opens)
        (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
          (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left))
        (hx : Point.map G.ι x ∈ Point.overOpen U),
        ν (conormalLocalClass G.ι U s x hx) =
          conormalLocalDerivative G.ι (G.k + G.k) U s x (e x ν).val) ∧
      let E := fun x => (e x).trans
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
  refine ⟨canonicalConormalFibreEquiv G, ?_, ?_⟩
  · exact canonicalConormalFibreEquiv_localEquation G
  · exact coherent_period_lifts_evaluation_topology_aux G F (fun x => (hF x).1)
      (canonicalAbelLiftOverlap G p F (fun x => (hF x).2)) hgeom

#print axioms canonical_conormal_comparison_aux
end HodgeLean.Foundations.Program.G32Native.ContinuitySplit
