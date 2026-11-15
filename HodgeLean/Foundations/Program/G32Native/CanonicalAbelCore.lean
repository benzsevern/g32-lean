import HodgeLean.Foundations.Program.G32Native.CanonicalConormalContinuitySplit
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelAnalyticLifts
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelTransposeKernel
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelTangentVanishing
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelKernelLinearAlgebra


/-! # Three geometric steps for the retained canonical normal model -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Local holomorphic lifts of the actual symmetric Abel sum, also at repeated divisors.
Source: Griffiths–Harris, Principles of Algebraic Geometry, ch. 2.7;
ACGH, Geometry of Algebraic Curves I, IV.1–IV.3, Abel mapping in symmetric coordinates. -/
theorem canonical_abel_lifts_aux (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z) :
    ∃ (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ)),
      ∀ x : ComplexPoint G.Q,
      AnalyticAt ℂ (F x)
        (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)) ∧
      ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
        Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
        canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
          ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i) := by
  exact canonical_abel_analytic_lifts G p

/-- The Abel differential at a canonical divisor has precisely the immersion tangent kernel
and its image annihilates that divisor's retained homogeneous form.
Source: ACGH, Geometry of Algebraic Curves I, IV.1–IV.3, differential of the Abel map;
Griffiths–Harris, ch. 2.7 and 3.4, canonical linear systems and duality. -/
theorem canonical_abel_equations_aux (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (hF : ∀ x : ComplexPoint G.Q,
      AnalyticAt ℂ (F x)
        (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)) ∧
      ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
        Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
        canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
          ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i)) :
    ∀ x : ComplexPoint G.Q,
      LinearMap.ker (canonicalAbelDifferential G F x) = LinearMap.range
        (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
          (localChart G.Q G.k x x)).toLinearMap ∧
      ∀ v, canonicalAbelDifferential G F x v (g32n_homogeneousLine G.k G.eQ x).rep = 0 := by
  intro x
  let D := fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
    (localChart G.Q G.k x x)
  have hleft : Function.LeftInverse
      (closedImmersionDerivativeProjection G.W G.Q G.ι G.k (G.k + G.k) x) D := by
    intro v
    exact congrArg (fun L : (Fin G.k → ℂ) →L[ℂ] (Fin G.k → ℂ) => L v)
      (closedImmersionDerivativeProjection_leftInverse G.W G.Q G.ι G.k (G.k + G.k) x)
  exact linear_kernel_eq_range_of_transpose_line G.k (canonicalAbelDifferential G F x)
    D.toLinearMap hleft.injective
    (canonical_abel_tangent_vanishes G p F x (hF x).1 (hF x).2)
    (g32n_homogeneousLine G.k G.eQ x)
    (canonical_abel_transpose_kernel_aux G p F x (hF x).1 (hF x).2)

/-- Algebraic–analytic dual-conormal comparison retains the derivative-induced fibre maps
and makes both coefficient total-space maps continuous in the local-section topology.
Source: Voisin, Hodge Theory and Complex Algebraic Geometry I, 7.1;
Griffiths–Harris, ch. 3.4, normal-conormal sequence and analytic comparison. -/
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
  exact ContinuitySplit.canonical_conormal_comparison_aux G p F hF hgeom

#print axioms canonical_abel_lifts_aux
#print axioms canonical_abel_equations_aux
#print axioms canonical_conormal_comparison_aux
end HodgeLean.Foundations.Program.G32Native
