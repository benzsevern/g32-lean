import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialParameterJet
import HodgeLean.Foundations.Program.SchoenCycleU1SectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver

/-! # Actual complex points of the polynomial parameter scheme -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The actual complex point of the affine parameter scheme at a scalar value.
Source: Hartshorne, Algebraic Geometry, II.2, polynomial evaluation and Spec. -/
def s2e_u1_polynomialParameterPoint (t : ℂ) :
    ComplexPoint (s2e_u1_specOver (Polynomial ℂ)) := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom)) ?_
  change Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))) = 𝟙 _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)) ≫
      CommRingCat.ofHom (Polynomial.aeval t).toRingHom = 𝟙 (CommRingCat.of ℂ) := by
    ext a
    exact (Polynomial.aeval t).commutes a
  rw [he, Spec.map_id]

/-- Global regular sections on the parameter scheme evaluate as the actual
polynomials given by the canonical global-section ring isomorphism.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib, `Scheme.ΓSpecIso_naturality`. -/
theorem s2e_u1_polynomialParameterPoint_evaluate_top
    (a : Γ((s2e_u1_specOver (Polynomial ℂ)).left, ⊤)) (t : ℂ) :
    Point.evaluate ⊤ a (s2e_u1_polynomialParameterPoint t) =
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom.hom a).eval t := by
  rw [← s2e_u1_pointEvaluation_eq_evaluate (s2e_u1_specOver (Polynomial ℂ)) ⊤
    (s2e_u1_polynomialParameterPoint t) (by trivial)]
  change ((Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom a = _
  rw [Scheme.ΓSpecIso_naturality]
  exact congrFun (Polynomial.coe_aeval_eq_eval t) _

/-- Global regular sections of the actual parameter scheme have analytic
scalar evaluations at the parameter origin.
Source: Mathlib, `AnalyticAt.aeval_polynomial`; Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_u1_polynomialParameterPoint_top_analytic
    (a : Γ((s2e_u1_specOver (Polynomial ℂ)).left, ⊤)) :
    AnalyticAt ℂ (fun t => Point.evaluate ⊤ a (s2e_u1_polynomialParameterPoint t)) 0 := by
  let p := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom.hom a
  have ha := (s2e_u1_polynomialFunction p).property
  change AnalyticAt ℂ (fun t => p.eval t) 0 at ha
  have he : (fun t => Point.evaluate ⊤ a (s2e_u1_polynomialParameterPoint t)) =
      (fun t => p.eval t) := by
    funext t
    exact s2e_u1_polynomialParameterPoint_evaluate_top a t
  rw [he]
  exact ha

end HodgeLean.Foundations.Program
