import HodgeLean.Foundations.Program.SchoenCyclePowerParameterEvaluation
import HodgeLean.Foundations.Program.SchoenCycleAffinePolynomialGerms
import HodgeLean.Foundations.Program.SchoenCycleGermEvaluation
import HodgeLean.Foundations.Program.SchoenCycleSectionPolynomialEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial Filter Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Native curve-power parameter polynomials have simultaneous actual affine representatives with their exact centered native chart evaluations near the original tuple.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.1, II.2 and II.8. -/
theorem s2e_curve_power_polynomial_regular_evaluation
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n)) :
    let X := g3_power Z n
    let R := X.left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ (U : X.left.Opens) (_ : IsAffineOpen U) (hxU : x.underlying ∈ U),
      ∃ G : MvPolynomial (Fin n) ℂ →+* Γ(X.left, U),
        (X.left.presheaf.germ U x.underlying hxU).hom.comp G = (aeval (s2e_curvePowerParameter Z n x)).toRingHom ∧
        (∀ᶠ q in 𝓝 x, ∀ P : MvPolynomial (Fin n) ℂ,
          Point.evaluate U (G P) q = aeval (fun i =>
            ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x) (Point.map (g3_proj Z n i) q) 0 -
              ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x) (Point.map (g3_proj Z n i) x) 0) P) := by
  dsimp only
  let X := g3_power Z n
  letI : Algebra ℂ (X.left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  obtain ⟨U, hU, hUT, hxU, G, hG⟩ := s2e_affine_polynomial_germ_representatives
    X x.underlying ⊤ trivial (s2e_curvePowerParameter Z n x)
  letI := s2e_step1_sectionAlgebra X U
  have hvar (i : Fin n) : ∀ᶠ q in 𝓝 x,
      Point.evaluate U (G (MvPolynomial.X i)) q =
        ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x) (Point.map (g3_proj Z n i) q) 0 -
          ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x) (Point.map (g3_proj Z n i) x) 0 := by
    obtain ⟨V, hxV, s, hs, hev⟩ := s2e_curve_power_parameter_regular_evaluation Z n x i
    have hg : X.left.presheaf.germ U x.underlying hxU (G (MvPolynomial.X i)) =
        X.left.presheaf.germ V x.underlying hxV s := by
      have hh := congrArg (fun F : MvPolynomial (Fin n) ℂ →ₐ[ℂ] X.left.presheaf.stalk x.underlying =>
        F (MvPolynomial.X i)) hG
      simp only [AlgHom.comp_apply, aeval_X] at hh
      change X.left.presheaf.germ U x.underlying hxU (G (MvPolynomial.X i)) =
        s2e_curvePowerParameter Z n x i at hh
      exact hh.trans hs.symm
    exact (s2e_equal_germs_eventually_evaluate X x U V hxU hxV _ _ hg).trans hev
  refine ⟨U, hU, hxU, G.toRingHom, congrArg AlgHom.toRingHom hG, ?_⟩
  filter_upwards [eventually_all.mpr hvar, (Point.isOpen_overOpen (X := X) U).mem_nhds hxU]
    with q hq hqU
  intro P
  change Point.evaluate U (G P) q = _
  rw [s2e_section_polynomial_evaluate X U (Fin n) G q hqU P]
  exact congrArg (fun r : Fin n → ℂ => aeval r P) (funext hq)

#print axioms s2e_curve_power_polynomial_regular_evaluation
end HodgeLean.Foundations.Program
