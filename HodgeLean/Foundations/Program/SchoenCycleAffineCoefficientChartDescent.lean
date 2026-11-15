import HodgeLean.Foundations.Program.SchoenCycleEtaleAnalyticChartDescent
import HodgeLean.Foundations.Program.SchoenCycleEtaleSectionTopCoordinates
import HodgeLean.Foundations.Program.SchoenCycleEtaleSmoothSource

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Exact centered etale sections on an actual affine coefficient open descend along an etale comparison to the original smooth base, with analytic inverse and exact evaluations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; EGA IV, 17.11.1. -/
theorem s2e_affine_coefficient_chart_etale_descent
    (S B T : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (V : S.left.Opens) (hV : IsAffineOpen V) :
    letI := s2e_step1_sectionAlgebra S V
    ∀ (G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(S.left, V)) (hG : G.toRingHom.Etale)
      (a : T ⟶ ComplexPoint.openScheme S V) (f : T ⟶ B),
      Etale a.left → Etale f.left → ∀ x : ComplexPoint T,
      (∀ i, Point.evaluate V (G (MvPolynomial.X i))
        (Point.map (a ≫ ComplexPoint.openInclusion S V) x) = 0) →
      ∃ e : OpenPartialHomeomorph (ComplexPoint B) (Fin n → ℂ),
        Point.map f x ∈ e.source ∧ e (Point.map f x) = 0 ∧
        AnalyticAt ℂ (fun z => e ((ComplexPoint.localChart B n (Point.map f x)).symm
          (ComplexPoint.localChart B n (Point.map f x) (Point.map f x) + z))) 0 ∧
        AnalyticAt ℂ (fun z => ComplexPoint.localChart B n (Point.map f x) (e.symm z)) 0 ∧
        (∀ᶠ q in 𝓝 x, ∀ i, e (Point.map f q) i =
          Point.evaluate V (G (MvPolynomial.X i))
            (Point.map (a ≫ ComplexPoint.openInclusion S V) q)) := by
  letI := s2e_step1_sectionAlgebra S V
  intro G hG a f ha hf x hz
  letI : Etale a.left := ha
  letI : Etale f.left := hf
  let Y := ComplexPoint.openScheme S V
  letI : SmoothOfRelativeDimension n Y.hom := s2e_etale_sections_smooth_open S V hV n G hG
  letI : SmoothOfRelativeDimension n T.hom := s2e_etale_smooth_source T B n f
  let D := s2e_etale_sections_top_coordinates S V hV n G hG (Point.map a x)
  obtain ⟨E, hE⟩ := s2e_etale_pullback_coordinates T Y n a x D
  have hv (q : ComplexPoint T) (hq : q ∈ Point.overOpen E.neighborhood) (i : Fin n) :
      Point.evaluate E.ambientCoordinateOpen (E.ambientCoordinateSection i) q =
        Point.evaluate V (G (MvPolynomial.X i))
          (Point.map (a ≫ ComplexPoint.openInclusion S V) q) := by
    rw [s2e_ambient_coordinate_section_evaluate T n x E q hq i, hE q hq i]
    exact s2e_complex_open_top_section_evaluate S V _ (Point.map a q)
  obtain ⟨e, he, hez, hef, hei, hev⟩ := s2e_etale_analytic_chart_descent T B n f x E
    (fun i => (hv x E.mem i).trans (hz i))
  refine ⟨e, he, hez, hef, hei, ?_⟩
  filter_upwards [hev, (Point.isOpen_overOpen (X := T) E.neighborhood).mem_nhds E.mem]
    with q hq hqE
  intro i
  exact (hq i).trans (hv q hqE i)

#print axioms s2e_affine_coefficient_chart_etale_descent
end HodgeLean.Foundations.Program
