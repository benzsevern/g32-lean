import HodgeLean.Foundations.Program.SchoenCycleEtaleMapAnalyticChart
import HodgeLean.Foundations.Program.SchoenCycleAnalyticChartTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- A supplied centered etale coordinate chart descends through an actual etale morphism, retaining its exact coordinate evaluations near the marked point and both analytic directions on the original target.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; EGA IV, 17.11.1. -/
theorem s2e_etale_analytic_chart_descent
    (X Y : Over (Spec ↧ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
    (f : X ⟶ Y) [Etale f.left] (x : ComplexPoint X)
    (D : LocalEtaleCoordinates X n x.underlying)
    (hzero : ∀ i, Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) x = 0) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint Y) (Fin n → ℂ),
      Point.map f x ∈ e.source ∧ e (Point.map f x) = 0 ∧
      AnalyticAt ℂ (fun z => e ((ComplexPoint.localChart Y n (Point.map f x)).symm
        (ComplexPoint.localChart Y n (Point.map f x) (Point.map f x) + z))) 0 ∧
      AnalyticAt ℂ (fun z => ComplexPoint.localChart Y n (Point.map f x) (e.symm z)) 0 ∧
      (∀ᶠ q in 𝓝 x, ∀ i, e (Point.map f q) i =
        Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) q) := by
  obtain ⟨e₀, hx₀, hev₀, hf₀, hi₀⟩ := s2e_etale_map_analytic_chart X Y n f x
  obtain ⟨e₁, hx₁, hev₁, hf₁, hi₁⟩ := s2e_etale_analytic_coordinate_chart X n x D
  let C := ComplexPoint.localChart X n x
  let B := ComplexPoint.localChart Y n (Point.map f x)
  have hxC : x ∈ C.source := ComplexPoint.mem_localChart_source X n x
  have hyB : Point.map f x ∈ B.source := ComplexPoint.mem_localChart_source Y n (Point.map f x)
  have hcoord : e₀ x = B (Point.map f x) := hev₀.self_of_nhds
  have hz : e₁ x = 0 := by
    funext i
    exact (hev₁ x hx₁ i).trans (hzero i)
  have hf := s2e_analytic_chart_transition n C e₀ e₁ x hxC hx₀ hf₁ hi₀
  have hi := s2e_analytic_chart_transition n C e₁ e₀ x hxC hx₁ hf₀ hi₁
  obtain ⟨e, he, hez, hef, hei, heval⟩ :=
    s2e_analytic_chart_transport n B e₀ e₁ x (Point.map f x) hx₀ hx₁ hyB hcoord hz hf hi
  refine ⟨e, he, hez, hef, hei, ?_⟩
  filter_upwards [hev₀, e₀.open_source.mem_nhds hx₀, e₁.open_source.mem_nhds hx₁]
    with q hq hq₀ hq₁
  intro i
  rw [heval, ← hq, e₀.left_inv hq₀]
  exact hev₁ q hq₁ i

#print axioms s2e_etale_analytic_chart_descent
end HodgeLean.Foundations.Program
