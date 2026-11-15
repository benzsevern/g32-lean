import HodgeLean.Foundations.Program.SchoenCycleEtalePullbackCoordinates
import HodgeLean.Foundations.Program.SchoenCycleAmbientCoordinateEvaluation
import HodgeLean.Foundations.Program.SchoenCycleEtaleAnalyticCoordinateChart

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- An actual etale morphism is represented near the marked point by an analytic source chart equal to the native target coordinates, with analytic inverse.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; EGA IV, 17.11.1. -/
theorem s2e_etale_map_analytic_chart
    (X Y : Over (Spec ↧ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
    (f : X ⟶ Y) [Etale f.left] (x : ComplexPoint X) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X) (Fin n → ℂ),
      x ∈ e.source ∧
      (∀ᶠ q in 𝓝 x, e q = ComplexPoint.localChart Y n (Point.map f x) (Point.map f q)) ∧
      AnalyticAt ℂ (fun v => e ((ComplexPoint.localChart X n x).symm v))
        (ComplexPoint.localChart X n x x) ∧
      AnalyticAt ℂ (fun v => ComplexPoint.localChart X n x (e.symm v)) (e x) := by
  let D := ComplexPoint.localEtaleCoordinates Y n (Point.map f x)
  obtain ⟨E, hE⟩ := s2e_etale_pullback_coordinates X Y n f x D
  obtain ⟨e, he, hev, hf, hi⟩ := s2e_etale_analytic_coordinate_chart X n x E
  refine ⟨e, he, ?_, hf, hi⟩
  let C := ComplexPoint.localChart Y n (Point.map f x)
  have hC : ∀ᶠ q in 𝓝 x, Point.map f q ∈ C.source :=
    (Point.continuous_map f).continuousAt
      (C.open_source.mem_nhds (ComplexPoint.mem_localChart_source Y n (Point.map f x)))
  filter_upwards [e.open_source.mem_nhds he,
    (Point.isOpen_overOpen (X := X) E.neighborhood).mem_nhds E.mem, hC] with q hq hqE hqC
  funext i
  calc
    e q i = Point.evaluate E.ambientCoordinateOpen (E.ambientCoordinateSection i) q := hev q hq i
    _ = Point.evaluate E.neighborhood (E.coordinateAlgHom (MvPolynomial.X i)) q :=
      s2e_ambient_coordinate_section_evaluate X n x E q hqE i
    _ = Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i)) (Point.map f q) :=
      hE q hqE i
    _ = Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) (Point.map f q) :=
      (s2e_ambient_coordinate_section_evaluate Y n (Point.map f x) D (Point.map f q)
        (ComplexPoint.mem_coordinateNeighborhood_of_mem_localChart_source Y n (Point.map f x)
          (Point.map f q) hqC) i).symm
    _ = C (Point.map f q) i :=
      (ComplexPoint.localChart_apply_component_eq_evaluate Y n (Point.map f x) (Point.map f q) hqC i).symm

#print axioms s2e_etale_map_analytic_chart
end HodgeLean.Foundations.Program
