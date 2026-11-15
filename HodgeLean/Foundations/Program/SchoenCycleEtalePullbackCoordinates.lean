import HodgeLean.Foundations.Program.SchoenCycleComplexSectionPullback
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Etale pullback gives actual etale coordinates with exactly the supplied target coordinate evaluations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; EGA IV, 17.11.1. -/
theorem s2e_etale_pullback_coordinates
    (X Y : Over (Spec ↧ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
    (f : X ⟶ Y) [Etale f.left] (x : ComplexPoint X)
    (D : LocalEtaleCoordinates Y n (Point.map f x).underlying) :
    ∃ E : LocalEtaleCoordinates X n x.underlying,
      ∀ (q : ComplexPoint X), q ∈ Point.overOpen E.neighborhood → ∀ i,
        Point.evaluate E.neighborhood (E.coordinateAlgHom (MvPolynomial.X i)) q =
          Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i)) (Point.map f q) := by
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (U := f.left ⁻¹ᵁ D.neighborhood) D.mem
  letI := s2e_step1_sectionAlgebra Y D.neighborhood
  letI := s2e_step1_sectionAlgebra X V
  let G := (s2e_complex_section_pullback X Y f D.neighborhood V hle).comp D.coordinateAlgHom
  let E : LocalEtaleCoordinates X n x.underlying := {
    neighborhood := V
    isAffine := hV
    mem := hxV
    coordinateAlgHom := G
    etale := RingHom.Etale.stableUnderComposition _ _ D.etale
      (f.left.etale_appLE D.isAffine hV hle) }
  refine ⟨E, ?_⟩
  intro q hq i
  change Point.evaluate V ((f.left.appLE D.neighborhood V hle).hom
    (D.coordinateAlgHom (MvPolynomial.X i))) q = _
  exact (Point.evaluate_res hle (f.left.app D.neighborhood
    (D.coordinateAlgHom (MvPolynomial.X i))) q hq).symm.trans
      (Point.evaluate_map f D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i)) q).symm

#print axioms s2e_etale_pullback_coordinates
end HodgeLean.Foundations.Program
