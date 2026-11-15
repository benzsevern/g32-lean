import HodgeLean.Foundations.Program.SchoenCycleSectionStandardSmooth
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.AffineRelativeDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual affine open carrying n etale section coordinates is a smooth complex scheme of relative dimension n, without smoothness of the ambient scheme.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1. -/
theorem s2e_etale_sections_smooth_open
    (X : Over (Spec ↧ℂ)) (V : X.left.Opens) (hV : IsAffineOpen V) (n : ℕ) :
    letI := s2e_step1_sectionAlgebra X V
    ∀ G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, V), G.toRingHom.Etale →
      SmoothOfRelativeDimension n (ComplexPoint.openScheme X V).hom := by
  letI := s2e_step1_sectionAlgebra X V
  intro G hG
  let A := Γ(X.left, V)
  let P := MvPolynomial (Fin n) ℂ
  letI : Algebra P A := G.toAlgebra
  letI : IsScalarTower ℂ P A := IsScalarTower.of_algebraMap_eq' G.comp_algebraMap.symm
  letI : Algebra.Etale P A := RingHom.etale_algebraMap.mp hG
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 P A :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  have hs : Algebra.IsStandardSmoothOfRelativeDimension n ℂ A := by
    simpa only [zero_add] using Algebra.IsStandardSmoothOfRelativeDimension.trans n 0 ℂ P A
  exact smoothOfRelativeDimension_affineOpen_of_isStandardSmooth X.hom hV
    (s2e_section_standardSmooth_dimension X V n hs)

#print axioms s2e_etale_sections_smooth_open
end HodgeLean.Foundations.Program
