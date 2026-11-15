import HodgeLean.Foundations.Program.SchoenCycleOpenTopSectionEquiv
import HodgeLean.Foundations.Program.SchoenCycleEtaleSectionSmoothOpen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Supplied etale section coordinates give actual global etale coordinates on their own smooth open scheme at every marked point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
def s2e_etale_sections_top_coordinates
    (X : Over (Spec ↧ℂ)) (V : X.left.Opens) (hV : IsAffineOpen V) (n : ℕ) :
    letI := s2e_step1_sectionAlgebra X V
    ∀ (G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, V)) (hG : G.toRingHom.Etale),
      let Y := ComplexPoint.openScheme X V
      letI : SmoothOfRelativeDimension n Y.hom := s2e_etale_sections_smooth_open X V hV n G hG
      ∀ z : ComplexPoint Y, LocalEtaleCoordinates Y n z.underlying := by
  dsimp only
  letI := s2e_step1_sectionAlgebra X V
  intro G hG
  let Y := ComplexPoint.openScheme X V
  letI : SmoothOfRelativeDimension n Y.hom := s2e_etale_sections_smooth_open X V hV n G hG
  letI : IsAffine Y.left := hV
  letI := s2e_step1_sectionAlgebra Y ⊤
  intro z
  let G0 := (s2e_complex_open_top_section_equiv X V).toAlgHom.comp G
  refine {
    neighborhood := ⊤
    isAffine := isAffineOpen_top Y.left
    mem := trivial
    coordinateAlgHom := G0
    etale := ?_ }
  exact RingHom.Etale.respectsIso.1 G.toRingHom V.topIso.symm.commRingCatIsoToRingEquiv hG

#print axioms s2e_etale_sections_top_coordinates
end HodgeLean.Foundations.Program
