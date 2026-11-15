import HodgeLean.Foundations.Program.SchoenCycleSectionDefinedAffineMap
import HodgeLean.Foundations.Program.SchoenCycleOpenTopSectionEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual affine open is the spectrum of its original section algebra over the native complex structure map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_complex_affine_open_spec_iso
    (X : Over (Spec ↧ℂ)) (V : X.left.Opens) (hV : IsAffineOpen V) :
    letI := s2e_step1_sectionAlgebra X V
    ComplexPoint.openScheme X V ≅
      Over.mk (ComplexPoint.affineSpecStructureMap Γ(X.left, V)) := by
  letI := s2e_step1_sectionAlgebra X V
  let Y := ComplexPoint.openScheme X V
  letI : IsAffine Y.left := hV
  letI := s2e_step1_sectionAlgebra Y ⊤
  let G := (s2e_complex_open_top_section_equiv X V).toAlgHom
  let f := s2e_section_defined_affine_map Y Γ(X.left, V) G
  haveI : IsIso f.left := by
    change IsIso (Y.left.toSpecΓ ≫ Spec.map V.topIso.inv)
    infer_instance
  exact Over.isoMk (asIso f.left) f.w

#print axioms s2e_complex_affine_open_spec_iso
end HodgeLean.Foundations.Program
