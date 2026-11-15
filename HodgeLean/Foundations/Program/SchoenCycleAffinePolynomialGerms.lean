import HodgeLean.Foundations.Program.SchoenCycleSimultaneousAffineGerms
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineGerm
import Mathlib.Algebra.MvPolynomial.CommRing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Finitely many actual complex stalk elements are the variable germs of one affine polynomial coordinate map on a prescribed neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.1–II.2. -/
theorem s2e_affine_polynomial_germ_representatives
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (x : X.left) (U : X.left.Opens) (hxU : x ∈ U)
    {σ : Type*} [Finite σ] (r : σ → X.left.presheaf.stalk x) :
    letI : Algebra ℂ (X.left.presheaf.stalk x) :=
      (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
    ∃ (V : X.left.Opens) (_ : IsAffineOpen V) (_ : V ≤ U) (hxV : x ∈ V),
      letI := s2e_step1_sectionAlgebra X V
      ∃ F : MvPolynomial σ ℂ →ₐ[ℂ] Γ(X.left, V),
        (s2e_complex_section_germ X V x hxV).comp F = aeval r := by
  letI : Algebra ℂ (X.left.presheaf.stalk x) :=
    (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
  obtain ⟨V, hV, hVU, hxV, s, hs⟩ :=
    s2e_simultaneous_affine_germ_representatives X.left x U hxU r
  refine ⟨V, hV, hVU, hxV, ?_⟩
  letI := s2e_step1_sectionAlgebra X V
  refine ⟨aeval s, ?_⟩
  ext i
  simp only [AlgHom.comp_apply, aeval_X]
  exact hs i

#print axioms s2e_affine_polynomial_germ_representatives
end HodgeLean.Foundations.Program
