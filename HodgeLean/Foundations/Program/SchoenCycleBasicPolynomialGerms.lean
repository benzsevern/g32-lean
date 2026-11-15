import HodgeLean.Foundations.Program.SchoenCycleAffinePolynomialGerms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Actual finitely many stalk elements have exact polynomial section representatives on one basic open inside a fixed affine neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.1–II.2. -/
theorem s2e_basic_polynomial_germ_representatives
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (x : X.left) (U : X.left.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
    {σ : Type*} [Finite σ] (r : σ → X.left.presheaf.stalk x) :
    letI : Algebra ℂ (X.left.presheaf.stalk x) :=
      (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
    ∃ (f : Γ(X.left, U)) (hxf : x ∈ X.left.basicOpen f),
      letI := s2e_step1_sectionAlgebra X (X.left.basicOpen f)
      ∃ F : MvPolynomial σ ℂ →ₐ[ℂ] Γ(X.left, X.left.basicOpen f),
        (s2e_complex_section_germ X (X.left.basicOpen f) x hxf).comp F = aeval r := by
  letI : Algebra ℂ (X.left.presheaf.stalk x) :=
    (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
  obtain ⟨V, _, _, hxV, s, hs⟩ :=
    s2e_simultaneous_affine_germ_representatives X.left x U hxU r
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hxU
  refine ⟨f, hxf, ?_⟩
  letI := s2e_step1_sectionAlgebra X (X.left.basicOpen f)
  refine ⟨aeval (fun i => (X.left.presheaf.map (homOfLE hfV).op).hom (s i)), ?_⟩
  ext i
  simp only [AlgHom.comp_apply, aeval_X]
  change (X.left.presheaf.map (homOfLE hfV).op ≫
    X.left.presheaf.germ (X.left.basicOpen f) x hxf).hom (s i) = r i
  rw [X.left.presheaf.germ_res]
  exact hs i

#print axioms s2e_basic_polynomial_germ_representatives
end HodgeLean.Foundations.Program
