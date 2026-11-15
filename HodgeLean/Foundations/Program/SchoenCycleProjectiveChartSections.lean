import HodgeLean.Foundations.Program.SchoenCycleProjectiveStandardChart

/-! # Actual section rings of the retained standard projective charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Sections on the actual retained standard projective chart identify with normalized complex polynomials.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_standardProjectiveSectionRingEquiv {n : ℕ} (i : Fin (n + 1)) :
    Γ(ProjectiveSpace (Fin (n + 1)) (Spec (CommRingCat.of ℂ)),
      (s2e_standardProjectiveAffineOpen i).1) ≃+*
      MvPolynomial (Fin (n + 1)) ℂ ⧸
        Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) ℂ)) := by
  let A := ℂ ⊗[ℤ] HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)
  letI : IsOpenImmersion (s2e_standardProjectiveChart i) :=
    s2e_standardProjectiveChart_isOpenImmersion i
  let e₁ : Γ(ProjectiveSpace (Fin (n + 1)) (Spec (CommRingCat.of ℂ)),
      (s2e_standardProjectiveAffineOpen i).1) ≅ Γ(Spec (CommRingCat.of A), ⊤) :=
    (s2e_standardProjectiveChart i).appIso ⊤
  exact e₁.commRingCatIsoToRingEquiv.trans
    ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.trans
      (s2e_baseChangedChartAlgEquiv ℂ i).toRingEquiv)

end HodgeLean.Foundations.Program
