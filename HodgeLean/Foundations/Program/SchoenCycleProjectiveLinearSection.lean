import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartSections

/-! # Actual regular linear equations on retained projective charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A complex linear form gives an actual regular section on each retained standard projective affine chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_standardProjectiveLinearSection
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ) (i : Fin (k + 1)) :
    Γ(ProjectiveSpace (Fin (k + 1)) (Spec (CommRingCat.of ℂ)),
      (s2e_standardProjectiveAffineOpen i).1) :=
  (s2e_standardProjectiveSectionRingEquiv i).symm
    (Ideal.Quotient.mk (Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (k + 1)) ℂ)))
      (∑ j, MvPolynomial.C (L (Module.finBasisOfFinrankEq ℂ V hd j)) * MvPolynomial.X j))

example (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ) (i : Fin (k + 1)) :
    s2e_standardProjectiveSectionRingEquiv i (s2e_standardProjectiveLinearSection V k hd L i) =
      Ideal.Quotient.mk (Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (k + 1)) ℂ)))
        (∑ j, MvPolynomial.C (L (Module.finBasisOfFinrankEq ℂ V hd j)) * MvPolynomial.X j) :=
  (s2e_standardProjectiveSectionRingEquiv i).apply_symm_apply _

end HodgeLean.Foundations.Program
