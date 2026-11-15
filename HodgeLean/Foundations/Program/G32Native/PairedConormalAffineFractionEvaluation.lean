import HodgeLean.Foundations.Program.G32Native.PairedConormalAwayEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedConormalGradedAffineEvaluation

/-! # Affine evaluation of actual homogeneous fraction sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Composing a projective chart with an affine ring map evaluates its actual
fraction sections by that same specified ring map. -/
theorem conormal_affine_fraction_evaluation (k : ℕ) (i : Fin (k + 1))
    {R : Type} [CommRing R]
    (f : HomogeneousLocalization.Away (UniversalGrading k) (X i) →+* R)
    (h : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      (Spec.map (CommRingCat.ofHom f) ≫
        Proj.awayι (UniversalGrading k) (X i) (isHomogeneous_X (ULift ℤ) i) zero_lt_one) ⁻¹ᵁ
          Proj.basicOpen (UniversalGrading k) (X i)) :
    Proj.awayToSection (UniversalGrading k) (X i) ≫
      (Spec.map (CommRingCat.ofHom f) ≫
        Proj.awayι (UniversalGrading k) (X i) (isHomogeneous_X (ULift ℤ) i) zero_lt_one).appLE
        (Proj.basicOpen (UniversalGrading k) (X i)) ⊤ h ≫
          (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom f := by
  exact conormal_graded_affine_fraction_evaluation (UniversalGrading k) (X i)
    (isHomogeneous_X (ULift ℤ) i) zero_lt_one f h

end HodgeLean.Foundations.Program.G32Native
