import HodgeLean.Foundations.Program.SchoenCycleInsertionParameters
import HodgeLean.Foundations.Program.SchoenCycleStalkScalars

/-! # Polynomial coordinate action of actual marked insertion -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual insertion stalk map acts on parameter polynomials by setting
the marked coordinate to zero and preserving every moving coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_branchInsertion_parameter_polynomial
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z n))
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    let q := s2c_branchInsertion Z n a
    let z := Point.map q x
    let Rt := (g3_power Z (n + 1)).left.presheaf.stalk z.underlying
    let Rs := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ Rt := (HodgeLean.Foundations.Curves.stalkC z.underlying).toAlgebra
    letI : Algebra ℂ Rs := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    q.left.stalkMap x.underlying (aeval (s2e_curvePowerParameter Z (n + 1) z) p) =
      aeval (Fin.cases 0 (s2e_curvePowerParameter Z n x)) p := by
  let q := s2c_branchInsertion Z n a
  let z := Point.map q x
  let Rt := (g3_power Z (n + 1)).left.presheaf.stalk z.underlying
  let Rs := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ Rt := (HodgeLean.Foundations.Curves.stalkC z.underlying).toAlgebra
  letI : Algebra ℂ Rs := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let F : Rt →ₐ[ℂ] Rs :=
    { toRingHom := (q.left.stalkMap x.underlying).hom
      commutes' := fun c => s2e_stalkMap_complex_scalars (g3_power Z n)
        (g3_power Z (n + 1)) q x.underlying c }
  have he : F.comp (aeval (s2e_curvePowerParameter Z (n + 1) z)) =
      aeval (Fin.cases 0 (s2e_curvePowerParameter Z n x)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change F (aeval (s2e_curvePowerParameter Z (n + 1) z)
      (X i : MvPolynomial (Fin (n + 1)) ℂ)) =
      aeval (Fin.cases 0 (s2e_curvePowerParameter Z n x))
        (X i : MvPolynomial (Fin (n + 1)) ℂ)
    rw [aeval_X, aeval_X]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact s2e_branchInsertion_curvePowerParameter_zero Z n a x
    · exact s2e_branchInsertion_curvePowerParameter_succ Z n a x j
  exact congrArg (fun f : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] Rs => f p) he

end HodgeLean.Foundations.Program
