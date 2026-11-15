import HodgeLean.Foundations.Program.SchoenCycleParameterPermutations
import HodgeLean.Foundations.Program.SchoenCycleFixedStalkScalars

/-! # Polynomial parameter expressions under actual tuple stabilizers -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual fixed-tuple stalk action on every polynomial parameter
expression is the polynomial coordinate renaming action.
Source: Hartshorne, Algebraic Geometry, II.2; Macdonald, Symmetric Functions
and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_fixed_permutation_parameter_polynomial
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : ComplexPoint (g3_power X n))
    (hx : Point.map (s2_permute X n σ) x = x) (p : MvPolynomial (Fin n) ℂ) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    s2e_fixed_point_stalkPullback (g3_power X n).left (s2_permute X n σ).left x.underlying
      (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ) x hx)
      (aeval (s2e_curvePowerParameter X n x) p) =
        aeval (s2e_curvePowerParameter X n x) (rename σ.symm p) := by
  let P := g3_power X n
  let R := P.left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let q := s2_permute X n σ
  let hp := s2e_complex_point_fixed_underlying P q x hx
  let α : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback P.left q.left x.underlying hp
      commutes' := s2e_fixed_point_stalkPullback_scalars P q x.underlying hp }
  have he : α.comp (aeval (s2e_curvePowerParameter X n x)) =
      (aeval (s2e_curvePowerParameter X n x)).comp (rename σ.symm) := by
    ext i
    change α (aeval (s2e_curvePowerParameter X n x)
        (MvPolynomial.X i : MvPolynomial (Fin n) ℂ)) =
      aeval (s2e_curvePowerParameter X n x)
        (rename σ.symm (MvPolynomial.X i : MvPolynomial (Fin n) ℂ))
    rw [aeval_X, rename_X, aeval_X]
    exact s2e_fixed_permutation_curvePowerParameter X n σ x hx i
  exact congrArg (fun k : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R => k p) he

end HodgeLean.Foundations.Program
