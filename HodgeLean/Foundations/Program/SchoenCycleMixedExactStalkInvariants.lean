import HodgeLean.Foundations.Program.SchoenCycleMixedStalkInvariantValues
import HodgeLean.Foundations.Program.SchoenCycleFormalInvariantReflection

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every actual mixed elementary coefficient polynomial in the native curve parameters is fixed by the geometric tuple stabilizer on the actual stalk.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_mixed_exact_stalk_invariants
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n b : ℕ) (x : ComplexPoint (g3_power Z n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (q : MvPolynomial (Σ a, Fin (m a)) ℂ) (σ : s2e_powerPointStabilizer Z n x) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    let r := aeval (s2e_curvePowerParameter Z n x)
      (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m q).val)
    s2e_fixed_point_stalkPullback (g3_power Z n).left (s2_permute Z n σ.val).left x.underlying
      (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ.val) x σ.property) r = r := by
  dsimp only
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : IsLocallyNoetherian (g3_power Z n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z n).hom
  let β : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback (g3_power Z n).left
        (s2_permute Z n σ.val).left x.underlying
        (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ.val) x σ.property)
      commutes' := s2e_fixed_point_stalkPullback_scalars (g3_power Z n) (s2_permute Z n σ.val)
        x.underlying (s2e_complex_point_fixed_underlying (g3_power Z n)
          (s2_permute Z n σ.val) x σ.property) }
  let hf := s2e_fixed_point_stalkPullback_power (g3_power Z n).left
    (s2_permute Z n σ.val).left x.underlying
    (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ.val) x σ.property)
  let z := s2e_mixed_formal_stalk_invariant_coordinates Z n b x m ι p hp hx
    (AdicCompletion.of (idealOfVars (Σ a, Fin (m a)) ℂ)
      (MvPolynomial (Σ a, Fin (m a)) ℂ) q)
  have hz := Algebra.mem_iInf.mp z.property σ
  change s2e_adic_algebra_map _ _ β hf z.val = z.val at hz
  rw [s2e_mixed_formal_stalk_invariant_values Z n b x m ι p hp hx q] at hz
  exact s2e_actual_invariant_of_formal_invariant β hf _ hz

#print axioms s2e_mixed_exact_stalk_invariants
end HodgeLean.Foundations.Program
