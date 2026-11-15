import HodgeLean.Foundations.Program.SchoenTowerL1aEquivariantParameters
import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantImageEquiv

/-! # The actual symmetric coefficient presentation square

Implication from the actual descended coefficient equations to the commuting
square of fixed-ring and quotient section presentations.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The descended coefficient evaluation is exactly the fixed-ring parameter
map under the actual source and target algebra identifications.
Source: Schoen (1988), Lemma 2.2, printed p. 13; fundamental theorem of symmetric polynomials. -/
theorem s2v_l1a_symmetric_coefficient_square
    {K B D : Type*} [CommRing K] [CommRing B] [CommRing D]
    [Algebra K B] [Algebra K D] (n : ℕ)
    [MulSemiringAction (Equiv.Perm (Fin n)) B]
    [SMulCommClass (Equiv.Perm (Fin n)) K B]
    (z : Fin n → B) (hz : ∀ g : Equiv.Perm (Fin n), ∀ i, g • z i = z (g i))
    (q : D →ₐ[K] B) (hq : Function.Injective q)
    (himage : ∀ b : B, b ∈ Set.range q ↔ ∀ g : Equiv.Perm (Fin n), g • b = b)
    (c : Fin n → D)
    (hc : ∀ j, q (c j) = MvPolynomial.aeval (R := K) z
      (MvPolynomial.esymm (Fin n) K (j.val + 1))) :
    letI := s2v_l1a_polynomialPermutationAction K (Fin n)
    letI := s2v_l1a_polynomialPermutationAction_scalars K (Fin n)
    (s2v_l1a_invariantImageEquiv q hq himage).toAlgHom.comp (MvPolynomial.aeval (R := K) c) =
      (s2t_fixedSubalgebraMap (MvPolynomial.aeval (R := K) z)
        (s2v_l1a_parameter_eval_equivariant (K := K) z hz)).comp
          (s2v_l1a_polynomialFixedEquiv K n).toAlgHom := by
  letI := s2v_l1a_polynomialPermutationAction K (Fin n)
  letI := s2v_l1a_polynomialPermutationAction_scalars K (Fin n)
  apply MvPolynomial.algHom_ext
  intro j
  apply Subtype.ext
  change q (MvPolynomial.aeval (R := K) c (MvPolynomial.X j)) =
    MvPolynomial.aeval (R := K) z
      ((s2v_l1a_polynomialFixedEquiv K n) (MvPolynomial.X j) : MvPolynomial (Fin n) K)
  rw [MvPolynomial.aeval_X, s2v_l1a_polynomialFixedEquiv_X]
  exact hc j

end HodgeLean.Foundations.Program
