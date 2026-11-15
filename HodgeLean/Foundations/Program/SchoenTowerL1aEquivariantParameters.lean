import HodgeLean.Foundations.Program.SchoenTowerL1aPolynomialAction
import HodgeLean.Foundations.Program.SchoenTowerEquivariantFixedMaps

/-! # Equivariant polynomial evaluation for actual parameters

Implication from the parameter permutation equations to equivariance of the
actual polynomial evaluation map and its fixed-ring coordinates.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual polynomial evaluation map is equivariant when its parameters
satisfy the specified permutation equations.
Source: Schoen (1988), Lemma 2.2, printed p. 13, symmetric local parameters. -/
theorem s2v_l1a_parameter_eval_equivariant
    {K B ι : Type*} [CommRing K] [CommRing B] [Algebra K B]
    [MulSemiringAction (Equiv.Perm ι) B] [SMulCommClass (Equiv.Perm ι) K B]
    (z : ι → B) (hz : ∀ g : Equiv.Perm ι, ∀ i, g • z i = z (g i)) :
    letI := s2v_l1a_polynomialPermutationAction K ι
    ∀ (g : Equiv.Perm ι) (p : MvPolynomial ι K),
      MvPolynomial.aeval (R := K) z (g • p) = g • MvPolynomial.aeval (R := K) z p := by
  letI := s2v_l1a_polynomialPermutationAction K ι
  intro g p
  have H : (MvPolynomial.aeval (R := K) z).comp (MvPolynomial.rename g) =
      (MulSemiringAction.toAlgHom K B g).comp (MvPolynomial.aeval (R := K) z) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    exact (hz g i).symm
  exact congrArg (fun F : MvPolynomial ι K →ₐ[K] B => F p) H

end HodgeLean.Foundations.Program
