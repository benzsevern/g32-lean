import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-! # Permutation actions and symmetric coefficient rings

Implication from the actual variable permutation action to the polynomial
presentation of its fixed ring by elementary symmetric coefficients.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Variable renaming gives the polynomial permutation action.
Source: fundamental theorem of symmetric polynomials, variable permutation convention. -/
@[instance_reducible]
def s2v_l1a_polynomialPermutationAction (K ι : Type*) [CommRing K] :
    MulSemiringAction (Equiv.Perm ι) (MvPolynomial ι K) where
  smul g p := MvPolynomial.rename g p
  one_smul p := by
    change MvPolynomial.rename id p = p
    rw [MvPolynomial.rename_id]
    rfl
  mul_smul g h p := by
    change MvPolynomial.rename (g * h) p = MvPolynomial.rename g (MvPolynomial.rename h p)
    rw [MvPolynomial.rename_rename]
    rfl
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

/-- Renaming variables commutes with coefficient scalar multiplication.
Source: fundamental theorem of symmetric polynomials, coefficient-linear variable renaming. -/
theorem s2v_l1a_polynomialPermutationAction_scalars (K ι : Type*) [CommRing K] :
    letI := s2v_l1a_polynomialPermutationAction K ι
    SMulCommClass (Equiv.Perm ι) K (MvPolynomial ι K) := by
  letI := s2v_l1a_polynomialPermutationAction K ι
  constructor
  intro g c p
  change MvPolynomial.rename g (c • p) = c • MvPolynomial.rename g p
  exact map_smul (MvPolynomial.rename g) c p

/-- The fixed polynomial subalgebra is exactly the symmetric polynomial subalgebra.
Source: fundamental theorem of symmetric polynomials, definition of symmetry. -/
theorem s2v_l1a_polynomial_fixed_eq (K ι : Type*) [CommRing K] :
    letI := s2v_l1a_polynomialPermutationAction K ι
    letI := s2v_l1a_polynomialPermutationAction_scalars K ι
    FixedPoints.subalgebra K (MvPolynomial ι K) (Equiv.Perm ι) =
      MvPolynomial.symmetricSubalgebra ι K := by
  letI := s2v_l1a_polynomialPermutationAction K ι
  letI := s2v_l1a_polynomialPermutationAction_scalars K ι
  ext p
  rfl

/-- The fixed ring of the actual variable permutation action has its elementary
symmetric polynomial presentation, including the coefficient indexing.
Source: fundamental theorem of symmetric polynomials. -/
def s2v_l1a_polynomialFixedEquiv (K : Type*) [CommRing K] (n : ℕ) :
    letI := s2v_l1a_polynomialPermutationAction K (Fin n)
    letI := s2v_l1a_polynomialPermutationAction_scalars K (Fin n)
    MvPolynomial (Fin n) K ≃ₐ[K]
      FixedPoints.subalgebra K (MvPolynomial (Fin n) K) (Equiv.Perm (Fin n)) := by
  letI := s2v_l1a_polynomialPermutationAction K (Fin n)
  letI := s2v_l1a_polynomialPermutationAction_scalars K (Fin n)
  exact (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).trans
    (Subalgebra.equivOfEq _ _ (s2v_l1a_polynomial_fixed_eq K (Fin n)).symm)

/-- The actual fixed-ring presentation sends each coordinate to its indexed
elementary symmetric coefficient.
Source: fundamental theorem of symmetric polynomials. -/
theorem s2v_l1a_polynomialFixedEquiv_X (K : Type*) [CommRing K] (n : ℕ) (j : Fin n) :
    letI := s2v_l1a_polynomialPermutationAction K (Fin n)
    letI := s2v_l1a_polynomialPermutationAction_scalars K (Fin n)
    ((s2v_l1a_polynomialFixedEquiv K n) (MvPolynomial.X j) : MvPolynomial (Fin n) K) =
      MvPolynomial.esymm (Fin n) K (j.val + 1) := by
  change (MvPolynomial.esymmAlgHom (Fin n) K n (MvPolynomial.X j)).val = _
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.aeval_X]

end HodgeLean.Foundations.Program
