import HodgeLean.Foundations.Program.SchoenTowerL1aEquivariantParameters
import HodgeLean.Foundations.Program.SchoenTowerL1aPolynomialStabilizers
import HodgeLean.Foundations.Program.SchoenTowerInvariantEtale
import Mathlib.RingTheory.RingHom.Etale

/-! # Local etaleness of symmetric parameter evaluation

Implication from etale ordered parameters and reflection of rational point
stabilizers to local etaleness on the actual invariant rings.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Etale ordered parameters induce an etale map of fixed rings at a rational
point when their values reflect its actual permutation stabilizer.
Source: Stacks Project, tag 04A9; EGA IV, 17.1.1, equivariant etale local comparison. -/
theorem s2v_l1a_symmetric_parameter_isEtaleAt
    {K B : Type} [Field K] [IsAlgClosed K] [CharZero K] [CommRing B]
    [Algebra K B] [Algebra.FiniteType K B] (n : ℕ)
    [MulSemiringAction (Equiv.Perm (Fin n)) B]
    [SMulCommClass (Equiv.Perm (Fin n)) K B]
    (z : Fin n → B) (hz : ∀ g : Equiv.Perm (Fin n), ∀ i, g • z i = z (g i))
    (hEt : (MvPolynomial.aeval (R := K) z).toRingHom.Etale)
    (φ : B →ₐ[K] K)
    (hreflect : ∀ g : Equiv.Perm (Fin n),
      (∀ i, φ (z (g⁻¹ i)) = φ (z i)) →
      φ.comp (MulSemiringAction.toAlgHom K B g⁻¹) = φ) :
    letI := s2v_l1a_polynomialPermutationAction K (Fin n)
    letI := s2v_l1a_polynomialPermutationAction_scalars K (Fin n)
    let f := MvPolynomial.aeval (R := K) z
    let heq := s2v_l1a_parameter_eval_equivariant (K := K) z hz
    letI := (s2t_fixedSubalgebraMap f heq).toRingHom.toAlgebra
    letI : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
    Algebra.IsEtaleAt
      (FixedPoints.subalgebra K (MvPolynomial (Fin n) K) (Equiv.Perm (Fin n)))
      ((RingHom.ker φ.toRingHom).under (FixedPoints.subalgebra K B (Equiv.Perm (Fin n)))) := by
  letI := s2v_l1a_polynomialPermutationAction K (Fin n)
  letI := s2v_l1a_polynomialPermutationAction_scalars K (Fin n)
  let f := MvPolynomial.aeval (R := K) z
  let heq := s2v_l1a_parameter_eval_equivariant (K := K) z hz
  let qA := RingHom.ker (φ.comp f).toRingHom
  let qB := RingHom.ker φ.toRingHom
  letI : qA.IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun k => ⟨algebraMap K (MvPolynomial (Fin n) K) k, (φ.comp f).commutes k⟩)
  letI : qB.IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun k => ⟨algebraMap K B k, φ.commutes k⟩)
  have hcomp : φ.comp f = MvPolynomial.aeval (R := K) (fun i => φ (z i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, f, MvPolynomial.aeval_X]
  have hstab (g : Equiv.Perm (Fin n)) : g • qA = qA ↔ g • qB = qB := by
    dsimp only [qA, qB]
    rw [hcomp, s2v_l1a_polynomial_kernel_stabilizer,
      s2v_l1a_rational_kernel_stabilizer]
    constructor
    · exact hreflect g
    · intro h i
      have H := congrArg (fun ψ : B →ₐ[K] K => ψ (z i)) h
      change φ (g⁻¹ • z i) = φ (z i) at H
      rw [hz] at H
      exact H
  have hformal : f.toRingHom.FormallyEtale := by
    letI : Algebra (MvPolynomial (Fin n) K) B := f.toRingHom.toAlgebra
    letI : Algebra.Etale (MvPolynomial (Fin n) K) B := hEt
    exact inferInstanceAs (Algebra.FormallyEtale (MvPolynomial (Fin n) K) B)
  exact s2t_invariant_isEtaleAt f heq qA qB (fun _ ha => ha) hformal hstab

end HodgeLean.Foundations.Program
