import HodgeLean.Foundations.Program.SchoenTowerL1aSymmetricCoefficientSquare
import HodgeLean.Foundations.Program.SchoenTowerL1aSymmetricParameterEtale
import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleLocalizationTransport
import Mathlib.RingTheory.Etale.Locus

/-! # Etale neighborhoods for actual descended symmetric coefficients

Implication from etale separated ordered parameters and the actual invariant
section image to a principal etale neighborhood of their descended coefficients.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The actual descended symmetric coefficient map is etale on a principal
neighborhood retaining the specified rational quotient point.
Source: Schoen (1988), Lemma 2.2, printed p. 13; EGA IV, 17.1.1. -/
theorem s2v_l1a_symmetric_coefficient_neighborhood
    {K B D : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing B] [CommRing D] [Algebra K B] [Algebra K D]
    [Algebra.FiniteType K B] (n : ℕ)
    [MulSemiringAction (Equiv.Perm (Fin n)) B]
    [SMulCommClass (Equiv.Perm (Fin n)) K B]
    (z : Fin n → B) (hz : ∀ g : Equiv.Perm (Fin n), ∀ i, g • z i = z (g i))
    (hEt : (MvPolynomial.aeval (R := K) z).toRingHom.Etale)
    (q : D →ₐ[K] B) (hq : Function.Injective q)
    (himage : ∀ b : B, b ∈ Set.range q ↔ ∀ g : Equiv.Perm (Fin n), g • b = b)
    (c : Fin n → D)
    (hc : ∀ j, q (c j) = MvPolynomial.aeval (R := K) z
      (MvPolynomial.esymm (Fin n) K (j.val + 1)))
    (φ : B →ₐ[K] K)
    (hreflect : ∀ g : Equiv.Perm (Fin n),
      (∀ i, φ (z (g⁻¹ i)) = φ (z i)) →
      φ.comp (MulSemiringAction.toAlgHom K B g⁻¹) = φ) :
    ∃ d : D, φ (q d) ≠ 0 ∧
      ((algebraMap D (Localization.Away d)).comp
        (MvPolynomial.aeval (R := K) c).toRingHom).Etale := by
  letI := s2v_l1a_polynomialPermutationAction K (Fin n)
  letI := s2v_l1a_polynomialPermutationAction_scalars K (Fin n)
  let P := MvPolynomial (Fin n) K
  let RA := FixedPoints.subalgebra K P (Equiv.Perm (Fin n))
  let RB := FixedPoints.subalgebra K B (Equiv.Perm (Fin n))
  let f := MvPolynomial.aeval (R := K) z
  let heq := s2v_l1a_parameter_eval_equivariant (K := K) z hz
  let F := s2t_fixedSubalgebraMap f heq
  letI : Algebra RA RB := F.toRingHom.toAlgebra
  letI : IsScalarTower K RA RB := IsScalarTower.of_algebraMap_eq
    (fun k => (F.commutes k).symm)
  letI : Algebra.FiniteType K RA := s2_fixedAlgebra_finiteType K P (Equiv.Perm (Fin n))
  letI : Algebra.FiniteType K RB := s2_fixedAlgebra_finiteType K B (Equiv.Perm (Fin n))
  letI : IsNoetherianRing RA := Algebra.FiniteType.isNoetherianRing K RA
  letI : Algebra.FiniteType RA RB := Algebra.FiniteType.of_restrictScalars_finiteType K RA RB
  letI : Algebra.FinitePresentation RA RB := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let ψ : RB →ₐ[K] K := φ.comp RB.val
  let Q := RingHom.ker ψ.toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime _
  letI : Algebra.IsEtaleAt RA Q :=
    s2v_l1a_symmetric_parameter_isEtaleAt n z hz hEt φ hreflect
  obtain ⟨r, hr, hrEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := RA) Q
  have hrMap : ((algebraMap RB (Localization.Away r)).comp F.toRingHom).Etale := by
    letI : Algebra.Etale RA (Localization.Away r) := hrEt
    change (algebraMap RA (Localization.Away r)).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  let eR := s2v_l1a_polynomialFixedEquiv K n
  let eD := s2v_l1a_invariantImageEquiv q hq himage
  have hcomm : eD.toRingHom.comp (MvPolynomial.aeval (R := K) c).toRingHom =
      F.toRingHom.comp eR.toRingHom := by
    exact congrArg (fun f : P →ₐ[K] RB => f.toRingHom)
      (s2v_l1a_symmetric_coefficient_square n z hz q hq himage c hc)
  refine ⟨eD.symm r, ?_, ?_⟩
  · change φ ((eD (eD.symm r)).val) ≠ 0
    rw [eD.apply_symm_apply]
    exact hr
  · exact s2v_l1a_etale_localization_transport
      (MvPolynomial.aeval (R := K) c).toRingHom F.toRingHom eR.toRingEquiv eD.toRingEquiv
      hcomm r hrMap

end HodgeLean.Foundations.Program
