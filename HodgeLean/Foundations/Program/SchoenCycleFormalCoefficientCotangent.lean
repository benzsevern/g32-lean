import HodgeLean.Foundations.Program.SchoenCycleCoefficientCotangentBasis
import HodgeLean.Foundations.Program.SchoenCycleAdicCotangentEquiv
import HodgeLean.Foundations.Program.SchoenCycleMaximalAdicLocal
import HodgeLean.Foundations.Program.SchoenCycleOriginIdealMaximal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The actual formal coefficient variables form a basis in the maximal-ideal cotangent module of the coefficient adic algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_formal_coefficient_cotangent_basis
    (k σ : Type*) [Field k] [Fintype σ] :
    let I := idealOfVars σ k
    let A := AdicCompletion I (MvPolynomial σ k)
    letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
    letI := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
    ∃ B : Module.Basis σ k (IsLocalRing.maximalIdeal A).Cotangent,
      ∀ i, ∃ hi : AdicCompletion.of I (MvPolynomial σ k) (X i) ∈ IsLocalRing.maximalIdeal A,
        B i = (IsLocalRing.maximalIdeal A).toCotangent
          ⟨AdicCompletion.of I (MvPolynomial σ k) (X i), hi⟩ := by
  dsimp only
  let I := idealOfVars σ k
  let P := MvPolynomial σ k
  let A := AdicCompletion I P
  letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
  letI := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
  let J := I.map (algebraMap P A)
  have hJ : J = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I I le_rfl (idealOfVars_fg σ k))
  let E := (s2e_adic_ideal_cotangent_equiv (k := k) I (idealOfVars_fg σ k)).trans
    ((Ideal.Cotangent.equivOfEq J (IsLocalRing.maximalIdeal A) hJ).restrictScalars k)
  obtain ⟨B, hB⟩ := s2e_coefficient_origin_cotangent_basis (R := k) (σ := σ)
  refine ⟨B.map E, ?_⟩
  intro i
  have hi : AdicCompletion.of I P (X i) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hJ]
    exact Ideal.mem_map_of_mem (algebraMap P A) (Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨hi, ?_⟩
  rw [Module.Basis.map_apply, hB]
  rfl

#print axioms s2e_formal_coefficient_cotangent_basis
end HodgeLean.Foundations.Program
