import HodgeLean.Foundations.Program.SchoenCycleParameterJetAlgebra
import HodgeLean.Foundations.Program.SchoenCycleAdicMapBijective
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues

/-! # Formal coordinates retaining a specified regular parameter -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- Evaluation in a regular parameter induces formal coordinates and retains
all polynomial values under the canonical maps to the completions. -/
theorem s2e_c1_parameter_formal_coordinates
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x)) :
    ∃ E : AdicCompletion (Ideal.span {(Polynomial.X : Polynomial ℂ)}) (Polynomial ℂ)
        ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal R) R,
      ∀ p : Polynomial ℂ, E (AdicCompletion.of _ _ p) =
        AdicCompletion.of _ _ (Polynomial.aeval t p) := by
  let I : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X}
  let J : Ideal R := IsLocalRing.maximalIdeal R
  have hI (n : ℕ) : I ^ n = Ideal.span {(Polynomial.X : Polynomial ℂ) ^ n} :=
    Ideal.span_singleton_pow _ _
  have hJ (n : ℕ) : J ^ n = Ideal.span {t ^ n} := by
    change IsLocalRing.maximalIdeal R ^ n = _
    rw [ht, Ideal.span_singleton_pow]
  have hp (n : ℕ) (p : Polynomial ℂ) (h : p ∈ I ^ n) :
      Polynomial.aeval t p ∈ J ^ n := by
    rw [hI, Ideal.mem_span_singleton] at h
    obtain ⟨q, rfl⟩ := h
    rw [map_mul, map_pow, Polynomial.aeval_X, hJ]
    exact (Ideal.span {t ^ n}).mul_mem_right _ (Ideal.subset_span rfl)
  have hj (n : ℕ) : ∃ e : (Polynomial ℂ ⧸ I ^ n) ≃ₐ[ℂ] (R ⧸ J ^ n),
      ∀ p, e (Ideal.Quotient.mk (I ^ n) p) =
        Ideal.Quotient.mk (J ^ n) (Polynomial.aeval t p) := by
    let E := ((Ideal.quotientEquivAlgOfEq ℂ (hI n)).trans
      (s2e_parameter_jet_algEquiv R φ t ht hreg n)).trans
      (Ideal.quotientEquivAlgOfEq ℂ (hJ n).symm)
    refine ⟨E, ?_⟩
    intro p
    simp only [E, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      s2e_parameter_jet_algEquiv_mk]
  refine ⟨AlgEquiv.ofBijective (s2e_adic_algebra_map I J (Polynomial.aeval t) hp)
    (s2e_adic_algebra_map_bijective I J (Polynomial.aeval t) hp hj), ?_⟩
  intro p
  exact s2e_adic_algebra_map_of I J (Polynomial.aeval t) hp p

end HodgeLean.Foundations.Program
