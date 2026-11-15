import HodgeLean.Foundations.Program.SchoenCycleC1ParameterFormalCoordinates

/-! # Bijectivity of the specified formal parameter evaluation map -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The canonical adic map induced by regular parameter evaluation is bijective,
independently of the proof used to express preservation of the ideal powers. -/
theorem s2e_c1_parameter_adic_evaluation_bijective
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x))
    (hp : ∀ n : ℕ, ∀ p ∈ (Ideal.span {(Polynomial.X : Polynomial ℂ)}) ^ n,
      Polynomial.aeval t p ∈ IsLocalRing.maximalIdeal R ^ n) :
    Function.Bijective (s2e_adic_algebra_map _ _ (Polynomial.aeval t) hp) := by
  apply s2e_adic_algebra_map_bijective
  intro n
  have hI : (Ideal.span {(Polynomial.X : Polynomial ℂ)}) ^ n =
      Ideal.span {(Polynomial.X : Polynomial ℂ) ^ n} := Ideal.span_singleton_pow _ _
  have hJ : IsLocalRing.maximalIdeal R ^ n = Ideal.span {t ^ n} := by
    rw [ht, Ideal.span_singleton_pow]
  let E := ((Ideal.quotientEquivAlgOfEq ℂ hI).trans
    (s2e_parameter_jet_algEquiv R φ t ht hreg n)).trans
    (Ideal.quotientEquivAlgOfEq ℂ hJ.symm)
  refine ⟨E, ?_⟩
  intro p
  simp only [E, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    s2e_parameter_jet_algEquiv_mk]

end HodgeLean.Foundations.Program
