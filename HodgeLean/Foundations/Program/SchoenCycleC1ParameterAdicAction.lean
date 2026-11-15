import HodgeLean.Foundations.Program.SchoenCycleC1ParameterAdicEvaluation
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMapComp

/-! # Formal action coordinates for a specified regular eigenparameter -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The actual maps on all finite parameter jets intertwine, and therefore so
 do their induced adic maps, for every prescribed scalar parameter action. -/
theorem s2e_c1_parameter_adic_action
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x))
    (T : Type*) (β : T → R →ₐ[ℂ] R) (ζ : T → ℂ)
    (he : ∀ g, β g t = algebraMap ℂ R (ζ g) * t) :
    let I : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X}
    let J : Ideal R := IsLocalRing.maximalIdeal R
    let α (g : T) : Polynomial ℂ →ₐ[ℂ] Polynomial ℂ :=
      Polynomial.aeval (Polynomial.C (ζ g) * Polynomial.X)
    ∃ hp : ∀ n : ℕ, ∀ p ∈ I ^ n, Polynomial.aeval t p ∈ J ^ n,
    ∃ hα : ∀ g n, ∀ p ∈ I ^ n, α g p ∈ I ^ n,
    ∃ hβ : ∀ g n, ∀ x ∈ J ^ n, β g x ∈ J ^ n,
    ∃ E : AdicCompletion I (Polynomial ℂ) ≃ₐ[ℂ] AdicCompletion J R,
      E.toAlgHom = s2e_adic_algebra_map I J (Polynomial.aeval t) hp ∧
      (∀ p, E (AdicCompletion.of _ _ p) =
        AdicCompletion.of _ _ (Polynomial.aeval t p)) ∧
      ∀ g, (s2e_adic_algebra_map J J (β g) (hβ g)).comp E.toAlgHom =
        E.toAlgHom.comp (s2e_adic_algebra_map I I (α g) (hα g)) := by
  dsimp only
  let I : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X}
  let J : Ideal R := IsLocalRing.maximalIdeal R
  let α (g : T) : Polynomial ℂ →ₐ[ℂ] Polynomial ℂ :=
    Polynomial.aeval (Polynomial.C (ζ g) * Polynomial.X)
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
  have hα (g : T) (n : ℕ) (p : Polynomial ℂ) (h : p ∈ I ^ n) : α g p ∈ I ^ n := by
    rw [hI, Ideal.mem_span_singleton] at h ⊢
    obtain ⟨q, rfl⟩ := h
    refine ⟨Polynomial.C (ζ g) ^ n * α g q, ?_⟩
    simp only [map_mul, map_pow, α, Polynomial.aeval_X, mul_pow]
    ring
  have hβ (g : T) (n : ℕ) (x : R) (h : x ∈ J ^ n) : β g x ∈ J ^ n := by
    rw [hJ, Ideal.mem_span_singleton] at h ⊢
    obtain ⟨y, rfl⟩ := h
    refine ⟨algebraMap ℂ R (ζ g) ^ n * β g y, ?_⟩
    rw [map_mul, map_pow, he, mul_pow]
    ring
  let E := AlgEquiv.ofBijective (s2e_adic_algebra_map I J (Polynomial.aeval t) hp)
    (s2e_c1_parameter_adic_evaluation_bijective R φ t ht hreg hp)
  refine ⟨hp, hα, hβ, E, rfl, ?_, ?_⟩
  · intro p
    exact s2e_adic_algebra_map_of I J (Polynomial.aeval t) hp p
  · intro g
    change (s2e_adic_algebra_map J J (β g) (hβ g)).comp
        (s2e_adic_algebra_map I J (Polynomial.aeval t) hp) =
      (s2e_adic_algebra_map I J (Polynomial.aeval t) hp).comp
        (s2e_adic_algebra_map I I (α g) (hα g))
    rw [s2e_adic_algebra_map_comp, s2e_adic_algebra_map_comp]
    have hc : (β g).comp (Polynomial.aeval t) = (Polynomial.aeval t).comp (α g) := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, Polynomial.aeval_X, α, map_mul, Polynomial.aeval_C, he]
    congr 1

end HodgeLean.Foundations.Program
