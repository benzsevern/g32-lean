import HodgeLean.Foundations.Program.SchoenCycleAdicCotangentInverse
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraLift
import HodgeLean.Foundations.Program.SchoenCycleCoefficientAdicNoetherian
import HodgeLean.Foundations.Program.SchoenCycleCoefficientAdicAugmentation
import HodgeLean.Foundations.Program.SchoenCycleMaximalAdicLocal
import HodgeLean.Foundations.Program.SchoenCycleOriginIdealMaximal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Prescribed elements of the coefficient-origin maximal ideal whose classes form a cotangent basis are actual formal algebra coordinates, with their prescribed values on every variable.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2, 7 and 10. -/
theorem s2e_formal_coefficient_inverse
    (k σ : Type*) [Field k] [Finite σ] :
    let I := idealOfVars σ k
    let A := AdicCompletion I (MvPolynomial σ k)
    letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
    letI := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
    ∀ (c : σ → A) (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal A)
      (b : Module.Basis σ k (IsLocalRing.maximalIdeal A).Cotangent),
      (∀ i, b i = (IsLocalRing.maximalIdeal A).toCotangent ⟨c i, hc i⟩) →
      ∃ E : A ≃ₐ[k] A, ∀ i, E (AdicCompletion.of I (MvPolynomial σ k) (X i)) = c i := by
  dsimp only
  let I := idealOfVars σ k
  let P := MvPolynomial σ k
  let A := AdicCompletion I P
  letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
  letI : IsLocalRing A := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
  letI : IsNoetherianRing A := s2e_coefficient_adic_isNoetherianRing k σ
  have hJ : I.map (algebraMap P A) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I I le_rfl (idealOfVars_fg σ k))
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
    hJ ▸ AdicCompletion.isAdicComplete_self I (idealOfVars_fg σ k)
  intro c hc b hb
  let f : P →ₐ[k] A := aeval c
  have hI : I ≤ (IsLocalRing.maximalIdeal A).comap f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f (X i) ∈ IsLocalRing.maximalIdeal A
    change (aeval (R := k) c) (X i) ∈ IsLocalRing.maximalIdeal A
    rw [aeval_X]
    exact hc i
  have hp : ∀ n r, r ∈ I ^ n → f r ∈ IsLocalRing.maximalIdeal A ^ n := by
    intro n r hr
    have hh : (I ^ n).map f.toRingHom ≤ IsLocalRing.maximalIdeal A ^ n := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hI) n
    exact hh (Ideal.mem_map_of_mem f.toRingHom hr)
  let F := s2e_adic_algebra_lift I (IsLocalRing.maximalIdeal A) f hp
  have hF (r : P) : F (AdicCompletion.of I P r) = f r := s2e_adic_algebra_lift_of I _ f hp r
  have hFm : ∀ r ∈ IsLocalRing.maximalIdeal A, F r ∈ IsLocalRing.maximalIdeal A := by
    change IsLocalRing.maximalIdeal A ≤ (IsLocalRing.maximalIdeal A).comap F.toRingHom
    apply Ideal.map_le_iff_le_comap.mp
    rw [← hJ, Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change F (AdicCompletion.of I P r) ∈ I.map (algebraMap P A)
    rw [hF, hJ]
    exact hI hr
  have hvar (i : σ) : AdicCompletion.of I P (X i) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hJ]
    exact Ideal.mem_map_of_mem (algebraMap P A) (Ideal.subset_span ⟨i, rfl⟩)
  have hbij : Function.Bijective F := s2e_adic_endomorphism_bijective_of_cotangent_basis
    k A σ (s2e_coefficient_adic_augmentation k σ) F hFm
    (fun i => ⟨AdicCompletion.of I P (X i), hvar i⟩) b (by
      intro i
      change b i = (IsLocalRing.maximalIdeal A).toCotangent
        ⟨F (AdicCompletion.of I P (X i)), _⟩
      exact (hb i).trans (congrArg (IsLocalRing.maximalIdeal A).toCotangent
        (Subtype.ext (show c i = F (AdicCompletion.of I P (X i)) by rw [hF, aeval_X]))))
  exact ⟨AlgEquiv.ofBijective F hbij, fun i => by
    change F (AdicCompletion.of I P (X i)) = c i
    rw [hF, aeval_X]⟩

#print axioms s2e_formal_coefficient_inverse
end HodgeLean.Foundations.Program
