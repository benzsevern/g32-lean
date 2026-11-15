import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationCone
import HodgeLean.Adapters.IntersectionProductMovingRobertsFinite

/-! Finite linear Noether parameters in the specified ambient embedding. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- Finite linear parameters can be chosen in the specified ambient homogeneous coordinate ring. -/
lemma retained_presentation_finite_linear_forms
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (P : ProjectiveSpace.Presentation X.hom) (d : ℕ)
    (hdim : topologicalKrullDim X.left = (d : ℕ)) :
    ∃ ℓ : Matrix (Fin (d+1)) (Fin (P.ambientDimension+1)) ℂ,
      ((Ideal.Quotient.mk (retained_presentation_cone_ideal X P)).comp
        (a3r_lin ℓ).toRingHom).Finite := by
  have h := a3r_generic_finite (retained_presentation_cone_ideal X P)
    (retained_presentation_cone_homogeneous X P)
    (retained_presentation_cone_dimension X P d hdim)
  obtain ⟨a, ha⟩ := h.nonempty
  exact ⟨a3r_mat a, ha⟩

/-- Finite linear parameters have no common projective zero in the specified embedding. -/
lemma retained_presentation_exists_notMem (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {n : ℕ}
    (ℓ : Matrix (Fin (n + 1)) (Fin (D.ambientDimension + 1)) ℂ)
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp (a3r_lin ℓ).toRingHom).Finite) (x : X.left) :
    ∃ k, a3r_lin ℓ (MvPolynomial.X k) ∉ (retained_presentation_charts X D).prime x := by
  by_contra hall
  push Not at hall
  set P := (retained_presentation_charts X D).prime x
  have hdim := a3r_dim_eq_of_finite (retained_presentation_cone_ideal X D) ℓ hfin P ((retained_presentation_charts X D).prime_mono (genericPoint_specializes x))
  set K := RingHom.ker (constantCoeff : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ)
  have hK : K.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun z => ⟨C z, constantCoeff_C _ z⟩
  have hKle : K ≤ P.comap (a3r_lin ℓ) := by
    intro F hF
    have hF' : F ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin (n + 1))) :
        Set (MvPolynomial (Fin (n + 1)) ℂ)) := by
      rw [mem_ideal_span_X_image]
      intro m hm
      by_contra h0
      push Not at h0
      have hm0 : m = 0 := Finsupp.ext fun i => h0 i trivial
      rw [hm0, MvPolynomial.mem_support_iff, ← constantCoeff_eq] at hm
      exact hm (RingHom.mem_ker.1 hF)
    refine (Ideal.span_le.2 ?_) hF'
    rintro _ ⟨k, -, rfl⟩
    exact hall k
  have hcomapPrime : (P.comap (a3r_lin ℓ)).IsPrime := Ideal.comap_isPrime _ _
  have heq : P.comap (a3r_lin ℓ) = K := (hK.eq_of_le hcomapPrime.ne_top hKle).symm
  have h0 : ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P.comap (a3r_lin ℓ)) = 0 := by
    rw [heq]
    exact ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient K).1 hK)
  let C := retained_presentation_charts X D
  obtain ⟨j, hj⟩ : ∃ j, MvPolynomial.X j ∉ C.prime x :=
    ⟨C.chart x, fun h => (C.X_mem_prime_iff x _).1 h (C.mem_chart x)⟩
  have h1 := a3r_one_le_dim P ((retained_presentation_charts X D).isHomogeneous_prime x) j hj
  rw [hdim, h0] at h1
  exact absurd h1 (by decide)


end HodgeLean.Foundations.QuotientDuality
