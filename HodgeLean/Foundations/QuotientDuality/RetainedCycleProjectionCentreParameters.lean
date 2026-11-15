import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationNoether

/-! # Finite projection parameters with the required centre dimension bound -/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- Finite Noether parameters can simultaneously cut the ambient cone by the required number of dimensions. -/
lemma retained_presentation_finite_forms_with_centre_bound
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) (n : ℕ)
    (hdim : topologicalKrullDim X.left = (n : ℕ)) :
    ∃ ℓ : Matrix (Fin (n+1)) (Fin (D.ambientDimension+1)) ℂ,
      ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
        (a3r_lin ℓ).toRingHom).Finite ∧
      ∀ Q : Ideal (MvPolynomial (Fin (D.ambientDimension+1)) ℂ), Q.IsPrime →
        (∃ j, MvPolynomial.X j ∉ Q) →
        (∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈ Q) →
        ringKrullDim (MvPolynomial (Fin (D.ambientDimension+1)) ℂ ⧸ Q) + (n+1 : ℕ) ≤
          ringKrullDim (MvPolynomial (Fin (D.ambientDimension+1)) ℂ) := by
  classical
  have hf := a3r_generic_finite (retained_presentation_cone_ideal X D)
    (retained_presentation_cone_homogeneous X D)
    (retained_presentation_cone_dimension X D n hdim)
  have hb := a3r_generic_iInter_fintype _ fun j : Fin (D.ambientDimension+1) =>
    a3r_generic_linear (ρ := Fin (n+1)) (MvPolynomial (Fin (D.ambientDimension+1)) ℂ)
      MvPolynomial.X 0 j
  obtain ⟨a, ha, hb⟩ := (hf.inter hb).nonempty
  refine ⟨a3r_mat a, ha, ?_⟩
  intro Q hQ hrel hforms
  obtain ⟨j, hj⟩ := hrel
  have h := hb j Q hQ hj (fun i => by
    simpa [a3r_lin_X, a3r_mat] using hforms i)
  simpa only [Fintype.card_fin] using h

end HodgeLean.Foundations.QuotientDuality


/-! Finite projection parameters with a uniform dimension bound on the ambient centre. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- Finite parameters can simultaneously impose the expected dimension bound at their ambient centre.
Source: Hartshorne, Algebraic Geometry, II, Exercise 3.22; Kleiman (1974), proof of Theorem 2. -/
lemma retained_presentation_finite_parameters_with_centre_bound
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) (d : ℕ)
    (hdim : topologicalKrullDim X.left = (d : ℕ)) :
    ∃ ℓ : Matrix (Fin (d+1)) (Fin (D.ambientDimension+1)) ℂ,
      ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
        (a3r_lin ℓ).toRingHom).Finite ∧
      ∀ P : Ideal (MvPolynomial (Fin (D.ambientDimension+1)) ℂ), P.IsPrime →
        (∃ j, MvPolynomial.X j ∉ P) →
        (∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈ P) →
        ringKrullDim (MvPolynomial (Fin (D.ambientDimension+1)) ℂ ⧸ P) +
          (d+1 : ℕ) ≤ (D.ambientDimension+1 : ℕ) := by
  classical
  let S := MvPolynomial (Fin (D.ambientDimension+1)) ℂ
  let U (j : Fin (D.ambientDimension+1)) :=
    {a : Fin (d+1) × Fin (D.ambientDimension+1) → ℂ |
      ∀ P : Ideal S, P.IsPrime → MvPolynomial.X j ∉ P →
        (∀ i, ∑ k, algebraMap ℂ S (a (i,k)) * MvPolynomial.X k - 0 ∈ P) →
        ringKrullDim (S ⧸ P) + Fintype.card (Fin (d+1)) ≤ ringKrullDim S}
  have hU : ∀ j, a3r_Generic (U j) := fun j =>
    a3r_generic_linear S (fun k => MvPolynomial.X k) (fun _ : Fin (d+1) => 0) j
  have hf := a3r_generic_finite (retained_presentation_cone_ideal X D)
    (retained_presentation_cone_homogeneous X D)
    (retained_presentation_cone_dimension X D d hdim)
  obtain ⟨a, ha, hb⟩ := (hf.inter (a3r_generic_iInter_fintype U hU)).nonempty
  refine ⟨a3r_mat a, ha, ?_⟩
  intro P hP hj hforms
  obtain ⟨j, hj⟩ := hj
  have h := hb j P hP hj (fun i => by
    simpa [a3r_lin_X, a3r_mat, S, MvPolynomial.algebraMap_eq] using hforms i)
  simpa [S, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card] using h

end HodgeLean.Foundations.QuotientDuality
