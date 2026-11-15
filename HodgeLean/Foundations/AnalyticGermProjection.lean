import HodgeLean.Foundations.AnalyticGermProjectionProofs

/-! # Finite projection: frozen first primitives

Implication from Weierstrass preparation to finite maps of analytic quotient rings,
and from an analytic distinguished polynomial family to a proper surjective
projection with finite fibres on actual neighbourhoods. Prime normalization,
Krull dimension comparison and point extension remain deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- Source: Gunning--Rossi, II.B and III.B, division and finite hypersurface projection. -/
theorem adim4_prepared_finite (n : ℕ)
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) (P : Polynomial (AnalyticGerm n))
    (hP : IsWeierstrassPolynomial P) :
    ((Ideal.Quotient.mk (Ideal.span {ι P})).comp (ι.comp C)).Finite ∧
      Function.Injective ((Ideal.Quotient.mk (Ideal.span {ι P})).comp (ι.comp C)) :=
  adim4_prepared_finite_aux n ι hι P hP

/-- Source: de Jong--Pfister, Local Analytic Geometry, Chapter 3, finite analytic algebras. -/
theorem adim4_contraction_finite (n : ℕ)
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) (P : Polynomial (AnalyticGerm n))
    (hP : IsWeierstrassPolynomial P) (I : Ideal (AnalyticGerm (n + 1)))
    (hI : ι P ∈ I) :
    (Ideal.quotientMap I (ι.comp C) (le_refl (I.comap (ι.comp C)))).Finite :=
  adim4_contraction_finite_aux n ι hι P hP I hI

/-- Source: Gunning--Rossi, III.B--C, distinguished polynomials and local projection;
Chirka, Complex Analytic Sets, §3, local parametrization. -/
theorem adim4_polynomial_projection (n k : ℕ) (hk : 0 < k)
    (a : Fin k → (Fin n → ℂ) → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ (0 : Fin n → ℂ) ∈ V ∧
      ∃ p : {z : (Fin n → ℂ) × ℂ //
        z.1 ∈ V ∧ ‖z.2‖ < r ∧ z.2 ^ k + ∑ i : Fin k, a i z.1 * z.2 ^ (i : ℕ) = 0} → V,
        (∀ z, (p z).val = z.val.1) ∧ IsProperMap p ∧ Function.Surjective p ∧
        (∀ w : V, (p ⁻¹' {w}).Finite) ∧
        ∀ z, (p z).val = 0 → z.val = (0, 0) :=
  adim4_polynomial_projection_aux n k hk a ha ha0 r hr


/-- W1: preparation of the coordinate supplies every input of the finite hypersurface map.
Source: Gunning--Rossi, II.B, preparation of a coordinate. -/
example : ∃ (ι : Polynomial (AnalyticGerm 1) →+* AnalyticGerm 2)
    (P : Polynomial (AnalyticGerm 1)),
    IsWeierstrassEmbedding ι ∧ IsWeierstrassPolynomial P ∧
    ((Ideal.Quotient.mk (Ideal.span {ι P})).comp (ι.comp C)).Finite ∧
    Function.Injective ((Ideal.Quotient.mk (Ideal.span {ι P})).comp (ι.comp C)) := by
  obtain ⟨ι, P, hι, hP, _⟩ :=
    spec_preparation_transfer (adim_coordinate_regular 1) (adim_coordinate_nonunit 1)
  exact ⟨ι, P, hι, hP, adim4_prepared_finite 1 ι hι P hP⟩

/-- W2: the prepared coordinate ideal gives a concrete contraction step.
Source: de Jong--Pfister, Chapter 3, quotients of finite analytic algebras. -/
example : ∃ (ι : Polynomial (AnalyticGerm 1) →+* AnalyticGerm 2)
    (P : Polynomial (AnalyticGerm 1)),
    IsWeierstrassEmbedding ι ∧ IsWeierstrassPolynomial P ∧
    (Ideal.quotientMap (Ideal.span {ι P}) (ι.comp C)
      (le_refl ((Ideal.span {ι P}).comap (ι.comp C)))).Finite := by
  obtain ⟨ι, P, hι, hP, _⟩ :=
    spec_preparation_transfer (adim_coordinate_regular 1) (adim_coordinate_nonunit 1)
  exact ⟨ι, P, hι, hP, adim4_contraction_finite 1 ι hι P hP
    (Ideal.span {ι P}) (Ideal.subset_span (by simp))⟩

/-- W3: the cusp has a proper surjective two-sheeted projection, with branching allowed.
Source: Chirka, Complex Analytic Sets, §3, singular plane curves. -/
example : ∃ V : Set (Fin 1 → ℂ), IsOpen V ∧ (0 : Fin 1 → ℂ) ∈ V ∧
    ∃ p : {z : (Fin 1 → ℂ) × ℂ //
      z.1 ∈ V ∧ ‖z.2‖ < 1 ∧ z.2 ^ 2 + ∑ i : Fin 2,
        (![fun x : Fin 1 → ℂ ↦ -(x 0) ^ 3, fun _ ↦ 0]) i z.1 * z.2 ^ (i : ℕ) = 0} → V,
      (∀ z, (p z).val = z.val.1) ∧ IsProperMap p ∧ Function.Surjective p ∧
      (∀ w : V, (p ⁻¹' {w}).Finite) ∧
      ∀ z, (p z).val = 0 → z.val = (0, 0) := by
  have ha : ∀ i : Fin 2, AnalyticAt ℂ
      ((![fun z : Fin 1 → ℂ ↦ -(z 0) ^ 3, fun _ ↦ 0]) i) 0 := by
    intro i
    fin_cases i
    · exact ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).pow 3 |>.neg
    · exact analyticAt_const
  have h := adim4_polynomial_projection 1 2 (by norm_num)
    (![fun z : Fin 1 → ℂ ↦ -(z 0) ^ 3, fun _ ↦ 0]) ha
    (by intro i; fin_cases i <;> simp) 1 (by norm_num)
  exact h

/-- The explicit coefficient family in W3 is the cusp equation.
Source: Chirka, Complex Analytic Sets, §3, singular plane curves. -/
example (z : (Fin 1 → ℂ) × ℂ) :
    z.2 ^ 2 + ∑ i : Fin 2,
      (![fun x : Fin 1 → ℂ ↦ -(x 0) ^ 3, fun _ ↦ 0]) i z.1 * z.2 ^ (i : ℕ) =
      z.2 ^ 2 - (z.1 0) ^ 3 := by
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- W4: a doubled point in one variable exercises the zero-dimensional base.
Source: Gunning--Rossi, III.B, finite fibres with multiplicity. -/
example : ∃ V : Set (Fin 0 → ℂ), IsOpen V ∧ (0 : Fin 0 → ℂ) ∈ V ∧
    ∃ p : {z : (Fin 0 → ℂ) × ℂ // z.1 ∈ V ∧ ‖z.2‖ < 1 ∧ z.2 ^ 2 + ∑ i : Fin 2, (0 : ℂ) * z.2 ^ (i : ℕ) = 0} → V,
      (∀ z, (p z).val = z.val.1) ∧ IsProperMap p ∧ Function.Surjective p ∧
      (∀ w : V, (p ⁻¹' {w}).Finite) ∧
      ∀ z, (p z).val = 0 → z.val = (0, 0) := by
  have h := adim4_polynomial_projection 0 2 (by norm_num)
    (fun _ _ ↦ 0) (fun _ ↦ analyticAt_const) (fun _ ↦ rfl) 1 (by norm_num)
  exact h

end HodgeLean.Foundations
