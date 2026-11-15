import HodgeLean.Foundations.AnalyticDivisorAlgebraic11Proofs

/-! # Nearby-point translation of analytic germs: frozen specification

This stage freezes translation of analytic germs, coefficientwise translation of polynomials,
and restriction of representatives to translated neighbourhoods. It does not transport the
stage-ten resultant or discriminant identities or their clean-root consequences.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic11

open Filter Polynomial Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- Translation by `p` identifies analytic germs at `p` with analytic germs at zero, carries a
representative `f` to `z ↦ f (p + z)`, and preserves evaluation. Source: Gunning--Rossi,
*Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
theorem spec_germ_translation_equiv (n : ℕ) (p : Fin n → ℂ) :
    ∃ e : AnalyticGermAt n p ≃+* AnalyticGerm n,
      (∀ g : AnalyticGermAt n p,
        analyticGermValue n (e g) = analyticGermAtValue n p g) ∧
      ∀ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
          (ht : AnalyticAt ℂ (fun z ↦ f (p + z)) 0),
        e ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z)),
            ⟨fun z ↦ f (p + z), ht, rfl⟩⟩ :=
  spec_germ_translation_equiv_aux n p

/-- At `p = 0`, the translation equivalence acts as the identity on underlying germs.
Source: Gunning--Rossi, II.B, Definition 1. -/
theorem spec_germ_translation_zero (n : ℕ) :
    ∃ e : AnalyticGermAt n 0 ≃+* AnalyticGerm n,
      ∀ g : AnalyticGermAt n 0, (e g).1 = g.1 :=
  spec_germ_translation_zero_aux n

/-- Polynomial translation is coefficientwise. Source: Bourbaki, *Algebra*, Ch. IV, §1. -/
theorem spec_polynomial_translation_coeff {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Polynomial R) (j : ℕ) :
    (P.map e.toRingHom).coeff j = e (P.coeff j) :=
  spec_polynomial_translation_coeff_aux e P j

/-- Coefficient translation through a ring equivalence preserves monicity and degree, including
constant and zero polynomials. Source: Bourbaki, *Algebra*, Ch. IV, §1. -/
theorem spec_polynomial_translation_monic_degree {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Polynomial R) :
    ((P.map e.toRingHom).Monic ↔ P.Monic) ∧
      (P.map e.toRingHom).natDegree = P.natDegree :=
  spec_polynomial_translation_monic_degree_aux e P

/-- Coefficient translation preserves polynomial coprimality. Source: Bourbaki, *Algebra*,
Ch. IV, §1. -/
theorem spec_polynomial_translation_coprime {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P Q : Polynomial R) :
    IsCoprime (P.map e.toRingHom) (Q.map e.toRingHom) ↔ IsCoprime P Q :=
  spec_polynomial_translation_coprime_aux e P Q

/-- Coefficient translation preserves polynomial irreducibility. Source: Bourbaki, *Algebra*,
Ch. IV, §1. -/
theorem spec_polynomial_translation_irreducible {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Polynomial R) :
    Irreducible (P.map e.toRingHom) ↔ Irreducible P :=
  spec_polynomial_translation_irreducible_aux e P

/-- Translation preserves units, including zero-dimensional base germs. Source: Gunning--Rossi,
II.B, Definition 1. -/
theorem spec_polynomial_translation_units {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : R) : IsUnit (e x) ↔ IsUnit x :=
  spec_polynomial_translation_units_aux e x

/-- At the origin, the pointwise Weierstrass predicate agrees with the stage-seven predicate
under the translation equivalence. -/
example (n : ℕ) : ∃ e : AnalyticGermAt n 0 ≃+* AnalyticGerm n,
    ∀ P : Polynomial (AnalyticGermAt n 0),
      IsWeierstrassPolynomialAt P ↔ IsWeierstrassPolynomial (P.map e.toRingHom) := by
  obtain ⟨e, hvalue, -⟩ := spec_germ_translation_equiv n 0
  refine ⟨e, fun P ↦ ?_⟩
  rw [IsWeierstrassPolynomialAt, IsWeierstrassPolynomial]
  have hdegree := spec_polynomial_translation_monic_degree e P
  constructor
  · rintro ⟨hmonic, hpositive, hcoeff⟩
    refine ⟨hdegree.1.mpr hmonic, hdegree.2.symm ▸ hpositive, ?_⟩
    intro j hj
    change analyticGermValue n ((P.map e.toRingHom).coeff j) = 0
    rw [spec_polynomial_translation_coeff, hvalue]
    exact hcoeff j (by rwa [hdegree.2] at hj)
  · rintro ⟨hmonic, hpositive, hcoeff⟩
    refine ⟨hdegree.1.mp hmonic, hdegree.2 ▸ hpositive, ?_⟩
    intro j hj
    have hc := hcoeff j (by rw [hdegree.2]; exact hj)
    change analyticGermValue n ((P.map e.toRingHom).coeff j) = 0 at hc
    rw [spec_polynomial_translation_coeff, hvalue] at hc
    exact hc

/-- An analytic representative on a neighbourhood of `p` restricts to its translate on a
neighbourhood of zero, with the pointwise fibre identity unchanged. Source: Gunning--Rossi,
II.B, Definition 1. -/
theorem spec_translated_representative {n : ℕ} (p : Fin n → ℂ)
    (f : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (hp : p ∈ U) (hU : U ∈ nhds p) (hf : AnalyticOnNhd ℂ f U) :
    gaga11_translatedSet p U ∈ nhds (0 : Fin n → ℂ) ∧
      AnalyticOnNhd ℂ (fun z ↦ f (p + z)) (gaga11_translatedSet p U) ∧
      ∀ z ∈ gaga11_translatedSet p U, (fun y ↦ f (p + y)) z = f (p + z) :=
  spec_translated_representative_aux p f U hp hU hf

/-- Two simultaneous coefficient families define coefficient polynomials over the germ ring at
`p`. Translation carries each coefficient used by the original finite supports to the germ at
zero of the corresponding translated representative. Source: Gunning--Rossi, II.B,
Definition 1; Bourbaki, *Algebra*, Ch. IV, §1. -/
theorem spec_simultaneous_representatives_translate {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (a b : ℕ → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (p : Fin n → ℂ) (hUp : U ∈ nhds p)
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U) (hb : ∀ j, AnalyticOnNhd ℂ (b j) U) :
    ∃ (e : AnalyticGermAt n p ≃+* AnalyticGerm n)
        (A B : Polynomial (AnalyticGermAt n p)),
      A = P.sum (fun j _ ↦ monomial j
        ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j),
          ⟨a j, ha j p (mem_of_mem_nhds hUp), rfl⟩⟩) ∧
      B = g.sum (fun j _ ↦ monomial j
        ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (b j),
          ⟨b j, hb j p (mem_of_mem_nhds hUp), rfl⟩⟩) ∧
      (∀ j ∈ P.support, (e (A.coeff j)).1 =
        @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ a j (p + z))) ∧
      (∀ j ∈ g.support, (e (B.coeff j)).1 =
        @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ b j (p + z))) :=
  spec_simultaneous_representatives_translate_aux P g a b U p hUp ha hb

/-- The explicit monic polynomial `X + z₀` is Weierstrass at the origin but fails to be
Weierstrass at nonzero points arbitrarily close to it. Thus base translation alone does not
preserve the Weierstrass condition. Source: Gunning--Rossi, II.B, Definition 2. -/
theorem spec_weierstrass_translation_falsification : ∀ ε : ℝ, 0 < ε →
    ∃ p : Fin 1 → ℂ, ‖p‖ < ε ∧
      IsWeierstrassPolynomialAt
        (X + C (gaga11_coordinateGermAt 0) : Polynomial (AnalyticGermAt 1 0)) ∧
      ¬ IsWeierstrassPolynomialAt
        (X + C (gaga11_coordinateGermAt p) : Polynomial (AnalyticGermAt 1 p)) :=
  spec_weierstrass_translation_falsification_aux

-- Degenerate convention checks used when freezing the statements above.
example : gaga11_translatedSet (0 : Fin 0 → ℂ) Set.univ = Set.univ := by rfl
example : ((0 : ℂ[X]).map (RingHom.id ℂ)) = 0 := by simp
example : ((1 : ℂ[X]).map (RingHom.id ℂ)) = 1 := by simp
example (c : ℂ) : ((C c).map (RingHom.id ℂ)) = C c := by simp
example : (∏ i ∈ (∅ : Finset ℕ), (i : ℂ)) = 1 := by simp
example : IsUnit (1 : ℂ) := isUnit_one
example : ¬ IsUnit (0 : ℂ) := not_isUnit_zero

end HodgeLean.Foundations.AnalyticDivisorAlgebraic11
