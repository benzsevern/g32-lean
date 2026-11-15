import HodgeLean.Foundations.AnalyticDivisorAlgebraic9Proofs

/-! # Resultant handoff for clean hypersurface loci: frozen specification

This stage isolates the algebraic core of the resultant route to clean regular points. Coprime
polynomials over the analytic-germ domain have nonzero resultant; after specialization over a
field, a common root is impossible. Applying the same fact to a polynomial and its derivative
gives the discriminant obstruction to singular fibers.

The analytic density bridge and the resulting clean-locus closure are also frozen here. The
representative-level compatibility and nearby-point locality needed to apply the construction
after translating away from the origin remain future work.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic9

open Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7

/-- A nonzero analytic germ has nonvanishing points in every neighborhood of the origin.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II--III, identity
theorem. -/
theorem spec_zero_mem_closure_ne_zero {n : ℕ}
    (h : (Fin n → ℂ) → ℂ) (hh : AnalyticAt ℂ h 0)
    (hnz : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) h, ⟨h, hh, rfl⟩⟩ :
      AnalyticGerm n) ≠ 0) :
    (0 : Fin n → ℂ) ∈ closure {x | h x ≠ 0} :=
  spec_zero_mem_closure_ne_zero_aux h hh hnz

/-- The nonvanishing loci of two nonzero analytic germs meet arbitrarily near the origin.
Source: Gunning--Rossi, II--III, applied to the product germ. -/
theorem spec_zero_mem_closure_two_ne_zero {n : ℕ}
    (h₁ h₂ : (Fin n → ℂ) → ℂ) (hh₁ : AnalyticAt ℂ h₁ 0)
    (hh₂ : AnalyticAt ℂ h₂ 0)
    (hnz₁ : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) h₁, ⟨h₁, hh₁, rfl⟩⟩ :
      AnalyticGerm n) ≠ 0)
    (hnz₂ : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) h₂, ⟨h₂, hh₂, rfl⟩⟩ :
      AnalyticGerm n) ≠ 0) :
    (0 : Fin n → ℂ) ∈ closure {x | h₁ x ≠ 0 ∧ h₂ x ≠ 0} :=
  spec_zero_mem_closure_two_ne_zero_aux h₁ h₂ hh₁ hh₂ hnz₁ hnz₂

/-- Weierstrass division transfers coprimality with a germ to the polynomial remainder, whose
resultant with the divisor polynomial is therefore nonzero.
Source: de Jong--Pfister, *Local Analytic Geometry*, Ch. 3--4. -/
theorem spec_weierstrass_resultant_ne_zero {n : ℕ}
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) (P : Polynomial (AnalyticGerm n))
    (hP : IsWeierstrassPolynomial P) (g : AnalyticGerm (n + 1))
    (hPg : IsCoprime (ι P) g) :
    ∃ (q : AnalyticGerm (n + 1)) (r : Polynomial (AnalyticGerm n)),
      g = q * ι P + ι r ∧ r.natDegree < P.natDegree ∧
        IsCoprime P r ∧ P.resultant r ≠ 0 :=
  spec_weierstrass_resultant_ne_zero_aux ι hι P hP g hPg

/-- Nonvanishing of the specialized resultant rules out a common root in that fiber.
Source: de Jong--Pfister, Ch. 3, specialization of the resultant and Bézout criterion. -/
theorem spec_resultant_specialization_avoids_common_root {n : ℕ}
    (P g : Polynomial (AnalyticGerm n))
    (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : U ∈ nhds (0 : Fin n → ℂ))
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hb : ∀ j, AnalyticOnNhd ℂ (b j) U) (hR : AnalyticOnNhd ℂ R U)
    (haP : ∀ j, (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j),
      ⟨a j, ha j 0 (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGerm n) =
        P.coeff j)
    (hbg : ∀ j, (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j),
      ⟨b j, hb j 0 (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGerm n) =
        g.coeff j)
    (hRR : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R,
      ⟨R, hR 0 (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGerm n) =
        P.resultant g)
    (hfibre : ∀ x ∈ U, P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0)
    (hcompat : ∀ x ∈ U, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
      (g.sum fun j _ ↦ monomial j (b j x)))
    (x : Fin n → ℂ) (hxU : x ∈ U) (hx : R x ≠ 0) (w : ℂ) :
    (P.sum fun j _ ↦ monomial j (a j x)).eval w ≠ 0 ∨
      (g.sum fun j _ ↦ monomial j (b j x)).eval w ≠ 0 :=
  spec_resultant_specialization_avoids_common_root_aux P g a b R U hU ha hb hR haP hbg hRR
    hfibre hcompat x hxU hx w

/-- At a fiber where the discriminant is nonzero, every root is simple.
Source: de Jong--Pfister, Ch. 3--4, discriminant criterion. -/
theorem spec_discriminant_specialization_simple_root {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (a : ℕ → (Fin n → ℂ) → ℂ)
    (D : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (hU : U ∈ nhds (0 : Fin n → ℂ)) (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hD : AnalyticOnNhd ℂ D U)
    (haP : ∀ j, (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j),
      ⟨a j, ha j 0 (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGerm n) =
        P.coeff j)
    (hDD : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D,
      ⟨D, hD 0 (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGerm n) = P.discr)
    (hfibre : ∀ x ∈ U, P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0)
    (hcompat : ∀ x ∈ U, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr)
    (x : Fin n → ℂ) (hxU : x ∈ U) (hx : D x ≠ 0)
    (w : ℂ) (hw : (P.sum fun j _ ↦ monomial j (a j x)).eval w = 0) :
    (P.sum fun j _ ↦ monomial j (a j x)).derivative.eval w ≠ 0 :=
  spec_discriminant_specialization_simple_root_aux P a D U hU ha hD haP hDD hfibre hcompat
    x hxU hx w hw

/-- Every irreducible factor has clean regular points, avoiding all other pairwise-coprime
factors, arbitrarily close to the origin.
Source: Gunning--Rossi, Ch. III; Chirka, §§2--5, regular locus and proper analytic subsets. -/
theorem spec_zero_mem_closure_clean_regular_factor {n k : ℕ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0)) (i : Fin k) :
    (0 : (Fin n → ℂ) × ℂ) ∈ closure
      {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0} :=
  spec_zero_mem_closure_clean_regular_factor_aux hP hcP i

/-- Coprime polynomials over a domain have nonzero resultant.
Source: de Jong--Pfister, *Local Analytic Geometry*, Ch. 3, resultant criterion. -/
theorem spec_resultant_ne_zero_of_isCoprime {R : Type*} [CommRing R] [IsDomain R]
    (P g : R[X]) (hPg : IsCoprime P g) : P.resultant g ≠ 0 :=
  spec_resultant_ne_zero_of_isCoprime_aux P g hPg

/-- Two coprime polynomials over a field cannot vanish at the same point.
Source: de Jong--Pfister, *Local Analytic Geometry*, Ch. 3, Bézout identity. -/
theorem spec_resultant_avoids_common_root {K : Type*} [Field K]
    (P g : K[X]) (hPg : IsCoprime P g) (w : K) : P.eval w ≠ 0 ∨ g.eval w ≠ 0 :=
  spec_resultant_avoids_common_root_aux P g hPg w

/-- A monic positive-degree polynomial coprime to its derivative has nonzero discriminant.
Source: de Jong--Pfister, *Local Analytic Geometry*, Ch. 3; the discriminant-resultant formula. -/
theorem spec_discr_ne_zero_of_isCoprime_derivative {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] (P : R[X]) (hP : P.Monic)
    (hdeg : 0 < P.natDegree) (hsep : IsCoprime P P.derivative) : P.discr ≠ 0 :=
  spec_discr_ne_zero_of_isCoprime_derivative_aux P hP hdeg hsep

/-- For the degree-one polynomial `X`, the resultant is evaluation at zero.
Source: de Jong--Pfister, *Local Analytic Geometry*, Ch. 3, degree-one resultant. -/
theorem spec_resultant_X_eq_eval_zero {R : Type*} [CommRing R] (g : R[X]) :
    resultant X g 1 g.natDegree = g.eval 0 := spec_resultant_X_eq_eval_zero_aux g

/-- A polynomial of positive degree has zero resultant with each of its multiples.
Source: de Jong--Pfister, *Local Analytic Geometry*, Ch. 3, multiplicativity of resultants. -/
theorem spec_resultant_self_zero_excluded {R : Type*} [Field R]
    (P h : R[X]) (hdeg : P.natDegree ≠ 0) : P.resultant (P * h) = 0 :=
  spec_resultant_self_zero_excluded_aux P h hdeg

/-- Associated nonunits are not coprime, so duplicate components are excluded by coprimality.
Source: Gunning--Rossi, II.B, Definition 1. -/
theorem spec_associated_non_coprime {R : Type*} [CommRing R] [IsDomain R]
    (P Q : R[X]) (hP : ¬ IsUnit P) (hPQ : Associated P Q) : ¬ IsCoprime P Q :=
  spec_associated_non_coprime_aux P Q hP hPQ

-- Degenerate checks for the newly frozen germ-level statements.
-- The old specialization statements were false on zero fibres: all their old premises hold,
-- while their respective root conclusions fail.
example :
    let P : Polynomial (AnalyticGerm 0) := 0
    let g : Polynomial (AnalyticGerm 0) := 0
    let a : ℕ → (Fin 0 → ℂ) → ℂ := fun _ _ ↦ 0
    let b : ℕ → (Fin 0 → ℂ) → ℂ := fun _ _ ↦ 0
    let R : (Fin 0 → ℂ) → ℂ := fun _ ↦ 1
    Set.univ ∈ nhds (0 : Fin 0 → ℂ) ∧
      (∀ j, AnalyticOnNhd ℂ (a j) Set.univ) ∧
      (∀ j, AnalyticOnNhd ℂ (b j) Set.univ) ∧
      AnalyticOnNhd ℂ R Set.univ ∧
      (∀ j, (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (a j),
        ⟨a j, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = P.coeff j) ∧
      (∀ j, (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (b j),
        ⟨b j, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = g.coeff j) ∧
      (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) R,
        ⟨R, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = P.resultant g ∧
      (∀ x ∈ Set.univ, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
        (g.sum fun j _ ↦ monomial j (b j x))) ∧
      R 0 ≠ 0 ∧
      ¬ ((P.sum fun j _ ↦ monomial j (a j 0)).eval 0 ≠ 0 ∨
        (g.sum fun j _ ↦ monomial j (b j 0)).eval 0 ≠ 0) := by
  dsimp
  have hz : AnalyticOnNhd ℂ (fun _ : (Fin 0 → ℂ) ↦ (0 : ℂ)) Set.univ :=
    fun _ _ ↦ by fun_prop
  have ho : AnalyticOnNhd ℂ (fun _ : (Fin 0 → ℂ) ↦ (1 : ℂ)) Set.univ :=
    fun _ _ ↦ by fun_prop
  have hgz : (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ 0),
      ⟨_, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = 0 := by
    apply Subtype.ext
    apply Filter.EventuallyEq.germ_eq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hgo : (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ 1),
      ⟨_, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = 1 := by
    apply Subtype.ext
    apply Filter.EventuallyEq.germ_eq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  refine ⟨Filter.univ_mem, fun _ ↦ hz, fun _ ↦ hz, ho, ?_, ?_, ?_, ?_, by simp, by simp⟩
  · intro j
    simpa using hgz
  · intro j
    simpa using hgz
  · simpa using hgo
  · intro x hx
    simp

example :
    let P : Polynomial (AnalyticGerm 0) := 0
    let a : ℕ → (Fin 0 → ℂ) → ℂ := fun _ _ ↦ 0
    let D : (Fin 0 → ℂ) → ℂ := fun _ ↦ 1
    Set.univ ∈ nhds (0 : Fin 0 → ℂ) ∧
      (∀ j, AnalyticOnNhd ℂ (a j) Set.univ) ∧ AnalyticOnNhd ℂ D Set.univ ∧
      (∀ j, (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (a j),
        ⟨a j, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = P.coeff j) ∧
      (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) D,
        ⟨D, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = P.discr ∧
      (∀ x ∈ Set.univ, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr) ∧
      D 0 ≠ 0 ∧ (P.sum fun j _ ↦ monomial j (a j 0)).eval 0 = 0 ∧
      ¬ (P.sum fun j _ ↦ monomial j (a j 0)).derivative.eval 0 ≠ 0 := by
  dsimp
  have hz : AnalyticOnNhd ℂ (fun _ : (Fin 0 → ℂ) ↦ (0 : ℂ)) Set.univ :=
    fun _ _ ↦ by fun_prop
  have ho : AnalyticOnNhd ℂ (fun _ : (Fin 0 → ℂ) ↦ (1 : ℂ)) Set.univ :=
    fun _ _ ↦ by fun_prop
  have hgz : (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ 0),
      ⟨_, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = 0 := by
    apply Subtype.ext
    apply Filter.EventuallyEq.germ_eq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hgo : (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ 1),
      ⟨_, (by fun_prop), rfl⟩⟩ : AnalyticGerm 0) = 1 := by
    apply Subtype.ext
    apply Filter.EventuallyEq.germ_eq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  refine ⟨Filter.univ_mem, fun _ ↦ hz, ho, ?_, ?_, ?_, by simp, by simp, by simp⟩
  · intro j
    simpa using hgz
  · rw [show (0 : Polynomial (AnalyticGerm 0)).discr = 1 by
      simpa only [← C_0, discr_C]]
    exact hgo
  · intro x hx
    change 1 = (0 : ℂ[X]).discr
    simpa only [← C_0, discr_C]

example (h : (Fin 0 → ℂ) → ℂ) (hh : AnalyticAt ℂ h 0)
    (hnz : (⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) h, ⟨h, hh, rfl⟩⟩ :
      AnalyticGerm 0) ≠ 0) :
    (0 : Fin 0 → ℂ) ∈ closure {x | h x ≠ 0} :=
  spec_zero_mem_closure_ne_zero h hh hnz

example : (X : ℂ[X]).resultant 1 ≠ 0 := by
  exact spec_resultant_ne_zero_of_isCoprime X 1 isCoprime_one_right

example (w : ℂ) : (X : ℂ[X]).eval w ≠ 0 ∨ (1 : ℂ[X]).eval w ≠ 0 := by
  exact spec_resultant_avoids_common_root X 1 isCoprime_one_right w

example : (X : ℂ[X]).discr ≠ 0 := by
  apply spec_discr_ne_zero_of_isCoprime_derivative X monic_X
  · simp
  · simpa only [derivative_X] using
      (isCoprime_one_right : IsCoprime (X : ℂ[X]) 1)

example : (X : ℂ[X]).resultant (X * (X + 1)) = 0 := by
  exact spec_resultant_self_zero_excluded X (X + 1) (by simp)

example : ¬ IsCoprime (X : ℂ[X]) X := by
  apply spec_associated_non_coprime X X
  · exact not_isUnit_of_natDegree_pos X (by simp)
  · exact Associated.rfl

end HodgeLean.Foundations.AnalyticDivisorAlgebraic9
