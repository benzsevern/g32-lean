import HodgeLean.Foundations.AnalyticDivisorAlgebraic10Proofs

/-! # Representative-level neighbourhood compatibility: frozen specification

This stage chooses coefficient representatives simultaneously and records fixed-degree resultant
compatibility, including fibres whose degree drops. It freezes the implication from a monic germ
polynomial to analytic resultant and discriminant representatives, and from their fibrewise
nonvanishing to absence of common roots and simplicity of roots. It does not claim nearby-point
locality or a sheaf-level algebraization statement.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic10

open Filter Polynomial Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- The finitely many nonzero coefficients of two germ polynomials have analytic representatives
on one neighbourhood of the origin. Source: Gunning--Rossi, *Analytic Functions of Several
Complex Variables*, II.B, Definition 1, and closure of neighbourhoods under finite intersection. -/
theorem spec_simultaneous_coefficient_representatives {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) :=
  spec_simultaneous_coefficient_representatives_aux P g

/-- Padding the second Sylvester degree does not change a resultant when the first polynomial is
monic. Thus a drop in the degree of a specialized second polynomial does not change the
fixed-degree value. Source: Bourbaki, *Algebra*, Ch. IV, §6, Sylvester determinant. -/
theorem spec_resultant_fixed_degree_of_monic {R : Type*} [CommRing R]
    (P g : Polynomial R) (hP : P.Monic) (N : ℕ) (hg : g.natDegree ≤ N) :
    P.resultant g P.natDegree N = P.resultant g :=
  spec_resultant_fixed_degree_of_monic_aux P g hP N hg

/-- A fibre with leading coefficient one is nonzero, including in degree zero.
Source: Bourbaki, *Algebra*, Ch. IV, §1, polynomial coefficients. -/
theorem spec_monic_fibre_ne_zero {n : ℕ} (P : Polynomial (AnalyticGerm n))
    (hP : P.Monic) (a : ℕ → (Fin n → ℂ) → ℂ)
    (x : Fin n → ℂ) (hlead : a P.natDegree x = 1) :
    P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0 :=
  spec_monic_fibre_ne_zero_aux P hP a x hlead

/-- The fixed-size Sylvester determinant of analytic coefficient representatives is analytic.
Source: Bourbaki, *Algebra*, Ch. III, §8 and Ch. IV, §6: a determinant is a finite polynomial
expression in its matrix entries. -/
theorem spec_fixed_degree_resultant_analytic {n m N : ℕ}
    (P g : Polynomial (AnalyticGerm n))
    (a b : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hb : ∀ j, AnalyticOnNhd ℂ (b j) U) :
    AnalyticOnNhd ℂ (fun x ↦
      (P.sum fun j _ ↦ monomial j (a j x)).resultant
        (g.sum fun j _ ↦ monomial j (b j x)) m N) U :=
  spec_fixed_degree_resultant_analytic_aux P g a b U ha hb

/-- A monic germ polynomial and a second germ polynomial have simultaneous coefficient
representatives on a common neighbourhood whose fibre resultants form an analytic representative
of their germ resultant. Source: Bourbaki, *Algebra*, Ch. IV, §6, functoriality of the Sylvester
determinant. -/
theorem spec_resultant_representative {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      AnalyticOnNhd ℂ R U ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R = (P.resultant g).1 ∧
      (∀ x ∈ U, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
        (g.sum fun j _ ↦ monomial j (b j x))) ∧
      (∀ x ∈ U, P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0) :=
  spec_resultant_representative_aux P g hP

/-- A monic germ polynomial has coefficient representatives on a common neighbourhood whose
fibre discriminants form an analytic representative of its germ discriminant. Source: Bourbaki,
*Algebra*, Ch. IV, §6, the discriminant--resultant formula. -/
theorem spec_discriminant_representative {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧ (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      AnalyticOnNhd ℂ D U ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D = P.discr.1 ∧
      (∀ x ∈ U, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr) ∧
      (∀ x ∈ U, P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0) :=
  spec_discriminant_representative_aux P hP

/-- On the common representative neighbourhood, nonvanishing of the resultant representative
rules out a common fibre root. Source: de Jong--Pfister, *Local Analytic Geometry*, Ch. 3,
specialization of the resultant and the Bézout criterion. -/
theorem spec_resultant_nonzero_fibre_avoids_common_root {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧ AnalyticOnNhd ℂ R U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R = (P.resultant g).1 ∧
      ∀ x ∈ U, R x ≠ 0 → ∀ w : ℂ,
        (P.sum fun j _ ↦ monomial j (a j x)).eval w ≠ 0 ∨
          (g.sum fun j _ ↦ monomial j (b j x)).eval w ≠ 0 :=
  spec_resultant_nonzero_fibre_avoids_common_root_aux P g hP

/-- On the common representative neighbourhood, nonvanishing of the discriminant representative
makes every fibre root simple. Source: de Jong--Pfister, *Local Analytic Geometry*, Ch. 3--4,
the discriminant criterion. -/
theorem spec_discriminant_nonzero_fibre_simple_roots {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧ AnalyticOnNhd ℂ D U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D = P.discr.1 ∧
      ∀ x ∈ U, D x ≠ 0 → ∀ w : ℂ,
        (P.sum fun j _ ↦ monomial j (a j x)).eval w = 0 →
          (P.sum fun j _ ↦ monomial j (a j x)).derivative.eval w ≠ 0 :=
  spec_discriminant_nonzero_fibre_simple_roots_aux P hP

-- Degenerate convention checks used when freezing the statements above.
example : ((0 : ℂ[X]).resultant 0) = 1 := by simp

example : (0 : ℂ[X]).discr = 1 := by simpa only [← C_0, discr_C]

example : (X : ℂ[X]).discr = 1 := by
  apply discr_of_degree_eq_one
  simp

example : (X : ℂ[X]).resultant 1 (X : ℂ[X]).natDegree (1 : ℂ[X]).natDegree = 1 := by simp

example : (∏ i ∈ (∅ : Finset ℕ), (i : ℂ)) = 1 := by simp

example : Set.univ ∈ nhds (0 : Fin 0 → ℂ) := Filter.univ_mem

example (g : ℂ[X]) : (X : ℂ[X]).resultant g 1 g.natDegree = g.eval 0 :=
  AnalyticDivisorAlgebraic9.spec_resultant_X_eq_eval_zero g

example : (X : ℂ[X]).resultant 1 = 1 := by simp

example (P g : ℂ[X]) (N : ℕ) (hg : g.natDegree ≤ N) (hP : P.Monic) :
    P.resultant g P.natDegree N = P.resultant g :=
  spec_resultant_fixed_degree_of_monic P g hP N hg

example {n : ℕ} (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ),
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      ∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1 := by
  obtain ⟨a, b, _R, _U, _hU, _hR, _ha, _hb, haP, hbg, _hRR, _hroot⟩ :=
    spec_resultant_nonzero_fibre_avoids_common_root P g hP
  exact ⟨a, b, haP, hbg⟩

example {n : ℕ} (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ),
      ∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1 := by
  obtain ⟨a, _D, _U, _hU, _hD, _ha, haP, _hDD, _hroot⟩ :=
    spec_discriminant_nonzero_fibre_simple_roots P hP
  exact ⟨a, haP⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic10
