import HodgeLean.Foundations.Program.SchoenCycleCoefficientCharts

/-! # The marked-root equation in the affine symmetric model -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Distinct root variables dividing a polynomial divide it jointly with multiplicity one.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1, prime elements. -/
theorem s2e_root_product_dvd
    (σ : Type) (s : Finset σ) (f : MvPolynomial σ ℂ)
    (h : ∀ i ∈ s, (X i : MvPolynomial σ ℂ) ∣ f) :
    (∏ i ∈ s, (X i : MvPolynomial σ ℂ)) ∣ f := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simpa only [Finset.prod_empty] using one_dvd f
  | @insert a s ha ih =>
    obtain ⟨q, rfl⟩ := h a (Finset.mem_insert_self a s)
    have hq (i : σ) (hi : i ∈ s) : (X i : MvPolynomial σ ℂ) ∣ q := by
      have hd := h i (Finset.mem_insert_of_mem hi)
      rcases (MvPolynomial.X_prime (R := ℂ) (i := i)).dvd_mul.mp hd with hd | hd
      · exact (ha ((X_dvd_X.mp hd) ▸ hi)).elim
      · exact hd
    obtain ⟨r, hr⟩ := ih q hq
    refine ⟨r, ?_⟩
    rw [Finset.prod_insert ha, hr, mul_assoc]

/-- A symmetric polynomial divisible by one root coordinate is divisible by their product
inside the symmetric subalgebra.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, symmetric products and divisors. -/
theorem s2e_symmetric_marked_root_divisible
    (σ : Type) [Fintype σ] (p : symmetricSubalgebra σ ℂ) (i : σ)
    (hi : (X i : MvPolynomial σ ℂ) ∣ (p : MvPolynomial σ ℂ)) :
    (⟨esymm σ ℂ (Fintype.card σ), esymm_isSymmetric σ ℂ _⟩ :
      symmetricSubalgebra σ ℂ) ∣ p := by
  classical
  have hall (j : σ) : (X j : MvPolynomial σ ℂ) ∣ (p : MvPolynomial σ ℂ) := by
    have hj := map_dvd (MvPolynomial.rename (Equiv.swap i j)).toRingHom hi
    change rename (Equiv.swap i j) (X i) ∣ rename (Equiv.swap i j) (p : MvPolynomial σ ℂ) at hj
    simpa only [rename_X, Equiv.swap_apply_left, p.property (Equiv.swap i j)] using hj
  obtain ⟨q, hq⟩ := s2e_root_product_dvd σ Finset.univ (p : MvPolynomial σ ℂ)
    (fun j _ => hall j)
  have hs : IsSymmetric (∏ j : σ, (X j : MvPolynomial σ ℂ)) := by
    rw [← s2e_top_elementary_coefficient σ ℂ]
    exact esymm_isSymmetric σ ℂ _
  have hqn : IsSymmetric q := by
    intro e
    apply mul_left_cancel₀ (show (∏ j : σ, (X j : MvPolynomial σ ℂ)) ≠ 0 from
      Finset.prod_ne_zero_iff.mpr (fun j _ => X_ne_zero j))
    calc
      (∏ j : σ, (X j : MvPolynomial σ ℂ)) * rename e q =
          rename e ((∏ j : σ, (X j : MvPolynomial σ ℂ)) * q) := by rw [map_mul, hs e]
      _ = rename e (p : MvPolynomial σ ℂ) := by rw [← hq]
      _ = (p : MvPolynomial σ ℂ) := p.property e
      _ = (∏ j : σ, (X j : MvPolynomial σ ℂ)) * q := hq
  refine ⟨⟨q, hqn⟩, ?_⟩
  apply Subtype.ext
  change (p : MvPolynomial σ ℂ) = esymm σ ℂ (Fintype.card σ) * q
  rw [s2e_top_elementary_coefficient]
  exact hq

/-- Contracting a root hyperplane to the symmetric ring gives the top coefficient ideal.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, symmetric products and divisors. -/
theorem s2e_symmetric_marked_root_ideal
    (σ : Type) [Fintype σ] (i : σ) :
    (Ideal.span {(X i : MvPolynomial σ ℂ)}).comap
      (symmetricSubalgebra σ ℂ).val.toRingHom =
    Ideal.span {(⟨esymm σ ℂ (Fintype.card σ), esymm_isSymmetric σ ℂ _⟩ :
      symmetricSubalgebra σ ℂ)} := by
  classical
  ext p
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · exact s2e_symmetric_marked_root_divisible σ p i
  · intro h
    have hm := map_dvd (symmetricSubalgebra σ ℂ).val.toRingHom h
    change esymm σ ℂ (Fintype.card σ) ∣ (p : MvPolynomial σ ℂ) at hm
    have hx : (X i : MvPolynomial σ ℂ) ∣ esymm σ ℂ (Fintype.card σ) := by
      rw [s2e_top_elementary_coefficient]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    exact hx.trans hm

/-- The monic root polynomial has signed top elementary coefficient as its constant term.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, symmetric products and divisors. -/
theorem s2e_marked_root_constant_coefficient
    (σ : Type) [Fintype σ] :
    (∏ i : σ, (Polynomial.X - Polynomial.C (X i : MvPolynomial σ ℂ))).coeff 0 =
      (-1 : MvPolynomial σ ℂ) ^ Fintype.card σ * esymm σ ℂ (Fintype.card σ) := by
  classical
  simp only [Polynomial.coeff_zero_prod, Polynomial.coeff_sub,
    Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub]
  rw [Finset.prod_neg, Finset.card_univ, ← s2e_top_elementary_coefficient σ ℂ]

end HodgeLean.Foundations.Program
