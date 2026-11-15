import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.OfFn

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finitely many nonzero polynomials over varying domains can be avoided
simultaneously along injective maps from an infinite parameter ring. -/
theorem s2_polynomial_simultaneous_avoidance
    (R : Type*) [CommRing R] [Infinite R]
    (ι : Type*) [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    (φ : ∀ i, R →+* B i) (hφ : ∀ i, Function.Injective (φ i))
    (p : ∀ i, Polynomial (B i)) (hp : ∀ i, p i ≠ 0) :
    ∃ t : R, ∀ i, (p i).eval (φ i t) ≠ 0 := by
  have hfin (i : ι) : Set.Finite {t : R | (p i).eval (φ i t) = 0} := by
    exact Set.Finite.preimage (hφ i).injOn (Polynomial.finite_setOfPred_isRoot (hp i))
  obtain ⟨t, ht⟩ := (Set.finite_iUnion hfin).exists_notMem
  refine ⟨t, ?_⟩
  intro i hi
  exact ht (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-- A single parameter makes finitely many power-weighted coefficient sums nonzero. -/
theorem s2_powerWeighted_sum_simultaneous_ne_zero
    (R : Type*) [CommRing R] [Infinite R]
    (ι : Type*) [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    (φ : ∀ i, R →+* B i) (hφ : ∀ i, Function.Injective (φ i))
    (n : ℕ) (c : ∀ i, Fin n → B i) (hc : ∀ i, ∃ j, c i j ≠ 0) :
    ∃ t : R, ∀ i, ∑ j : Fin n, c i j * (φ i t) ^ j.val ≠ 0 := by
  classical
  have hp (i : ι) : Polynomial.ofFn n (c i) ≠ 0 := by
    obtain ⟨j, hj⟩ := hc i
    intro hz
    have he := congrArg (fun p : Polynomial (B i) => p.coeff j.val) hz
    exact hj (by simpa only [Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt,
      Polynomial.coeff_zero] using he)
  obtain ⟨t, ht⟩ := s2_polynomial_simultaneous_avoidance R ι B φ hφ
    (fun i => Polynomial.ofFn n (c i)) hp
  refine ⟨t, ?_⟩
  intro i
  simpa only [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial] using ht i

end HodgeLean.Foundations.Program
