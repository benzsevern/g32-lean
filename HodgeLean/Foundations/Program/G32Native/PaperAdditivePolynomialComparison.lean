import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native

/-- An additive polynomial representation fixes a vector exactly when its linear
coefficient operator kills that vector. -/
theorem paperAdditivePolynomial_fixed_iff
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (C : K → Module.End K V) (X : Module.End K V)
    (hzero : C 0 = 1) (hadd : ∀ s t, C (s + t) = C s * C t)
    (hpoly : ∀ (v : V) (ℓ : Module.Dual K V), ∃ p : Polynomial K,
      (∀ t, p.eval t = ℓ (C t v)) ∧ p.coeff 1 = ℓ (X v)) (v : V) :
    (∀ t, C t v = v) ↔ X v = 0 := by
  constructor
  · intro hv
    apply (Module.forall_dual_apply_eq_zero_iff K _).mp
    intro ℓ
    obtain ⟨p, hp, hp1⟩ := hpoly v ℓ
    have heq : p = Polynomial.C (ℓ v) := by
      apply Polynomial.funext
      intro t
      rw [hp, hv, Polynomial.eval_C]
    rw [← hp1, heq, Polynomial.coeff_C]
    simp
  · intro hv t
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff K _).mp
    intro ℓ
    obtain ⟨p, hp, hp1⟩ := hpoly v ℓ
    have hd : p.derivative = 0 := by
      apply Polynomial.zero_of_eval_zero
      intro s
      obtain ⟨q, hq, hq1⟩ := hpoly v (ℓ.comp (C s))
      have hqeq : Polynomial.taylor s p = q := by
        apply Polynomial.funext
        intro r
        rw [Polynomial.taylor_eval, hp, add_comm r s, hq, LinearMap.comp_apply, hadd,
          Module.End.mul_apply]
      rw [← Polynomial.taylor_coeff_one, hqeq, hq1, hv, map_zero]
    have heq := Polynomial.eq_C_of_derivative_eq_zero hd
    have hconst : p.eval t = p.eval 0 := by rw [heq]; simp only [Polynomial.eval_C]
    have hvalue : ℓ (C t v) = ℓ v := by
      simpa only [hp, hzero, Module.End.one_apply] using hconst
    rw [map_sub, hvalue, sub_self]

end HodgeLean.Foundations.Program.G32Native
