import HodgeLean.Foundations.Program.CoverDictionaryUnique
import HodgeLean.Foundations.Program.CoverDictionaryBranch

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

theorem b66d_eval_polynomial_fraction (P D : ℂ[X]) (s : ℂ) (hD : D.eval s ≠ 0) :
    b65q_eval (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) D) s =
      P.eval s / D.eval s := by
  let f : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) D
  have hfr : b65g_reg s f := by
    intro hf
    exact hD (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd P D) hf)
  have hdr : b65g_reg s (algebraMap ℂ[X] (RatFunc ℂ) D) := by
    simp [b65g_reg, RatFunc.denom_algebraMap]
  have hDn : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    intro he
    exact hD (by rw [he, Polynomial.eval_zero])
  have he : f * algebraMap ℂ[X] (RatFunc ℂ) D = algebraMap ℂ[X] (RatFunc ℂ) P :=
    div_mul_cancel₀ _ hDn
  have heval (Q : ℂ[X]) : b65q_eval (algebraMap ℂ[X] (RatFunc ℂ) Q) s = Q.eval s := by
    simp [b65q_eval, RatFunc.eval_algebraMap]
  have h := congrArg (fun r : RatFunc ℂ => b65q_eval r s) he
  rw [b65g_eval_mul hfr hdr, heval, heval] at h
  exact (eq_div_iff hD).mpr h

theorem b66d_denominator_away_poles (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (h0 : (0 : ℂ) ∈ Set.range poles) (s : ℂ) (hs : s ∉ Set.range poles) :
    (b65q_denominator poles).eval s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hz
    apply hs
    simpa only [hz] using h0
  rw [b65q_denominator, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod]
  apply mul_ne_zero hs0
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr (fun h => hs ⟨Sum.inr i, h.symm⟩)

theorem b66d_numerator_fraction_evaluation (N : Fin 10 → ℂ)
    (poles : Fin 4 ⊕ Fin 12 → ℂ) (s : ℂ) (hD : (b65q_denominator poles).eval s ≠ 0) :
    b65q_eval ((∑ j : Fin 10, RatFunc.C (N j) * RatFunc.X ^ j.val) /
      algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles)) s =
        (∑ j : Fin 10, N j * s ^ j.val) / (b65q_denominator poles).eval s := by
  rw [b65g_numerator_poly, b66d_eval_polynomial_fraction _ _ s hD]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

end HodgeLean.Foundations.Program
