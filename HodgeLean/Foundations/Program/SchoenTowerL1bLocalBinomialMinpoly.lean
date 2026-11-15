import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Div

noncomputable section
set_option maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- A binomial generator of an extension of the displayed degree has exactly
the displayed binomial as its minimal polynomial. -/
theorem s2v_l1b_local_binomial_minpoly
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (t : E) (m : ℕ) (c : F) (hm : m ≠ 0)
    (hgen : IntermediateField.adjoin F ({t} : Set E) = ⊤)
    (hdegree : Module.finrank F E = m) (hpow : t ^ m = algebraMap F E c) :
    minpoly F t = Polynomial.X ^ m - Polynomial.C c := by
  have ht : IsIntegral F t := Algebra.IsIntegral.isIntegral t
  have hdeg : (minpoly F t).natDegree = m := by
    calc
      _ = Module.finrank F (IntermediateField.adjoin F ({t} : Set E)) :=
        (IntermediateField.adjoin.finrank ht).symm
      _ = Module.finrank F E := by
        rw [hgen]
        exact (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).toLinearEquiv.finrank_eq
      _ = m := hdegree
  have hdvd : minpoly F t ∣ Polynomial.X ^ m - Polynomial.C c := by
    apply minpoly.dvd F t
    simp only [map_sub, map_pow, aeval_X, aeval_C, hpow, sub_self]
  apply Eq.symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ht)
    (Polynomial.monic_X_pow_sub_C c hm) hdvd
  rw [hdeg, Polynomial.natDegree_X_pow_sub_C]

end HodgeLean.Foundations.Program
