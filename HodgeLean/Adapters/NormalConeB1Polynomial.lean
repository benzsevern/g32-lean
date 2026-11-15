import HodgeLean.Adapters.NormalConeDefs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section
namespace HodgeLean.Adapters

open LaurentPolynomial

lemma a3b1_parameterMap_coe
    (k R : Type*) [Field k] [CommRing R] [Algebra k R] (I : Ideal R)
    (p : Polynomial k) :
    ((a3b1_parameterMap k R I p : a3cc3_deformationAlgebra I) : LaurentPolynomial R) =
      Polynomial.toLaurent (p.map (algebraMap k R)) := by
  let f : Polynomial k →+* LaurentPolynomial R :=
    (a3cc3_deformationAlgebra I).val.toRingHom.comp (a3b1_parameterMap k R I)
  let g : Polynomial k →+* LaurentPolynomial R :=
    Polynomial.toLaurent.comp (Polynomial.mapRingHom (algebraMap k R))
  change f p = g p
  congr 1
  apply Polynomial.ringHom_ext
  · intro x
    simp [f, g, a3b1_parameterMap]
  · simp [f, g, a3b1_parameterMap, a3cc3_parameter]

lemma a3b1_toLaurent_map_mul_injective
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    (p : Polynomial k) (hp : p ≠ 0) :
    Function.Injective
      (fun f : LaurentPolynomial R => Polynomial.toLaurent (p.map (algebraMap k R)) * f) := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
      letI := h
      exact fun _ _ _ => Subsingleton.elim _ _
  | inr h =>
    letI := h
    have hpUnit : IsUnit (p.map (algebraMap k R)).leadingCoeff := by
      rw [Polynomial.leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective k R) p]
      exact (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)).map _
    intro f g hfg
    obtain ⟨nf, f', hf'⟩ := LaurentPolynomial.exists_T_pow f
    obtain ⟨ng, g', hg'⟩ := LaurentPolynomial.exists_T_pow g
    let n := max nf ng
    have hf : Polynomial.toLaurent (f' * Polynomial.X ^ (n - nf)) = f * T (n : ℤ) := by
      rw [map_mul, Polynomial.toLaurent_X_pow, hf']
      calc
        f * T (nf : ℤ) * T ((n - nf : ℕ) : ℤ) =
            f * (T (nf : ℤ) * T ((n - nf : ℕ) : ℤ)) := by rw [mul_assoc]
        _ = f * T (n : ℤ) := by rw [← T_add]; congr 2; omega
    have hg : Polynomial.toLaurent (g' * Polynomial.X ^ (n - ng)) = g * T (n : ℤ) := by
      rw [map_mul, Polynomial.toLaurent_X_pow, hg']
      calc
        g * T (ng : ℤ) * T ((n - ng : ℕ) : ℤ) =
            g * (T (ng : ℤ) * T ((n - ng : ℕ) : ℤ)) := by rw [mul_assoc]
        _ = g * T (n : ℤ) := by rw [← T_add]; congr 2; omega
    have hpoly :
        Polynomial.toLaurent (p.map (algebraMap k R)) *
            Polynomial.toLaurent (f' * Polynomial.X ^ (n - nf)) =
          Polynomial.toLaurent (p.map (algebraMap k R)) *
            Polynomial.toLaurent (g' * Polynomial.X ^ (n - ng)) := by
      rw [hf, hg]
      simpa only [mul_assoc] using congrArg (fun x => x * T (n : ℤ)) hfg
    have hpoly' :
        p.map (algebraMap k R) * (f' * Polynomial.X ^ (n - nf)) =
          p.map (algebraMap k R) * (g' * Polynomial.X ^ (n - ng)) := by
      apply Polynomial.toLaurent_injective
      simpa only [map_mul] using hpoly
    have htail : f' * Polynomial.X ^ (n - nf) = g' * Polynomial.X ^ (n - ng) := by
      rw [← sub_eq_zero]
      apply Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff hpUnit |>.mp
      rw [mul_sub, hpoly', sub_self]
    have hmul : f * T (n : ℤ) = g * T (n : ℤ) := by
      rw [← hf, ← hg]
      exact congrArg Polynomial.toLaurent htail
    calc
      f = f * T 0 := by simp
      _ = (f * T (n : ℤ)) * T (-(n : ℤ)) := by
        rw [mul_assoc, ← T_add, add_neg_cancel]
      _ = (g * T (n : ℤ)) * T (-(n : ℤ)) := by rw [hmul]
      _ = g * T 0 := by rw [mul_assoc, ← T_add, add_neg_cancel]
      _ = g := by simp

end HodgeLean.Adapters
