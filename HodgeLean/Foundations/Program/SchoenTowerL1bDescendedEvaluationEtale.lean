import HodgeLean.Foundations.Program.SchoenTowerL1bSymmetricExpansion
import HodgeLean.Foundations.Program.SchoenTowerL1bPolynomialEvaluationCoordinates
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Rev

/-! Two evaluations in the actual descended symmetric coefficient system.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open scoped BigOperators

/-- Changing the index type of a polynomial coordinate family preserves etaleness. -/
theorem s2v_l1b_reindex_etale
    {R A ι κ : Type} [CommRing R] [CommRing A]
    (f : R →+* A) (c : ι → A) (e : κ ≃ ι)
    (hEt : (MvPolynomial.eval₂Hom f c).Etale) :
    (MvPolynomial.eval₂Hom f (fun j => c (e j))).Etale := by
  let E := MvPolynomial.renameEquiv R e
  have hcomp : (MvPolynomial.eval₂Hom f c).comp E.toRingEquiv.toRingHom =
      MvPolynomial.eval₂Hom f (fun j => c (e j)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      change MvPolynomial.eval₂Hom f c (E (MvPolynomial.C r)) = f r
      rw [show E (MvPolynomial.C r) = MvPolynomial.C r from E.commutes r]
      exact MvPolynomial.eval₂Hom_C _ _ _
    · intro j
      change MvPolynomial.eval₂Hom f c (MvPolynomial.rename e (MvPolynomial.X j)) = _
      rw [MvPolynomial.rename_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  rw [← hcomp]
  exact RingHom.Etale.stableUnderComposition E.toRingEquiv.toRingHom _
    (RingHom.Etale.of_bijective E.bijective) hEt

/-- The signed reversed symmetric expansion gives two evaluation coordinates, with all other coordinates retained. -/
theorem s2v_l1b_symmetric_evaluations_etale
    {R A : Type} [CommRing R] [CommRing A]
    (n : ℕ) (f : R →+* A) (c : Fin (n + 2) → A)
    (a b : R) (hab : IsUnit (b - a))
    (hEt : (MvPolynomial.eval₂Hom f c).Etale) :
    let V (t : R) := (-f t) ^ (n + 2) +
      ∑ j : Fin (n + 2), c j * (-f t) ^ (n + 2 - (j.val + 1))
    (MvPolynomial.eval₂Hom f (Sum.elim ![V a, V b]
      (fun k : Fin n => c (Fin.rev ⟨k.val + 2, by omega⟩)))).Etale := by
  classical
  let e : Fin 2 ⊕ Fin n ≃ Fin (n + 2) :=
    finSumFinEquiv.trans (finCongr (by omega))
  let z : Fin 2 ⊕ Fin n → A := fun j => c (Fin.rev (e j))
  have hz : (MvPolynomial.eval₂Hom f z).Etale :=
    s2v_l1b_reindex_etale f c (e.trans Fin.revPerm) hEt
  have H := s2v_l1b_polynomial_evaluation_etale n f z (-a) (-b)
    (by simpa only [neg_sub_neg, neg_sub] using hab.neg) hz
  have hsum (t : R) :
      (∑ j : Fin (n + 2), c j * (-f t) ^ (n + 2 - (j.val + 1))) =
      ∑ j : Fin (n + 2), c (Fin.rev j) * (-f t) ^ j.val := by
    rw [← Equiv.sum_comp Fin.revPerm]
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  have hzrest (k : Fin n) : z (Sum.inr k) = c (Fin.rev ⟨k.val + 2, by omega⟩) := by
    change c (Fin.rev (e (Sum.inr k))) = _
    congr 2
    apply Fin.ext
    simp only [e, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply,
      Fin.val_cast, Fin.val_natAdd]
    omega
  have hsplit (t : R) :
      (∑ j : Fin (n + 2), c (Fin.rev j) * (-f t) ^ j.val) =
      z (Sum.inl 0) + z (Sum.inl 1) * (-f t) +
        ∑ k : Fin n, c (Fin.rev ⟨k.val + 2, by omega⟩) * (-f t) ^ (k.val + 2) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, zero_add, pow_one]
    have hz0 : z (Sum.inl 0) = c (Fin.rev ⟨0, by omega⟩) := by
      rfl
    have hz1 : z (Sum.inl 1) = c (Fin.rev ⟨1, by omega⟩) := by
      rfl
    rw [hz0, hz1]
    simp only [Nat.add_assoc, show 1 + 1 = 2 from rfl]
    rw [← add_assoc]
    rfl
  change (MvPolynomial.eval₂Hom f (Sum.elim ![_, _] _)).Etale at H
  have hev (t : R) :
      Polynomial.eval (f (-t))
        (Polynomial.X ^ (n + 2) + Polynomial.C (z (Sum.inl 0)) +
        Polynomial.C (z (Sum.inl 1)) * Polynomial.X +
        ∑ k : Fin n, Polynomial.C (z (Sum.inr k)) * Polynomial.X ^ (k.val + 2)) =
      (-f t) ^ (n + 2) +
        ∑ j : Fin (n + 2), c j * (-f t) ^ (n + 2 - (j.val + 1)) := by
    rw [hsum, hsplit]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_finsetSum, map_neg]
    simp only [hzrest]
    ring
  rw [hev a, hev b] at H
  simpa only [hzrest] using H

/-- Evaluations of the actual descended branch polynomial give coordinates after any etale coefficient localization. -/
theorem s2v_l1b_descended_evaluations_etale
    {K A B L : Type} [Field K] [CommRing A] [CommRing B] [CommRing L]
    [Algebra K A] [Algebra K B] [Algebra K L]
    (n : ℕ) (z : Fin (n + 2) → B) (q : A →ₐ[K] B)
    (hq : Function.Injective q) (P : Polynomial A)
    (hP : P.map q.toRingHom = ∏ i, (Polynomial.C (z i) - Polynomial.X))
    (c : Fin (n + 2) → A)
    (hc : ∀ j, q (c j) = MvPolynomial.aeval (R := K) z
      (MvPolynomial.esymm (Fin (n + 2)) K (j.val + 1)))
    (l : A →ₐ[K] L) (a b : K) (hab : a ≠ b)
    (hEt : (MvPolynomial.eval₂Hom (algebraMap K L) (fun j => l (c j))).Etale) :
    (MvPolynomial.eval₂Hom (algebraMap K L)
      (Sum.elim ![l (P.eval (algebraMap K A a)), l (P.eval (algebraMap K A b))]
        (fun k : Fin n => l (c (Fin.rev ⟨k.val + 2, by omega⟩))))).Etale := by
  have hev (t : K) : l (P.eval (algebraMap K A t)) =
      (-algebraMap K L t) ^ (n + 2) +
        ∑ j : Fin (n + 2), l (c j) * (-algebraMap K L t) ^ (n + 2 - (j.val + 1)) := by
    rw [s2v_l1b_descended_product_expansion (n + 2) z q hq P hP c hc t]
    simp only [map_add, map_sum, map_mul, map_pow, map_neg, l.commutes]
  rw [hev a, hev b]
  exact s2v_l1b_symmetric_evaluations_etale n (algebraMap K L) (fun j => l (c j))
    a b (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab.symm)) hEt

end HodgeLean.Foundations.Program
