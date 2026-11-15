import HodgeLean.Foundations.Program.SchoenTowerI2aBranchCoordinates
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.Fin.Rev

/-! # Actual monic polynomial coefficients as symmetric chart coordinates
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Every coefficient of the actual root product is its signed elementary symmetric coordinate.
Source: Mathlib, Multiset.prod_X_sub_C_coeff and MvPolynomial.aeval_esymm_eq_multiset_esymm. -/
theorem s2v_i2a_monic_coefficient_eq_symmetric
    {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    (n : ℕ) (z : Fin n → B) (j : Fin n) :
    (∏ i, (Polynomial.X - Polynomial.C (z i))).coeff (j : ℕ) =
      (-1 : B) ^ (n - j.val) * MvPolynomial.aeval (R := k) z
        (MvPolynomial.esymm (Fin n) k (n - j.val)) := by
  have hj : (j : ℕ) ≤ (Finset.univ.val.map z).card := by
    simpa only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin] using Nat.le_of_lt j.isLt
  have H := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map z) hj
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  simpa only [Multiset.map_map, Function.comp_def, Multiset.card_map,
    Finset.card_val, Finset.card_univ, Fintype.card_fin, Finset.prod] using H

/-- Signed reversal of elementary coordinates is an actual polynomial coordinate automorphism.
Source: Mathlib, invertible diagonal matrices and MvPolynomial.renameEquiv. -/
theorem s2v_i2a_signed_reverse_coordinates
    (k : Type*) [Field k] (n : ℕ) :
    ∃ e : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k,
      ∀ i, e (MvPolynomial.X i) =
        MvPolynomial.C ((-1 : k) ^ (n - i.val)) * MvPolynomial.X (Fin.rev i) := by
  let M : Matrix (Fin n) (Fin n) k := Matrix.diagonal fun i => (-1 : k) ^ (n - i.val)
  have hdet : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    change (Matrix.diagonal fun i : Fin n => (-1 : k) ^ (n - i.val)).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  let linear := s2v_i2a_matrixCoordinateEquiv k n M hdet
  let reindex := MvPolynomial.renameEquiv k (@Fin.revPerm n)
  refine ⟨linear.trans reindex, ?_⟩
  intro i
  change reindex (linear (MvPolynomial.X i)) = _
  have hXi : linear (MvPolynomial.X i) =
      MvPolynomial.C ((-1 : k) ^ (n - i.val)) * MvPolynomial.X i := by
    calc
      linear (MvPolynomial.X i) = ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j :=
        MvPolynomial.aeval_X _ _
      _ = _ := by
        simp only [M, Matrix.diagonal_apply]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hji
          rw [if_neg (Ne.symm hji), map_zero, zero_mul]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
  rw [hXi, map_mul, show reindex (MvPolynomial.C ((-1 : k) ^ (n - i.val))) =
    MvPolynomial.C ((-1 : k) ^ (n - i.val)) from reindex.commutes _]
  congr 1
  change MvPolynomial.rename Fin.revPerm (MvPolynomial.X i) = MvPolynomial.X (Fin.rev i)
  exact MvPolynomial.rename_X _ _

/-- An actual etale elementary coefficient chart gives an etale monic coefficient chart with the specified root-product pullback.
Source: Schoen (1988), Lemma 2.2; Mathlib, Vieta's formula and etale invariance under coordinate automorphisms. -/
theorem s2v_i2a_etale_monic_coefficient_chart
    (k B D : Type) [Field k] [CommRing B] [CommRing D] [Algebra k B] [Algebra k D]
    (n : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] D) (hcEt : c.toRingHom.Etale)
    (q : D →ₐ[k] B) (z : Fin n → B)
    (hc : ∀ j, q (c (MvPolynomial.X j)) =
      MvPolynomial.aeval (R := k) z (MvPolynomial.esymm (Fin n) k (j.val + 1))) :
    ∃ cMon : MvPolynomial (Fin n) k →ₐ[k] D, cMon.toRingHom.Etale ∧
      ∀ j, q (cMon (MvPolynomial.X j)) =
        (∏ i, (Polynomial.X - Polynomial.C (z i))).coeff (j : ℕ) := by
  obtain ⟨e, he⟩ := s2v_i2a_signed_reverse_coordinates k n
  refine ⟨c.comp e.toAlgHom, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition e.toRingHom c.toRingHom
      (RingHom.Etale.of_bijective e.bijective) hcEt
  · intro j
    change (q.comp c) (e (MvPolynomial.X j)) = _
    rw [he j, map_mul]
    have hC (a : k) : (q.comp c) (MvPolynomial.C a) = algebraMap k B a :=
      (q.comp c).commutes a
    rw [hC, map_pow, map_neg, map_one]
    change (-1 : B) ^ (n - j.val) * q (c (MvPolynomial.X (Fin.rev j))) = _
    rw [hc, s2v_i2a_monic_coefficient_eq_symmetric (k := k) n z j]
    have hindex : (Fin.rev j).val + 1 = n - j.val := by
      rw [Fin.val_rev]
      omega
    rw [hindex]

end HodgeLean.Foundations.Program
