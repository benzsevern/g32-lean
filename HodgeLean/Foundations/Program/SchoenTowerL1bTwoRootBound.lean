import HodgeLean.Foundations.Program.SchoenTowerL1bBranchPolynomial
import Mathlib.Data.Fintype.Card

/-! Coordinate count from two distinct branch values in an ordered tuple.
HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped BigOperators

/-- Two distinct values occurring among an ordered tuple require at least two coordinates. -/
theorem s2v_l1b_two_root_coordinate_bound
    {K : Type*} [Field K] (n : ℕ) (z : Fin n → K)
    (a b : K) (hab : a ≠ b)
    (ha : (∏ i, (z i - a)) = 0) (hb : (∏ i, (z i - b)) = 0) :
    2 ≤ n := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp ha
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hb
  have hij : i ≠ j := by
    intro H
    exact hab ((sub_eq_zero.mp hi).symm.trans (H ▸ sub_eq_zero.mp hj))
  have hcard := Finset.card_le_card
    (show ({i, j} : Finset (Fin n)) ⊆ Finset.univ from Finset.subset_univ _)
  simpa only [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin] using hcard

/-- Two distinct zeros of a descended ordered branch product force the retained coordinate count. -/
theorem s2v_l1b_descended_two_root_coordinate_bound
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (n : ℕ) (z : Fin n → B) (q : A →ₐ[K] B)
    (P : Polynomial A)
    (hP : P.map q.toRingHom = ∏ i, (Polynomial.C (z i) - Polynomial.X))
    (φ : B →ₐ[K] K) (a b : K) (hab : a ≠ b)
    (ha : φ (q (P.eval (algebraMap K A a))) = 0)
    (hb : φ (q (P.eval (algebraMap K A b))) = 0) :
    2 ≤ n := by
  have hev (t : K) : φ (q (P.eval (algebraMap K A t))) =
      ∏ i, (φ (z i) - t) := by
    change φ (q.toRingHom (P.eval (algebraMap K A t))) = _
    rw [s2v_l1b_branch_polynomial_eval n z q.toRingHom P hP]
    simp only [map_prod, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      q.commutes, φ.commutes, Algebra.algebraMap_self,
      RingHom.id_apply]
  rw [hev] at ha hb
  exact s2v_l1b_two_root_coordinate_bound n (fun i => φ (z i)) a b hab ha hb

end HodgeLean.Foundations.Program
