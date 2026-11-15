import HodgeLean.Foundations.Program.SchlesingerPathBoxes
import HodgeLean.Foundations.Program.PullbackMonodromyProofs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open Set Metric Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

def b65p_fibreLabels (e : ℤ) : Finset (Fin 12) := Finset.univ.filter (fun j ↦ b65p_fibre j = e)

theorem b65p_fibreLabels_card (e : ℤ) (he : e = 5 ∨ e = -7) :
    (b65p_fibreLabels e).card = 6 := by
  rcases he with rfl | rfl <;> decide

theorem b65p_label_fibre (k : Fin 12) : b65p_fibre (b65b_boxIndex k) = b65b_boxFibre k := by
  revert k; decide

theorem b65p_fibre_roots (p : Fin 12 → ℂ) (hpinj : Function.Injective p)
    (hroot : ∀ j, b65r_P (b65p_fibre j) (p j) = 0)
    (e : ℤ) (he : e = 5 ∨ e = -7) :
    (b65s_poly (e : ℂ)).roots = ((b65p_fibreLabels e).image p).val := by
  have he1 : (e : ℂ) ≠ 1 := by rcases he with rfl | rfl <;> norm_num
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hje : b65p_fibre j = e := (Finset.mem_filter.mp hj).2
    simpa only [b65s_poly_eval, ← hje] using hroot j
  · rw [Finset.card_image_of_injective _ hpinj, b65p_fibreLabels_card e he,
      b65s_poly_natDegree _ he1]
  · exact b65s_poly_ne_zero _ he1

theorem b65p_fibre_logDeriv (p : Fin 12 → ℂ) (hpinj : Function.Injective p)
    (hroot : ∀ j, b65r_P (b65p_fibre j) (p j) = 0)
    (e : ℤ) (he : e = 5 ∨ e = -7) (s : ℂ) (hs : b65r_P e s ≠ 0) :
    deriv (b65r_P e) s / b65r_P e s =
      ∑ j ∈ b65p_fibreLabels e, (s - p j)⁻¹ := by
  have hd : deriv (b65r_P e) s = ((b65s_poly e).derivative).eval s := by
    have ht : HasDerivAt (b65r_P e) ((b65s_poly e).derivative.eval s) s := by
      simpa only [b65s_poly_eval] using (b65s_poly e).hasDerivAt s
    exact ht.deriv
  have h := (IsAlgClosed.splits (b65s_poly (e : ℂ))).eval_derivative_div_eval_of_ne_zero
    (x := s) (by simpa only [b65s_poly_eval] using hs)
  rw [b65p_fibre_roots p hpinj hroot e he, b65s_poly_eval, ← hd] at h
  change deriv (b65r_P e) s / b65r_P e s =
    ∑ z ∈ (b65p_fibreLabels e).image p, 1 / (s - z) at h
  rw [Finset.sum_image (fun a _ b _ hab ↦ hpinj hab)] at h
  simpa only [one_div] using h

end HodgeLean.Foundations.Program
