module

public import HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_list_multilinear_form (m : ℕ) (l : List (Fin m)) :
    ∃ p : (Fin m → ℂ) [×l.length]→L[ℂ] ℂ,
      (∀ z, p (fun _ => z) = (l.map z).prod) ∧ ‖p‖ ≤ 1 := by
  let q := (MultilinearMap.mkPiAlgebra ℂ (Fin l.length) ℂ).compLinearMap
    (fun i => (LinearMap.proj (l[i.val]) : (Fin m → ℂ) →ₗ[ℂ] ℂ))
  have hb (v : Fin l.length → Fin m → ℂ) : ‖q v‖ ≤ 1 * ∏ i, ‖v i‖ := by
    change ‖∏ i : Fin l.length, v i (l[i.val])‖ ≤ _
    rw [norm_prod, one_mul]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => norm_le_pi_norm (v i) _)
  refine ⟨q.mkContinuous 1 hb, ?_, q.mkContinuous_norm_le (by norm_num) hb⟩
  intro z
  change (∏ i : Fin l.length, z (l[i.val])) = _
  exact Fin.prod_univ_fun_getElem l z

theorem s2e_monomial_multilinear_form (m n : ℕ) (a : Fin m →₀ ℕ)
    (ha : a.degree = n) :
    ∃ p : (Fin m → ℂ) [×n]→L[ℂ] ℂ,
      (∀ z, p (fun _ => z) = ∏ i, z i ^ a i) ∧ ‖p‖ ≤ 1 := by
  classical
  have hl : a.toMultiset.toList.length = n := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact ha
  rw [← hl]
  obtain ⟨p, hp, hn⟩ := s2e_list_multilinear_form m a.toMultiset.toList
  refine ⟨p, ?_, hn⟩
  intro z
  rw [hp, Multiset.prod_map_toList, Finset.prod_multiset_map_count]
  simp only [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset]
  exact Finsupp.prod_pow a z

theorem s2e_homogeneous_multilinear_form (m n : ℕ) (F : MvPowerSeries (Fin m) ℂ) :
    ∃ p : (Fin m → ℂ) [×n]→L[ℂ] ℂ,
      (∀ z, p (fun _ => z) = ∑' a : {a : Fin m →₀ ℕ // a.degree = n},
        MvPowerSeries.coeff a.val F * ∏ i, z i ^ a.val i) ∧
      ‖p‖ ≤ ∑' a : {a : Fin m →₀ ℕ // a.degree = n}, ‖MvPowerSeries.coeff a.val F‖ := by
  classical
  letI : Fintype {a : Fin m →₀ ℕ // a.degree = n} :=
    (Finsupp.finite_of_degree_eq n).fintype
  choose p hp hn using fun a : {a : Fin m →₀ ℕ // a.degree = n} =>
    s2e_monomial_multilinear_form m n a.val a.property
  refine ⟨∑ a, MvPowerSeries.coeff a.val F • p a, ?_, ?_⟩
  · intro z
    simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
      smul_eq_mul, hp, tsum_fintype]
  · rw [tsum_fintype]
    calc
      _ ≤ ∑ a, ‖MvPowerSeries.coeff a.val F • p a‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_smul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hn a)

end HodgeLean.Foundations.Program
