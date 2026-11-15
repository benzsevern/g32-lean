import HodgeLean.Foundations.Program.RelativeFrameOperatorDefs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable

set_option maxHeartbeats 400000

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_polynomial_sectors (n : ℕ) (hn : 0 < n) (y : ℂ) (hy : y ≠ 0)
    (a : Fin n → ℂ) (ha : ∀ w : ℂ, w ^ n = y → ∑ j : Fin n, w ^ (j : ℕ) * a j = 0) :
    a = 0 := by
  classical
  let p : Polynomial ℂ := ∑ j : Fin n, Polynomial.monomial (j : ℕ) (a j)
  let q : Polynomial ℂ := Polynomial.X ^ n - Polynomial.C y
  have hq0 : q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hn y
  have hsep : q.Separable := Polynomial.separable_X_pow_sub_C y (by exact_mod_cast hn.ne') hy
  have hcard : q.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree]
    exact Polynomial.natDegree_X_pow_sub_C
  have hpdeg : p.natDegree < n := by
    have hle : p.natDegree ≤ n - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      exact (Polynomial.natDegree_monomial_le _).trans (by omega)
    omega
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p q.roots.toFinset
    · intro w hw
      have hw' := (Polynomial.mem_roots hq0).mp (Multiset.mem_toFinset.mp hw)
      have hwy : w ^ n = y := by
        simpa only [q, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hw'
      simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm] using ha w hwy
    · rw [hcard]
      exact hpdeg
  funext j
  have hj := congrArg (fun t : Polynomial ℂ ↦ t.coeff (j : ℕ)) hp
  simpa only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    ← Fin.ext_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Polynomial.coeff_zero,
    Pi.zero_apply] using hj

theorem rf4_sector_injective_core (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ)
    (hε : ‖ε‖ < r) (g : Fin n → b63r_bddHol (Metric.ball c (2 * r)))
    (hg : ∀ w ∈ rf4_innerDisc n r ε,
      rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) (c + ε) w = 0) :
    g = 0 := by
  classical
  have hz : ∀ z ∈ Metric.ball c (2 * r), z ≠ c + ε →
      (fun j ↦ rf4_extendBdd (g j) z) = 0 := by
    intro z hz hzne
    apply rf4_polynomial_sectors n (by omega) (z - (c + ε)) (sub_ne_zero.mpr hzne)
    intro w hw
    have harg : c + ε + w ^ n = z := by rw [hw]; ring
    have hmem : w ∈ rf4_innerDisc n r ε := by
      change ‖w ^ n + ε‖ < 2 * r
      rw [hw]
      have heq : z - (c + ε) + ε = z - c := by ring
      rw [heq]
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hv := hg w hmem
    rw [rf4_sectorCoeff, harg] at hv
    exact (mul_eq_zero.mp hv).resolve_left (by exact_mod_cast (show n ≠ 0 by omega))
  funext j
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro z
  have hd : DifferentiableOn ℂ (rf4_extendBdd (g j)) (Metric.ball c (2 * r)) :=
    (b63r_mem_bddHol_iff Metric.isOpen_ball _).mp (g j).property
  have hc := (hd z z.property).differentiableAt (Metric.isOpen_ball.mem_nhds z.property)
  have hv : rf4_extendBdd (g j) z = 0 := by
    apply hc.continuousAt.continuousWithinAt.eq_const_of_mem_closure
      ((dense_compl_singleton (c + ε)).open_subset_closure_inter Metric.isOpen_ball z.property)
    intro y hy
    exact congrFun (hz y hy.1 hy.2) j
  simpa [rf4_extendBdd, z.property] using hv

theorem rf4_innerDisc_power_image (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (ε : ℂ) :
    (fun w : ℂ ↦ w ^ n + ε) '' rf4_innerDisc n r ε = Metric.ball (0 : ℂ) (2 * r) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact hw
  · intro hz
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z - ε) (show 0 < n by omega)
    have heq : w ^ n + ε = z := by rw [hw]; ring
    exact ⟨w, by simpa only [rf4_innerDisc, Set.mem_ofPred_eq, heq, Metric.mem_ball,
      dist_zero_right] using hz, heq⟩

theorem rf4_innerDisc_shifted_power_image (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (c ε : ℂ) :
    (fun w : ℂ ↦ c + ε + w ^ n) '' rf4_innerDisc n r ε = Metric.ball c (2 * r) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show c + ε + w ^ n - c = w ^ n + ε by ring]
    exact hw
  · intro hz
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z - (c + ε)) (show 0 < n by omega)
    have heq : c + ε + w ^ n = z := by rw [hw]; ring
    have hmem : w ∈ rf4_innerDisc n r ε := by
      change ‖w ^ n + ε‖ < 2 * r
      rw [hw, show z - (c + ε) + ε = z - c by ring]
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    exact ⟨w, hmem, heq⟩

end HodgeLean.Foundations.Program
