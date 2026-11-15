import HodgeLean.Foundations.Program.SchoenTowerT11bRootSections
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Topology.Algebra.Polynomial

/-! Uniform root bounds for monic polynomial families.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open scoped NNReal Topology

/-- Roots of a monic polynomial family are uniformly bounded over a compact parameter set.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, bounded root-section step. -/
theorem s2v_t11b_monic_family_root_bound (P : Polynomial (Polynomial ℝ)) (hP : P.Monic)
    (K : Set ℝ) (hK : IsCompact K) :
    ∃ B : ℝ≥0, 0 < B ∧ ∀ t ∈ K, ∀ x : ℝ,
      P.eval₂ (Polynomial.evalRingHom t) x = 0 → ‖x‖₊ < B := by
  classical
  have hc : ∀ i : Fin P.natDegree, ∃ M : ℝ≥0,
      ∀ t ∈ K, ‖(P.coeff i.val).eval t‖₊ ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := hK.bddAbove_image
      (P.coeff i.val).continuous.nnnorm.continuousOn
    exact ⟨M, fun t ht => hM ⟨t, ht, rfl⟩⟩
  choose M hM using hc
  let B : ℝ≥0 := Finset.univ.sup M + 1
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro t ht x hx
  have hmonic := hP.map (Polynomial.evalRingHom t)
  have hbound : (P.map (Polynomial.evalRingHom t)).cauchyBound ≤ B := by
    rw [Polynomial.cauchyBound, hmonic.leadingCoeff, nnnorm_one, div_one,
      hP.natDegree_map]
    dsimp [B]
    apply add_le_add ?_ le_rfl
    apply Finset.sup_le
    intro i hi
    rw [Polynomial.coeff_map]
    exact (hM ⟨i, Finset.mem_range.mp hi⟩ t ht).trans
      (Finset.le_sup (f := M) (Finset.mem_univ _))
  have hroot : (P.map (Polynomial.evalRingHom t)).IsRoot x := by
    simpa only [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map] using hx
  exact (hroot.norm_lt_cauchyBound hmonic.ne_zero).trans_le hbound

/-- All nearby roots of a monic family stay in any prescribed open neighborhood of the initial roots.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, bounded root-section step. -/
theorem s2v_t11b_monic_family_roots_stay_in
    (P : Polynomial (Polynomial ℝ)) (hP : P.Monic) (a : ℝ)
    (U : Set ℝ) (hU : IsOpen U)
    (hroots : ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom a) x = 0 → x ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Metric.ball a ε, ∀ x : ℝ,
      P.eval₂ (Polynomial.evalRingHom t) x = 0 → x ∈ U := by
  obtain ⟨B, _, hB⟩ := s2v_t11b_monic_family_root_bound P hP
    (Metric.closedBall a 1) (isCompact_closedBall a 1)
  let K : Set ℝ := Metric.closedBall 0 (B : ℝ) \ U
  have hK : IsCompact K := (isCompact_closedBall (0 : ℝ) (B : ℝ)).diff hU
  obtain ⟨r, hr, hno⟩ := s2v_t11b_polynomial_family_compact_root_exclusion P a K hK
    (fun x hx hzero => hx.2 (hroots x hzero))
  refine ⟨min r 1, lt_min hr zero_lt_one, ?_⟩
  intro t ht x hx
  have ht1 : t ∈ Metric.closedBall a 1 :=
    (Metric.mem_ball.mp ht).le.trans (min_le_right r 1)
  have hxr : ‖x‖₊ < B := hB t ht1 x hx
  have hxB : x ∈ Metric.closedBall 0 (B : ℝ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (show ‖x‖ < (B : ℝ) from hxr).le
  by_contra hxU
  exact hno t ((Metric.mem_ball.mp ht).trans_le (min_le_left r 1)) x ⟨hxB, hxU⟩ hx

end HodgeLean.Foundations.Program
