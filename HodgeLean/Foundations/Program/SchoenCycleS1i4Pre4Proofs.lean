module

public import HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import HodgeLean.Foundations.Program.SchoenCycleS1i4LinearHelpers
public import HodgeLean.Foundations.Program.SchoenCycleS1i4BallHelpers
public import HodgeLean.Foundations.Program.SchoenCycleS1i4AnisotropicHelpers
public import HodgeLean.Foundations.Program.SchoenCycleS1i4RecoveryBallHelpers
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients
import all HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all Mathlib.Basic.Complex.Basic

/-! # Analytic coefficient bridges
Homogeneous expansions, coefficient bounds and regular directions.
HC no distance; AV milestone no distance.
-/
public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators ENNReal
namespace HodgeLean.Foundations.Program
/-- Weighted monomials have a multilinear expansion on a ball about zero.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter I, §B, convergent power series; Mathlib, HasFPowerSeriesOnBall. -/
theorem s2e_s1i4_monomial_multilinear_aux
    (d : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (F : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a)) :
    ∃ p : FormalMultilinearSeries ℂ (Fin (d + 1) → ℂ) ℂ, ∃ ρ : ℝ≥0∞,
      HasFPowerSeriesOnBall (s2e_divSeries (d + 1) F) p 0 ρ ∧
      (∀ n z, p n (fun _ => z) =
        ∑' a : Fin (d + 1) →₀ ℕ, if a.sum (fun _ m => m) = n then
          MvPowerSeries.coeff a F * ∏ i, z i ^ a i else 0) ∧
      ∀ᶠ z in nhds (0 : Fin (d + 1) → ℂ),
        HasSum (fun a => MvPowerSeries.coeff a F * ∏ i, z i ^ a i)
          (s2e_divSeries (d + 1) F z) := by
  classical
  obtain ⟨p, ρ, hp, hd⟩ := s2e_monomial_ball_expansion d r hr F hF
  refine ⟨p, ρ, hp, ?_, ?_⟩
  · intro n z
    rw [hd]
    have h := tsum_subtype {a : Fin (d + 1) →₀ ℕ | a.degree = n}
      (fun a => MvPowerSeries.coeff a F * ∏ i, z i ^ a i)
    convert h using 1
    · rfl
    · apply tsum_congr
      intro a
      simp only [Set.indicator, Set.mem_setOf_eq, Finsupp.degree_apply, Finsupp.sum]
  · filter_upwards [s2e_eventually_polydisc d r hr] with z hz
    exact (s2e_monomial_norm_summable d r F hF z hz).of_norm.hasSum

/-- A convergent multilinear expansion supplies monomial coefficients and axis derivatives.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter I, §B, Taylor expansion and coefficient formula. -/
theorem s2e_s1i4_multilinear_coefficients_aux
    (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℂ)
    (p : FormalMultilinearSeries ℂ (Fin (d + 1) → ℂ) ℂ) (ρ : ℝ≥0∞)
    (hp : HasFPowerSeriesOnBall f p 0 ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : MvPowerSeries (Fin (d + 1)) ℂ, ∃ r : Fin (d + 1) → ℝ,
      (∀ i, 0 < r i ∧ r i < ε) ∧
      Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a) ∧
      (∀ n z, p n (fun _ => z) =
        ∑' a : Fin (d + 1) →₀ ℕ, if a.sum (fun _ m => m) = n then
          MvPowerSeries.coeff a F * ∏ i, z i ^ a i else 0) ∧
      (∀ j, iteratedDeriv j (fun t : ℂ => f (Pi.single (Fin.last d) t)) 0 =
        (j.factorial : ℂ) * MvPowerSeries.coeff (Finsupp.single (Fin.last d) j) F) ∧
      f =ᶠ[nhds 0] s2e_divSeries (d + 1) F := by
  classical
  let F := s2e_recoveredSeries (d + 1) p
  obtain ⟨r, hr, hF⟩ := s2e_recovery_small_radii d p (hp.r_pos.trans_le hp.r_le) ε hε
  refine ⟨F, r, hr, hF, ?_, ?_, s2e_recovered_germ d f p ρ hp r (fun i => (hr i).1) hF⟩
  · intro n z
    have h := s2e_recovered_diagonal (d + 1) n p z
    convert h using 1
    apply tsum_congr
    intro a
    simp only [Finsupp.degree_apply, Finsupp.sum, F]
    rfl
  · intro j
    let u : ℂ →L[ℂ] (Fin (d + 1) → ℂ) :=
      (ContinuousLinearMap.id ℂ ℂ).smulRight (Pi.single (Fin.last d) 1)
    have hu (t : ℂ) : u t = Pi.single (Fin.last d) t := by
      change t • Pi.single (Fin.last d) 1 = _
      ext i
      by_cases hi : i = Fin.last d <;> simp [Pi.single_apply, hi]
    have h := s2e_line_iteratedDeriv (d + 1) f p ρ hp u j
    rw [s2e_recovered_axis_coeff]
    simpa only [hu] using h

/-- Vanishing low axis coefficients permit a small relative weighted norm.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, anisotropic polydisc estimate in Weierstrass division. -/
theorem s2e_s1i4_anisotropic_majorant_aux
    (d k : ℕ) (R : Fin (d + 1) → ℝ) (hR : ∀ i, 0 < R i)
    (E : MvPowerSeries (Fin (d + 1)) ℂ)
    (hE : Summable (fun a => ‖MvPowerSeries.coeff a E‖ * s2e_divWeight d R a))
    (haxis : ∀ j ≤ k, MvPowerSeries.coeff (Finsupp.single (Fin.last d) j) E = 0)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ r : Fin (d + 1) → ℝ,
      (∀ i, 0 < r i ∧ r i < min (R i) ε) ∧
      Summable (fun a => ‖MvPowerSeries.coeff a E‖ * s2e_divWeight d r a) ∧
      s2e_divNorm d r E < η * r (Fin.last d) ^ k := by
  classical
  have hN : 0 ≤ s2e_divNorm d R E := tsum_nonneg fun a =>
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => (pow_pos (hR i) _).le)
  have hM : 0 < ‖R‖ + 1 := by positivity
  have hN1 : 0 < s2e_divNorm d R E + 1 := by linarith
  have hRp : 0 < R (Fin.last d) ^ k := pow_pos (hR _) _
  obtain ⟨t, ht, ht'⟩ := exists_between (show (0 : ℝ) <
      min 1 (min (ε / (‖R‖ + 1)) (η * R (Fin.last d) ^ k / (s2e_divNorm d R E + 1))) from
    lt_min (by norm_num) (lt_min (div_pos hε hM) (div_pos (mul_pos hη hRp) hN1)))
  have ht1 : t < 1 := lt_of_lt_of_le ht' (min_le_left _ _)
  have htε : t * (‖R‖ + 1) < ε := (lt_div_iff₀ hM).mp
    (lt_of_lt_of_le ht' ((min_le_right _ _).trans (min_le_left _ _)))
  have htη : t * (s2e_divNorm d R E + 1) < η * R (Fin.last d) ^ k :=
    (lt_div_iff₀ hN1).mp
      (lt_of_lt_of_le ht' ((min_le_right _ _).trans (min_le_right _ _)))
  let r := fun i => R i * t ^ (if i = Fin.last d then 1 else k + 1)
  have hr (i) : 0 < r i ∧ r i < min (R i) ε := by
    have hpow : t ^ (if i = Fin.last d then 1 else k + 1) ≤ t := by
      simpa only [pow_one] using pow_le_pow_of_le_one ht.le ht1.le
        (show 1 ≤ (if i = Fin.last d then 1 else k + 1) by split_ifs <;> omega)
    have hRi : R i ≤ ‖R‖ := (le_abs_self _).trans (norm_le_pi_norm R i)
    refine ⟨mul_pos (hR i) (pow_pos ht _), lt_min ?_ ?_⟩
    · exact (mul_le_mul_of_nonneg_left hpow (hR i).le).trans_lt (by nlinarith [hR i])
    · exact (mul_le_mul_of_nonneg_left hpow (hR i).le).trans_lt (by nlinarith)
  obtain ⟨hs, hn⟩ := s2e_anisotropic_norm_bound d k R hR E hE haxis t ht.le ht1.le
  refine ⟨r, hr, hs, ?_⟩
  have hl : r (Fin.last d) = R (Fin.last d) * t := by simp [r]
  rw [hl, mul_pow]
  calc
    _ ≤ s2e_divNorm d R E * t ^ (k + 1) := hn
    _ < η * (R (Fin.last d) ^ k * t ^ k) := by
      rw [pow_succ]
      have hlt : s2e_divNorm d R E * t < η * R (Fin.last d) ^ k := by nlinarith
      have := mul_lt_mul_of_pos_right hlt (pow_pos ht k)
      nlinarith

/-- A nonzero homogeneous polynomial has a nonzero evaluation away from the origin.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, regular direction for the initial homogeneous term; polynomial identity principle over an infinite field. -/
theorem s2e_s1i4_homogeneous_direction_aux
    (d k : ℕ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (hP : P ≠ 0) (hhom : P.IsHomogeneous k) :
    ∃ v : Fin (d + 1) → ℂ, v ≠ 0 ∧ MvPolynomial.eval v P ≠ 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    have hC := (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr hhom))
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h (Fin.last d)
      simpa using this
    · rw [hC]
      simpa using (show P.coeff 0 ≠ 0 from fun h =>
        hP (by rw [hC, h, map_zero]))
  · obtain ⟨v, hv⟩ : ∃ v, MvPolynomial.eval v P ≠ 0 := by
      by_contra h
      exact hP (hhom.eq_zero_of_forall_eval_eq_zero (by simpa using h))
    refine ⟨v, ?_, hv⟩
    intro h
    subst v
    apply hv
    rw [MvPolynomial.eval_zero]
    exact hhom.coeff_eq_zero (by simpa using Ne.symm hk)

/-- A nonzero direction can be the last column of a continuous linear coordinate change.
Source: Bourbaki, Algebra, Chapter II, §3, basis extension; Mathlib, finite-dimensional continuity of linear equivalences. -/
theorem s2e_s1i4_direction_basis_aux
    (d : ℕ) (v : Fin (d + 1) → ℂ) (hv : v ≠ 0) :
    ∃ L : (Fin (d + 1) → ℂ) ≃L[ℂ] (Fin (d + 1) → ℂ),
      L (Pi.single (Fin.last d) 1) = v := by
  classical
  have hu : (Pi.single (Fin.last d) 1 : Fin (d + 1) → ℂ) ≠ 0 := by
    intro h
    have := congrFun h (Fin.last d)
    simp at this
  obtain ⟨L, hL⟩ := s2e_linearEquiv_between_nonzero (K := ℂ) _ v hu hv
  exact ⟨L.toContinuousLinearEquiv, hL⟩

/-- Each total-degree layer of a formal series is an actual homogeneous polynomial.
Source: Mathlib, MvPolynomial.IsHomogeneous and finite total-degree monomial support; Gunning–Rossi, Chapter I, §B, homogeneous Taylor terms. -/
theorem s2e_s1i4_homogeneous_layer_aux
    (d n : ℕ) (F : MvPowerSeries (Fin (d + 1)) ℂ) :
    ∃ P : MvPolynomial (Fin (d + 1)) ℂ,
      P.IsHomogeneous n ∧
      (∀ a, P.coeff a =
        if a.sum (fun _ m => m) = n then MvPowerSeries.coeff a F else 0) ∧
      ∀ z, MvPolynomial.eval z P =
        ∑' a : Fin (d + 1) →₀ ℕ, if a.sum (fun _ m => m) = n then
          MvPowerSeries.coeff a F * ∏ i, z i ^ a i else 0 := by
  classical
  let P := MvPolynomial.homogeneousComponent n (F.truncTotal (n + 1))
  have hc (a : Fin (d + 1) →₀ ℕ) : P.coeff a =
      if a.sum (fun _ m => m) = n then MvPowerSeries.coeff a F else 0 := by
    change P.coeff a = if a.degree = n then MvPowerSeries.coeff a F else 0
    simp only [P, MvPolynomial.coeff_homogeneousComponent,
      MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs <;> first | rfl | omega
  refine ⟨P, MvPolynomial.homogeneousComponent_isHomogeneous _ _, hc, ?_⟩
  intro z
  rw [MvPolynomial.eval_eq']
  rw [tsum_eq_sum (s := P.support)]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [hc]
    split_ifs <;> simp
  · intro a ha
    have hz : P.coeff a = 0 := by simpa using ha
    rw [hc] at hz
    split_ifs at hz ⊢ <;> simp_all

end HodgeLean.Foundations.Program
