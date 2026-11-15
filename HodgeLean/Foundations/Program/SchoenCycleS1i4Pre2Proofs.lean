import HodgeLean.Foundations.Program.SchoenCycleS1i4PolynomialApproximation
import HodgeLean.Foundations.Program.SchoenCycleS1i4AlgebraicCoordinates
import HodgeLean.Foundations.Program.SchoenCycleS1i4Pre2Defs
import HodgeLean.Foundations.Program.SchoenCycleS1i4SumHelpers
import HodgeLean.Foundations.Program.SchoenCycleS1i4RemainderIdeals

/-! # Second native analytic comparison split
Implications from coefficient summability and explicit local comparison inputs.
Convergent division is new infrastructure; formal preparation alone is insufficient.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program
/-- Pure-power division satisfies the polydisc coefficient estimate.
Source: Serre, GAGA, §1, no. 4, printed p. 6; weighted coefficient proof of convergent division. -/
theorem s2e_s1i4_division_estimate_aux
    (d k : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (f : MvPowerSeries (Fin (d + 1)) ℂ)
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a)) :
    Summable (fun a => ‖MvPowerSeries.coeff a (s2e_divShift d k f)‖ * s2e_divWeight d r a) ∧
    (r (Fin.last d)) ^ k * s2e_divNorm d r (s2e_divShift d k f) ≤ s2e_divNorm d r f ∧
    s2e_divNorm d r (s2e_divRemainder d k f) ≤ s2e_divNorm d r f := by
  obtain ⟨hs, hb⟩ := s2e_shift_summable_bound d k r hr f hf
  refine ⟨hs, by simpa only [mul_comm] using (le_div_iff₀ (pow_pos (hr _) k)).mp hb, ?_⟩
  exact (s2e_remainder_summable_bound d k r hr f hf).2

/-- Quotient iterates converge absolutely in weighted coefficients.
Source: Serre, GAGA, §1, no. 4, printed p. 6; weighted coefficient proof of convergent division. -/
theorem s2e_s1i4_quotient_convergence_aux
    (d k : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (f : MvPowerSeries (Fin (d + 1)) ℂ)
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a))
    (e : MvPowerSeries (Fin (d + 1)) ℂ)
    (he : Summable (fun a => ‖MvPowerSeries.coeff a e‖ * s2e_divWeight d r a))
    (hsmall : s2e_divNorm d r e < (r (Fin.last d)) ^ k) :
    Summable (fun na : ℕ × (Fin (d + 1) →₀ ℕ) =>
      ‖MvPowerSeries.coeff na.2 (s2e_divShift d k ((s2e_divError d k e)^[na.1] f))‖ *
        s2e_divWeight d r na.2) := by
  let θ := s2e_divNorm d r e / r (Fin.last d) ^ k
  have hθ : 0 ≤ θ := div_nonneg (tsum_nonneg fun a =>
    mul_nonneg (norm_nonneg _) (s2e_divWeight_nonneg d r (fun i => (hr i).le) a))
    (pow_pos (hr _) _).le
  have hθ1 : θ < 1 := (div_lt_one (pow_pos (hr _) _)).mpr hsmall
  have hi := s2e_error_iterate_bound d k r hr e f he hf
  apply s2e_joint_summable_of_geometric _
    (fun n a => mul_nonneg (norm_nonneg _)
      (s2e_divWeight_nonneg d r (fun i => (hr i).le) a))
    (fun n => (s2e_shift_summable_bound d k r hr _ (hi n).1).1)
    (s2e_divNorm d r f / r (Fin.last d) ^ k) θ hθ hθ1
  intro n
  calc
    _ ≤ s2e_divNorm d r ((s2e_divError d k e)^[n] f) / r (Fin.last d) ^ k :=
      (s2e_shift_summable_bound d k r hr _ (hi n).1).2
    _ ≤ (θ ^ n * s2e_divNorm d r f) / r (Fin.last d) ^ k :=
      div_le_div_of_nonneg_right (hi n).2 (pow_pos (hr _) _).le
    _ = _ := by ring

/-- Remainder iterates converge absolutely in weighted coefficients.
Source: Serre, GAGA, §1, no. 4, printed p. 6; weighted coefficient proof of convergent division. -/
theorem s2e_s1i4_remainder_convergence_aux
    (d k : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (f : MvPowerSeries (Fin (d + 1)) ℂ)
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a))
    (e : MvPowerSeries (Fin (d + 1)) ℂ)
    (he : Summable (fun a => ‖MvPowerSeries.coeff a e‖ * s2e_divWeight d r a))
    (hsmall : s2e_divNorm d r e < (r (Fin.last d)) ^ k) :
    Summable (fun na : ℕ × (Fin (d + 1) →₀ ℕ) =>
      ‖MvPowerSeries.coeff na.2 (s2e_divRemainder d k ((s2e_divError d k e)^[na.1] f))‖ *
        s2e_divWeight d r na.2) := by
  let θ := s2e_divNorm d r e / r (Fin.last d) ^ k
  have hθ : 0 ≤ θ := div_nonneg (tsum_nonneg fun a =>
    mul_nonneg (norm_nonneg _) (s2e_divWeight_nonneg d r (fun i => (hr i).le) a))
    (pow_pos (hr _) _).le
  have hθ1 : θ < 1 := (div_lt_one (pow_pos (hr _) _)).mpr hsmall
  have hi := s2e_error_iterate_bound d k r hr e f he hf
  apply s2e_joint_summable_of_geometric _
    (fun n a => mul_nonneg (norm_nonneg _)
      (s2e_divWeight_nonneg d r (fun i => (hr i).le) a))
    (fun n => (s2e_remainder_summable_bound d k r hr _ (hi n).1).1)
    (s2e_divNorm d r f) θ hθ hθ1
  intro n
  exact (s2e_remainder_summable_bound d k r hr _ (hi n).1).2.trans (hi n).2

set_option maxHeartbeats 20000 in
/-- The geometric iteration gives division by the specified perturbed power.
Source: Serre, GAGA, §1, no. 4, printed p. 6; weighted coefficient proof of convergent division. -/
theorem s2e_s1i4_division_identity_aux
    (d k : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (f : MvPowerSeries (Fin (d + 1)) ℂ)
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a))
    (e : MvPowerSeries (Fin (d + 1)) ℂ)
    (he : Summable (fun a => ‖MvPowerSeries.coeff a e‖ * s2e_divWeight d r a))
    (hsmall : s2e_divNorm d r e < (r (Fin.last d)) ^ k) :
    let q : MvPowerSeries (Fin (d + 1)) ℂ := fun a =>
      ∑' n, MvPowerSeries.coeff a (s2e_divShift d k ((s2e_divError d k e)^[n] f))
    let b : MvPowerSeries (Fin (d + 1)) ℂ := fun a =>
      ∑' n, MvPowerSeries.coeff a (s2e_divRemainder d k ((s2e_divError d k e)^[n] f))
    f = (MvPowerSeries.X (Fin.last d) ^ k + e) * q + b := by
  classical
  let u := fun n => (s2e_divError d k e)^[n] f
  let v := fun n => s2e_divShift d k (u n)
  let w := fun n => s2e_divRemainder d k (u n)
  have hv := s2e_weighted_family_coeff_summable d r hr v
    (s2e_s1i4_quotient_convergence_aux d k r hr f hf e he hsmall)
  have hw := s2e_weighted_family_coeff_summable d r hr w
    (s2e_s1i4_remainder_convergence_aux d k r hr f hf e he hsmall)
  let θ := s2e_divNorm d r e / r (Fin.last d) ^ k
  have hθ : 0 ≤ θ := div_nonneg (tsum_nonneg fun a =>
    mul_nonneg (norm_nonneg _) (s2e_divWeight_nonneg d r (fun i => (hr i).le) a))
      (pow_pos (hr _) _).le
  have hθ1 : θ < 1 := (div_lt_one (pow_pos (hr _) _)).mpr hsmall
  have hi := s2e_error_iterate_bound d k r hr e f he hf
  have hujoint := s2e_joint_summable_of_geometric
    (fun n a => ‖MvPowerSeries.coeff a (u n)‖ * s2e_divWeight d r a)
    (fun n a => mul_nonneg (norm_nonneg _)
      (s2e_divWeight_nonneg d r (fun i => (hr i).le) a))
      (fun n => (hi n).1) (s2e_divNorm d r f) θ hθ hθ1 (fun n => (hi n).2)
  have hu := s2e_weighted_family_coeff_summable d r hr u hujoint
  have hstep (n) : u n = (MvPowerSeries.X (Fin.last d) ^ k + e) * v n + w n + u (n + 1) := by
    have hp := s2e_pure_power_division d k (u n)
    change u n = _ + _ + (s2e_divError d k e)^[n + 1] f
    rw [Function.iterate_succ_apply']
    change u n = _ + _ + -(e * v n)
    rw [add_mul]
    linear_combination hp
  let Q : MvPowerSeries (Fin (d + 1)) ℂ := fun a => ∑' n, MvPowerSeries.coeff a (v n)
  let B : MvPowerSeries (Fin (d + 1)) ℂ := fun a => ∑' n, MvPowerSeries.coeff a (w n)
  change f = (MvPowerSeries.X (Fin.last d) ^ k + e) * Q + B
  apply MvPowerSeries.ext
  intro a
  rw [map_add]
  have hsum := s2e_coeff_mul_sum d (MvPowerSeries.X (Fin.last d) ^ k + e) v hv a
  change MvPowerSeries.coeff a ((MvPowerSeries.X (Fin.last d) ^ k + e) * Q) = _ at hsum
  rw [hsum]
  change MvPowerSeries.coeff a f = (∑' n, MvPowerSeries.coeff a
    ((MvPowerSeries.X (Fin.last d) ^ k + e) * v n)) + ∑' n, MvPowerSeries.coeff a (w n)
  have hmul : Summable (fun n => MvPowerSeries.coeff a
      ((MvPowerSeries.X (Fin.last d) ^ k + e) * v n)) := by
    simp only [MvPowerSeries.coeff_mul]
    exact summable_sum (fun p _ => (hv p.2).mul_left _)
  have hs := (hu a).tsum_eq_zero_add
  have hs' : (∑' n, MvPowerSeries.coeff a (u n)) =
      ((∑' n, MvPowerSeries.coeff a ((MvPowerSeries.X (Fin.last d) ^ k + e) * v n)) +
       ∑' n, MvPowerSeries.coeff a (w n)) + ∑' n, MvPowerSeries.coeff a (u (n + 1)) := by
    rw [← hmul.tsum_add (hw a),
      ← (hmul.add (hw a)).tsum_add ((summable_nat_add_iff 1).mpr (hu a))]
    apply tsum_congr
    intro n
    simpa only [map_add] using congrArg (MvPowerSeries.coeff a) (hstep n)
  change (∑' n, MvPowerSeries.coeff a (u n)) = MvPowerSeries.coeff a f + _ at hs
  exact add_right_cancel (hs.symm.trans hs')

/-- A regular analytic divisor has analytic quotient and polynomial remainder.
Source: Serre, GAGA, §1, no. 4, printed p. 6; weighted coefficient proof of convergent division. -/
theorem s2e_s1i4_germ_division_aux
    (d k : ℕ) (g f : (Fin (d + 1) → ℂ) → ℂ)
    (hg : AnalyticAt ℂ g 0) (hf : AnalyticAt ℂ f 0)
    (hzero : ∀ j < k, iteratedDeriv j (fun t : ℂ => g (Pi.single (Fin.last d) t)) 0 = 0)
    (hlead : iteratedDeriv k (fun t : ℂ => g (Pi.single (Fin.last d) t)) 0 ≠ 0) :
    ∃ q : (Fin (d + 1) → ℂ) → ℂ, ∃ b : Fin k → (Fin d → ℂ) → ℂ,
      AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (b i) 0) ∧
      f =ᶠ[nhds 0] (fun z => g z * q z +
        ∑ i : Fin k, b i (fun j => z j.castSucc) * z (Fin.last d) ^ (i : ℕ)) := by
  classical
  obtain ⟨R, F, hR, hF, hfF⟩ := s2e_s1i4_analytic_coefficients_aux d f hf 1 zero_lt_one
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ R
    (show (Finset.univ : Finset (Fin (d + 1))).Nonempty from ⟨Fin.last d, Finset.mem_univ _⟩)
  obtain ⟨c, r, e, hc, hr, he, hsmall, hgG⟩ :=
    s2e_s1i4_normalized_smallness_aux d k g hg hzero hlead (R i) (hR i).1
  have hrpos (j) := (hr j).1
  have hFr := s2e_weighted_summable_mono d r R hrpos
    (fun j => (hr j).2.le.trans (hmin j (Finset.mem_univ _))) F hF
  let u := fun n => (s2e_divError d k e)^[n] F
  let Q : MvPowerSeries (Fin (d + 1)) ℂ := fun a =>
    ∑' n, MvPowerSeries.coeff a (s2e_divShift d k (u n))
  let B : MvPowerSeries (Fin (d + 1)) ℂ := fun a =>
    ∑' n, MvPowerSeries.coeff a (s2e_divRemainder d k (u n))
  have hQ := s2e_weighted_sum_summable d r hrpos
    (fun n => s2e_divShift d k (u n))
    (s2e_s1i4_quotient_convergence_aux d k r hrpos F hFr e he hsmall)
  have hB := s2e_weighted_sum_summable d r hrpos
    (fun n => s2e_divRemainder d k (u n))
    (s2e_s1i4_remainder_convergence_aux d k r hrpos F hFr e he hsmall)
  have hidentity : F = (MvPowerSeries.X (Fin.last d) ^ k + e) * Q + B :=
    s2e_s1i4_division_identity_aux d k r hrpos F hFr e he hsmall
  have hdegree (a) (ha : k ≤ a (Fin.last d)) : MvPowerSeries.coeff a B = 0 := by
    change (∑' n, MvPowerSeries.coeff a (s2e_divRemainder d k (u n))) = 0
    have hz (n) : MvPowerSeries.coeff a (s2e_divRemainder d k (u n)) = 0 := by
      change (if a (Fin.last d) < k then _ else 0) = 0
      exact if_neg (not_lt.mpr ha)
    simp only [hz, tsum_zero]
  obtain ⟨b, hb, hBb⟩ := s2e_s1i4_remainder_realization_aux d k r hrpos B hB hdegree
  have hQa := (s2e_s1i4_series_realization_aux d r hrpos Q hQ).1
  have hG := s2e_weighted_sub_summable d r hrpos
    (MvPowerSeries.X (Fin.last d) ^ k) (-e) (s2e_weighted_X_pow_summable d k r)
    (by simpa only [map_neg, norm_neg] using he)
  rw [sub_neg_eq_add] at hG
  have ht := s2e_s1i4_analytic_transport_aux d r hrpos F
    (MvPowerSeries.X (Fin.last d) ^ k + e) Q B hG hQ hB hidentity
  refine ⟨fun z => c * s2e_divSeries (d + 1) Q z, b, analyticAt_const.mul hQa, hb, ?_⟩
  filter_upwards [hfF, hgG, ht, hBb] with z hfz hgz htz hbz
  rw [hfz, htz, ← hgz, hbz]
  ring

/-- Division in one more variable gives finite generation of each germ ideal.
Source: Serre, GAGA, §1, no. 4, printed p. 6; weighted coefficient proof of convergent division. -/
theorem s2e_s1i4_ideal_induction_aux
    (d : ℕ) (hprev : IsNoetherianRing (s2e_nativeAnalyticGermRing d))
    (hdivision : ∀ (k : ℕ) (g f : (Fin (d + 1) → ℂ) → ℂ)
    (_hg : AnalyticAt ℂ g 0) (_hf : AnalyticAt ℂ f 0)
    (_hzero : ∀ j < k, iteratedDeriv j (fun t : ℂ => g (Pi.single (Fin.last d) t)) 0 = 0)
    (_hlead : iteratedDeriv k (fun t : ℂ => g (Pi.single (Fin.last d) t)) 0 ≠ 0),
      ∃ q : (Fin (d + 1) → ℂ) → ℂ, ∃ b : Fin k → (Fin d → ℂ) → ℂ,
      AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (b i) 0) ∧
      f =ᶠ[nhds 0] (fun z => g z * q z +
        ∑ i : Fin k, b i (fun j => z j.castSucc) * z (Fin.last d) ^ (i : ℕ))) (I : Ideal (s2e_nativeAnalyticGermRing (d + 1))) :
    I.FG := by
  classical
  by_cases hI : I = ⊥
  · rw [hI]
    exact Submodule.fg_bot
  obtain ⟨a, ha, hane⟩ := (Submodule.ne_bot_iff I).mp hI
  obtain ⟨f, hf, he⟩ := a.property
  have hfne : ¬ f =ᶠ[nhds 0] 0 := by
    intro hz
    apply hane
    apply Subtype.ext
    exact he.symm.trans (Filter.Germ.coe_eq.mpr hz)
  obtain ⟨L, k, hz, hl⟩ := s2e_s1i4_linear_regularization_aux d f hf hfne
  let E := s2e_nativeAnalytic_linearEquiv (d + 1) L
  let J := I.map E.toRingHom
  have hfg : AnalyticAt ℂ (f ∘ L) 0 := hf.comp_of_eq (L.analyticAt 0) (map_zero L)
  have hEa : (⟨Filter.Germ.ofFun (f ∘ L), ⟨f ∘ L, hfg, rfl⟩⟩ :
      s2e_nativeAnalyticGermRing (d + 1)) = E a := by
    apply Subtype.ext
    change Filter.Germ.ofFun (f ∘ L) = a.val.compTendsto L
      (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0))
    rw [← he]
    rfl
  have hJ : J.FG := s2e_analytic_ideal_fg_of_regular d k hprev J (f ∘ L) hfg
    (hEa ▸ Ideal.mem_map_of_mem E.toRingHom ha)
    (fun t ht => hdivision k (f ∘ L) t hfg ht hz hl)
  have hh := hJ.map E.symm.toRingHom
  change (I.map E.toRingHom).map E.symm.toRingHom |>.FG at hh
  rw [Ideal.map_map, show E.symm.toRingHom.comp E.toRingHom = RingHom.id _ from
    RingHom.ext (fun b => E.symm_apply_apply b), Ideal.map_id] at hh
  exact hh

/-- Centered actual coordinate polynomials represent algebraic finite-order classes.
Source: SGA 1, Exposé I, étale local coordinates; Serre, GAGA, §2, no. 6, Proposition 3. -/
theorem s2e_s1i4_algebraic_representatives_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (N : ℕ)
    (a : X.left.presheaf.stalk p.underlying) :
    ∃ q : MvPolynomial (Fin d) ℂ,
      a - s2e_actual_centeredPolynomial_stalk X d p q ∈
        IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N := by
  let e := (s2e_nativeAnalyticGerm_value d).comp (s2e_stalk_nativeAnalyticGerm X d p)
  apply s2e_polynomial_approximation_of_local_generators d
    (s2e_actual_centeredPolynomial_stalk X d p) e
    (fun c => ?_) (s2e_actual_maximalIdeal_centered_coordinates X d p) N a
  change s2e_nativeAnalyticGerm_value d (s2e_stalk_nativeAnalyticGerm X d p
    (s2e_actual_centeredPolynomial_stalk X d p (MvPolynomial.C c))) = c
  rw [s2e_actual_centeredPolynomial_nativeAnalytic, s2e_nativeAnalytic_polynomial_value,
    MvPolynomial.constantCoeff_C]

/-- Polynomial approximation and analytic polynomial order detect algebraic order.
Source: Serre, GAGA, §2, no. 6, Proposition 3. -/
theorem s2e_s1i4_order_reflection_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (N : ℕ)
    (hrep : ∀ a : X.left.presheaf.stalk p.underlying,
      ∃ q : MvPolynomial (Fin d) ℂ,
        a - s2e_actual_centeredPolynomial_stalk X d p q ∈
          IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N)
    (a : X.left.presheaf.stalk p.underlying)
    (ha : s2e_stalk_nativeAnalyticGerm X d p a ∈
      IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d) ^ N) :
    a ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N := by
  obtain ⟨q, hq⟩ := hrep a
  have hmap : (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N).map
      (s2e_stalk_nativeAnalyticGerm X d p) ≤
      IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d) ^ N := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le _) N
  have hdiff := hmap (Ideal.mem_map_of_mem _ hq)
  rw [map_sub, s2e_actual_centeredPolynomial_nativeAnalytic] at hdiff
  have hpoly := (s2e_nativeAnalytic_polynomial_order_iff d N q).mp
    (by simpa only [sub_sub_cancel] using
      (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d) ^ N).sub_mem ha hdiff)
  have hpoly' : s2e_actual_centeredPolynomial_stalk X d p q ∈
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N := by
    have hle : ((MvPolynomial.idealOfVars (Fin d) ℂ) ^ N).map
        (s2e_actual_centeredPolynomial_stalk X d p) ≤
        IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' (s2e_actual_centeredPolynomial_map_variableIdeal_le X d p) N
    exact hle (Ideal.mem_map_of_mem _ hpoly)
  simpa only [sub_add_cancel] using
    (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N).add_mem hq hpoly' 

/-- The actual local comparison extends the maximal ideal to the analytic maximal ideal.
Source: Serre, GAGA, §2, no. 6, Proposition 3; native analytic coordinate generators. -/
theorem s2e_s1i4_extended_maximal_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying)).map
      (s2e_stalk_nativeAnalyticGerm X d p) =
        IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d) := by
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le _)
  have hcomp : (s2e_stalk_nativeAnalyticGerm X d p).comp
      (s2e_actual_centeredPolynomial_stalk X d p) = s2e_nativeAnalytic_polynomial d := by
    apply RingHom.ext
    intro q
    exact s2e_actual_centeredPolynomial_nativeAnalytic X d p q
  rw [← s2e_nativeAnalytic_map_variableIdeal, ← hcomp, ← Ideal.map_map]
  exact Ideal.map_mono (s2e_actual_centeredPolynomial_map_variableIdeal_le X d p)

/-- Finite order reflection identifies the actual adic rings.
Source: Serre, GAGA, §2, no. 6, Proposition 3; inverse limits of finite quotients. -/
theorem s2e_s1i4_adic_bijective_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X)
    (horder : ∀ (N : ℕ) (a : X.left.presheaf.stalk p.underlying),
      s2e_stalk_nativeAnalyticGerm X d p a ∈
        IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d) ^ N →
      a ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N) :
    Function.Bijective (s2e_actualAnalytic_adic_stalkMap X d p) := by
  apply s2e_adic_ring_map_bijective
  intro N
  refine ⟨?_, s2e_actualAnalytic_finite_stalkMap_surjective X d p N⟩
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.mpr
  apply horder N (a - b)
  rw [map_sub]
  exact Ideal.Quotient.eq.mp hab

end HodgeLean.Foundations.Program
