import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Complex-analytic foundations for the cover dictionary (proof obligations)

One open auxiliary per statement of `CoverAnalytic.lean`. Mathlib only.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem caf_meromorphicAt_of_norm_le_aux [FiniteDimensional ℂ E] (f : ℂ → E) (z₀ : ℂ) (N : ℕ)
    (C : ℝ) (hf : ∀ᶠ z in 𝓝[≠] z₀, AnalyticAt ℂ f z)
    (hb : ∀ᶠ z in 𝓝[≠] z₀, ‖f z‖ ≤ C / ‖z - z₀‖ ^ N) :
    MeromorphicAt f z₀ ∧ ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z₀ := by
  classical
  let := FiniteDimensional.complete ℂ E
  let h : ℂ → E := fun z ↦ (z - z₀) ^ N • f z
  have hd : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ h z := by
    filter_upwards [hf] with z hz
    exact (((analyticAt_id.sub analyticAt_const).pow N).smul hz).differentiableAt
  have hb' : ∀ᶠ z in 𝓝[≠] z₀, ‖h z‖ ≤ C := by
    filter_upwards [hb, self_mem_nhdsWithin] with z hz hn
    have hn' : ‖z - z₀‖ ^ N ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hn))
    calc
      ‖h z‖ = ‖z - z₀‖ ^ N * ‖f z‖ := by simp [h, norm_smul]
      _ ≤ ‖z - z₀‖ ^ N * (C / ‖z - z₀‖ ^ N) := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = C := by field_simp
  obtain ⟨s, hs, hsd⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hd.and hb')
  let g := Function.update h z₀ (limUnder (𝓝[≠] z₀) h)
  have hg : AnalyticAt ℂ g z₀ := by
    apply (Complex.differentiableOn_update_limUnder_of_bddAbove hs
      (fun z hz ↦ (hsd hz).1.differentiableWithinAt) ?_).analyticAt hs
    exact ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact (hsd hz).2⟩
  have heq : f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ (-(N : ℤ)) • g z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    simp [g, Function.update_of_ne hz, h, zpow_neg, zpow_natCast, smul_smul, hn]
  have hp : MeromorphicAt (fun z : ℂ ↦ (z - z₀) ^ (-(N : ℤ))) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).zpow _
  have hm := hp.smul hg.meromorphicAt
  refine ⟨hm.congr heq.symm, ?_⟩
  rw [meromorphicOrderAt_congr heq]
  change ((-(N : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt ((fun z ↦ (z - z₀) ^ (-(N : ℤ))) • g) z₀
  rw [meromorphicOrderAt_smul hp hg.meromorphicAt]
  have ho : meromorphicOrderAt (fun z : ℂ ↦ (z - z₀) ^ (-(N : ℤ))) z₀ = ((-(N : ℤ)) : WithTop ℤ) := by
    exact meromorphicOrderAt_zpow_id_sub_const
  rw [ho]
  simpa [add_comm] using add_le_add_left hg.meromorphicOrderAt_nonneg ((-(N : ℤ) : ℤ) : WithTop ℤ)

theorem caf_ray_bound (f : ℂ → E) (B : ℂ → E →L[ℂ] E) (z₀ w : ℂ)
    (r K T : ℝ) (hw : w ≠ 0) (hwr : ‖w‖ < r) (hT : 0 ≤ T)
    (hode : ∀ z ∈ ball z₀ r \ {z₀}, HasDerivAt f (B z (f z)) z)
    (hB : ∀ z ∈ ball z₀ r \ {z₀}, ‖B z‖ ≤ K / ‖z - z₀‖) :
    ‖f (z₀ + (Real.exp (-T) : ℂ) * w)‖ ≤ ‖f (z₀ + w)‖ * Real.exp (K * T) := by
  let γ : ℝ → ℂ := fun t ↦ z₀ + (Real.exp (-t) : ℂ) * w
  have hγ (t : ℝ) : HasDerivAt γ (-(Real.exp (-t) : ℂ) * w) t := by
    convert ((((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).ofReal_comp).mul_const w).const_add z₀ using 1 <;>
      simp [γ]
  have hmem (t : ℝ) (ht : 0 ≤ t) : γ t ∈ ball z₀ r \ {z₀} := by
    have he : 0 < Real.exp (-t) := Real.exp_pos _
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    constructor
    · rw [mem_ball, dist_eq_norm]
      have hn : ‖γ t - z₀‖ = Real.exp (-t) * ‖w‖ := by simp only [γ, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
      rw [hn]
      exact (mul_le_of_le_one_left (norm_nonneg _) he1).trans_lt hwr
    · simpa [γ] using mul_ne_zero (Complex.ofReal_ne_zero.mpr he.ne') hw
  let F : ℝ → E := fun t ↦ f (γ t)
  let F' : ℝ → E := fun t ↦ (-(Real.exp (-t) : ℂ) * w) • B (γ t) (f (γ t))
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt F (F' t) t :=
    (hode _ (hmem t ht)).scomp t (hγ t)
  have hb (t : ℝ) (ht : 0 ≤ t) : ‖F' t‖ ≤ K * ‖F t‖ + 0 := by
    have he : 0 < Real.exp (-t) := Real.exp_pos _
    have hn : ‖γ t - z₀‖ = Real.exp (-t) * ‖w‖ := by simp only [γ, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
    have hpos : 0 < Real.exp (-t) * ‖w‖ := mul_pos he (norm_pos_iff.mpr hw)
    calc
      ‖F' t‖ ≤ (Real.exp (-t) * ‖w‖) * (‖B (γ t)‖ * ‖F t‖) := by
        simpa only [F', F, norm_smul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he] using
          mul_le_mul_of_nonneg_left ((B (γ t)).le_opNorm (f (γ t))) (norm_nonneg (-(Real.exp (-t) : ℂ) * w))
      _ ≤ (Real.exp (-t) * ‖w‖) * ((K / (Real.exp (-t) * ‖w‖)) * ‖F t‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by simpa [hn] using hB _ (hmem t ht)) (norm_nonneg _)) hpos.le
      _ = _ := by field_simp; ring
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun t ht ↦ (hd t ht.1).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t ht.1).hasDerivWithinAt) (le_refl ‖F 0‖)
    (fun t ht ↦ hb t ht.1) T (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  simpa [F, γ, gronwallBound_ε0] using h

theorem caf_meromorphicAt_of_linear_ode_aux [FiniteDimensional ℂ E] (f : ℂ → E)
    (B : ℂ → E →L[ℂ] E) (z₀ : ℂ) (r K : ℝ) (hr : 0 < r)
    (hode : ∀ z ∈ ball z₀ r \ {z₀}, HasDerivAt f (B z (f z)) z)
    (hB : ∀ z ∈ ball z₀ r \ {z₀}, ‖B z‖ ≤ K / ‖z - z₀‖) :
    MeromorphicAt f z₀ := by
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hRr : R < r := half_lt_self hr
  have hmem (z : ℂ) (hz : z ∈ sphere z₀ R) : z ∈ ball z₀ r \ {z₀} := by
    have hz' : ‖z - z₀‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
    exact ⟨by simpa only [mem_ball, dist_eq_norm, hz'] using hRr,
      by simpa only [mem_singleton_iff] using (sub_ne_zero.mp (norm_pos_iff.mp (hz' ▸ hR)))⟩
  obtain ⟨C, hC⟩ := (isCompact_sphere z₀ R).bddAbove_image
    (show ContinuousOn (fun z ↦ ‖f z‖) (sphere z₀ R) from
      fun z hz ↦ (hode z (hmem z hz)).continuousAt.norm.continuousWithinAt)
  obtain ⟨N, hN⟩ := exists_nat_gt K
  have hfa : ∀ᶠ z in 𝓝[≠] z₀, AnalyticAt ℂ f z := by
    have hdiff : DifferentiableOn ℂ f (ball z₀ r \ {z₀}) := fun z hz ↦
      (hode z hz).differentiableAt.differentiableWithinAt
    have hopen : IsOpen (ball z₀ r \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
    have hev : ball z₀ r \ {z₀} ∈ 𝓝[≠] z₀ :=
      inter_mem (nhdsWithin_le_nhds (ball_mem_nhds z₀ hr)) self_mem_nhdsWithin
    filter_upwards [hev] with z hz
    exact hdiff.analyticAt (hopen.mem_nhds hz)
  apply (caf_meromorphicAt_of_norm_le_aux f z₀ N (C * R ^ N) hfa ?_).1
  have hev : ∀ᶠ z in 𝓝[≠] z₀, ‖z - z₀‖ < R := by
    exact nhdsWithin_le_nhds (by simpa only [Metric.ball, dist_eq_norm] using ball_mem_nhds z₀ hR)
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hn
  let a := ‖z - z₀‖
  have ha : 0 < a := norm_pos_iff.mpr (sub_ne_zero.mpr hn)
  let w : ℂ := ((R / a : ℝ) : ℂ) * (z - z₀)
  have hw : ‖w‖ = R := by
    simp only [w, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hR ha)]
    change R / a * a = R
    field_simp
  have hwn : w ≠ 0 := norm_pos_iff.mp (hw ▸ hR)
  let T := Real.log (R / a)
  have hT : 0 ≤ T := Real.log_nonneg ((one_le_div ha).mpr hz.le)
  have hexp : Real.exp (-T) = a / R := by
    rw [Real.exp_neg, Real.exp_log (div_pos hR ha)]
    exact inv_div _ _
  have hpoint : z₀ + (Real.exp (-T) : ℂ) * w = z := by
    rw [hexp]
    dsimp [w]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne', Complex.ofReal_ne_zero.mpr hR.ne']
    <;> ring
  have hbound := caf_ray_bound f B z₀ w r K T hwn (hw ▸ hRr) hT hode hB
  rw [hpoint] at hbound
  have hwC : ‖f (z₀ + w)‖ ≤ C := hC (mem_image_of_mem _ (by simpa only [mem_sphere, dist_eq_norm, add_sub_cancel_left, hw]))
  have heN : Real.exp (K * T) ≤ (R / a) ^ N := by
    calc
      _ ≤ Real.exp ((N : ℝ) * T) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hN.le hT)
      _ = (Real.exp T) ^ N := by rw [Real.exp_nat_mul]
      _ = _ := by rw [Real.exp_log (div_pos hR ha)]
  calc
    ‖f z‖ ≤ ‖f (z₀ + w)‖ * Real.exp (K * T) := hbound
    _ ≤ ‖f (z₀ + w)‖ * (R / a) ^ N := mul_le_mul_of_nonneg_left heN (norm_nonneg _)
    _ ≤ C * (R / a) ^ N := mul_le_mul_of_nonneg_right hwC (by positivity)
    _ = C * R ^ N / ‖z - z₀‖ ^ N := by rw [div_pow, mul_div_assoc]

theorem caf_order_eigenvalue_complete [CompleteSpace E] (f : ℂ → E) (z₀ : ℂ)
    (A₀ : E →L[ℂ] E) (G : ℂ → E →L[ℂ] E) (m : ℤ) (hf : MeromorphicAt f z₀)
    (hm : meromorphicOrderAt f z₀ = (m : WithTop ℤ)) (hG : ContinuousAt G z₀)
    (hode : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) • deriv f z = A₀ (f z) + (z - z₀) • G z (f z)) :
    ∃ v : E, v ≠ 0 ∧ A₀ v = (m : ℂ) • v := by
  obtain ⟨g, hg, hgn, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hm
  have hd := Filter.EventuallyEq.nhdsNE_deriv hfg
  have heq : ∀ᶠ z in 𝓝[≠] z₀,
      (m : ℂ) • g z + (z - z₀) • deriv g z = A₀ (g z) + (z - z₀) • G z (g z) := by
    filter_upwards [hd, hfg, hode, nhdsWithin_le_nhds hg.eventually_analyticAt,
      self_mem_nhdsWithin] with z hdz hfz ho hgz hn
    have hn' : z - z₀ ≠ 0 := sub_ne_zero.mpr hn
    have hpz : DifferentiableAt ℂ (fun w : ℂ ↦ (w - z₀) ^ m) z :=
      (differentiableAt_id.sub_const z₀).zpow (Or.inl hn')
    rw [hdz, deriv_fun_smul hpz hgz.differentiableAt,
      deriv_comp_sub_const (f := fun w : ℂ ↦ w ^ m), deriv_zpow, hfz] at ho
    have hpow : (z - z₀) * ((m : ℂ) * (z - z₀) ^ (m - 1)) =
        (z - z₀) ^ m * (m : ℂ) := by
      rw [zpow_sub₀ hn', zpow_one]
      field_simp
    have ho' : (z - z₀) ^ m • ((m : ℂ) • g z + (z - z₀) • deriv g z) =
        (z - z₀) ^ m • (A₀ (g z) + (z - z₀) • G z (g z)) := by
      convert ho using 1 <;> simp only [smul_add, smul_smul, map_smul] <;>
        simp only [hpow, mul_comm] <;> module
    exact (smul_right_inj (zpow_ne_zero _ hn')).mp ho'
  have hlc : ContinuousAt (fun z ↦ (m : ℂ) • g z + (z - z₀) • deriv g z) z₀ :=
    (hg.continuousAt.const_smul (m : ℂ)).add
      ((continuousAt_id.sub continuousAt_const).smul hg.deriv.continuousAt)
  have hrc : ContinuousAt (fun z ↦ A₀ (g z) + (z - z₀) • G z (g z)) z₀ :=
    (A₀.continuous.continuousAt.comp hg.continuousAt).add
      ((continuousAt_id.sub continuousAt_const).smul (hG.clm_apply hg.continuousAt))
  have hl : Tendsto (fun z ↦ (m : ℂ) • g z + (z - z₀) • deriv g z)
      (𝓝[≠] z₀) (𝓝 ((m : ℂ) • g z₀)) := by
    simpa only [sub_self, zero_smul, add_zero] using hlc.tendsto.mono_left (show 𝓝[≠] z₀ ≤ 𝓝 z₀ from nhdsWithin_le_nhds)
  have hr : Tendsto (fun z ↦ A₀ (g z) + (z - z₀) • G z (g z))
      (𝓝[≠] z₀) (𝓝 (A₀ (g z₀))) := by
    simpa only [sub_self, zero_smul, add_zero] using hrc.tendsto.mono_left (show 𝓝[≠] z₀ ≤ 𝓝 z₀ from nhdsWithin_le_nhds)
  exact ⟨g z₀, hgn, (tendsto_nhds_unique (hl.congr' heq) hr).symm⟩

theorem caf_order_eigenvalue_aux [CompleteSpace E] (f : ℂ → E) (z₀ : ℂ) (A₀ : E →L[ℂ] E)
    (G : ℂ → E →L[ℂ] E) (m : ℤ) (hf : MeromorphicAt f z₀)
    (hm : meromorphicOrderAt f z₀ = (m : WithTop ℤ)) (hG : ContinuousAt G z₀)
    (hode : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) • deriv f z = A₀ (f z) + (z - z₀) • G z (f z)) :
    ∃ v : E, v ≠ 0 ∧ A₀ v = (m : ℂ) • v :=
  caf_order_eigenvalue_complete f z₀ A₀ G m hf hm hG hode

theorem caf_rotation_coeff (f : ℂ → E) (p : FormalMultilinearSeries ℂ ℂ E)
    (ζ : ℂ) (e k n : ℕ) (hζ : IsPrimitiveRoot ζ e) (hk : k < e)
    (hp : HasFPowerSeriesAt f p 0)
    (hrot : ∀ᶠ y in 𝓝 (0 : ℂ), f (ζ * y) = ζ ^ k • f y)
    (hn : n % e ≠ k) : p.coeff n = 0 := by
  let u : ℂ →L[ℂ] ℂ := ζ • ContinuousLinearMap.id ℂ ℂ
  have hl : HasFPowerSeriesAt (f ∘ u) (p.compContinuousLinearMap u) 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    simpa [u] using hp
  have hr := hp.const_smul (c := ζ ^ k)
  have heq := hl.eq_formalMultilinearSeries (hr.congr (by
    exact (show (fun y ↦ f (ζ * y)) =ᶠ[𝓝 0] (fun y ↦ ζ ^ k • f y) from hrot).symm))
  have hc := congrArg (fun q : FormalMultilinearSeries ℂ ℂ E ↦ q.coeff n) heq
  have hc' : ζ ^ n • p.coeff n = ζ ^ k • p.coeff n := by
    change p n (fun _ ↦ ζ * 1) = ζ ^ k • p.coeff n at hc
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff] at hc
    simpa only [mul_one, Finset.prod_const, Finset.card_fin] using hc
  have hne : ζ ^ n ≠ ζ ^ k := by
    intro he
    apply hn
    apply hζ.pow_inj (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hk)) hk
    rw [hζ.eq_orderOf, pow_mod_orderOf]
    exact he
  exact (smul_eq_zero.mp (show (ζ ^ n - ζ ^ k) • p.coeff n = 0 by
    rw [sub_smul, hc', sub_self])).resolve_left (sub_ne_zero.mpr hne)

theorem caf_rotation_factor_aux [FiniteDimensional ℂ E] (f : ℂ → E) (e k : ℕ) (hk : k < e)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ e) (hf : AnalyticAt ℂ f 0)
    (hrot : ∀ᶠ y in 𝓝 (0 : ℂ), f (ζ * y) = ζ ^ k • f y) :
    ∃ g : ℂ → E, AnalyticAt ℂ g 0 ∧ ∀ᶠ y in 𝓝 (0 : ℂ), f y = y ^ k • g (y ^ e) := by
  classical
  let := FiniteDimensional.complete ℂ E
  obtain ⟨p, hp⟩ := hf
  have he : 0 < e := lt_of_le_of_lt (Nat.zero_le k) hk
  let q : FormalMultilinearSeries ℂ ℂ E := fun n ↦
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (p.coeff (k + e * n))
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.radius_pos
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr0
  obtain ⟨C, hC, hpC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  have hqR : (r ^ e : ENNReal) ≤ q.radius := by
    apply q.le_radius_of_bound (C / (r : ℝ) ^ k)
    intro n
    have h := hpC (k + e * n)
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef] at h
    simp only [q, ContinuousMultilinearMap.norm_mkPiRing, NNReal.coe_pow]
    apply (le_div_iff₀ (pow_pos hrpos k)).mpr
    convert h using 1 <;> rw [pow_add, pow_mul] <;> ring
  have hqpos : 0 < q.radius := (by positivity : (0 : ENNReal) < r ^ e).trans_le hqR
  refine ⟨q.sum, (q.hasFPowerSeriesOnBall hqpos).analyticAt, ?_⟩
  filter_upwards [hp.eventually_hasSum] with y hy
  have hinj : Function.Injective (fun n : ℕ ↦ k + e * n) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left he (Nat.add_left_cancel h)
  have hsupport : Function.support (fun n ↦ p n (fun _ ↦ y)) ⊆ Set.range (fun n ↦ k + e * n) := by
    intro n hn
    have hmod : n % e = k := by
      by_contra h
      have hz := caf_rotation_coeff f p ζ e k n hζ hk hp hrot h
      exact hn (by simp [FormalMultilinearSeries.apply_eq_prod_smul_coeff, hz])
    exact ⟨n / e, by change k + e * (n / e) = n; rw [← hmod, Nat.mod_add_div]⟩
  have hsum := hinj.tsum_eq hsupport
  have hterms (n : ℕ) : p (k + e * n) (fun _ ↦ y) =
      y ^ k • q n (fun _ ↦ y ^ e) := by
    simp [q, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      ContinuousMultilinearMap.mkPiRing, smul_smul, pow_add, pow_mul]
  calc
    f y = ∑' n, p n (fun _ ↦ y) := by simpa using hy.tsum_eq.symm
    _ = ∑' n, p (k + e * n) (fun _ ↦ y) := hsum.symm
    _ = ∑' n, y ^ k • q n (fun _ ↦ y ^ e) := tsum_congr hterms
    _ = y ^ k • q.sum (y ^ e) := by rw [tsum_const_smul'']; rfl

theorem caf_meromorphicAt_of_comp_pow_aux [FiniteDimensional ℂ E] (F : ℂ → E) (t : ℂ) (e : ℕ)
    (he : 0 < e) (hF : ∀ᶠ s in 𝓝[≠] t, AnalyticAt ℂ F s)
    (hm : MeromorphicAt (fun y : ℂ ↦ F (t + y ^ e)) 0) :
    MeromorphicAt F t := by
  obtain ⟨N, hN⟩ := hm
  let H : ℂ → E := fun y ↦ (y - 0) ^ N • F (t + y ^ e)
  have hbound : ∀ᶠ y in 𝓝 (0 : ℂ), ‖H y‖ < ‖H 0‖ + 1 :=
    hN.continuousAt.norm (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hbδ⟩ := Metric.eventually_nhds_iff.mp hbound
  let ρ := min δ 1
  have hρ : 0 < ρ := lt_min hδ zero_lt_one
  apply (caf_meromorphicAt_of_norm_le_aux F t N (‖H 0‖ + 1) hF ?_).1
  have hev : ∀ᶠ s in 𝓝[≠] t, ‖s - t‖ < ρ ^ e := by
    exact nhdsWithin_le_nhds (by simpa only [Metric.ball, dist_eq_norm] using
      (Metric.ball_mem_nhds t (pow_pos hρ e)))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hn
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (s - t) he
  have hnorm : ‖y‖ ^ e = ‖s - t‖ := by rw [← norm_pow, hy]
  have hyρ : ‖y‖ < ρ := by
    by_contra h
    have := pow_le_pow_left₀ hρ.le (le_of_not_gt h) e
    rw [hnorm] at this
    exact (not_lt_of_ge this) hs
  have hyδ : dist y 0 < δ := by
    simpa [dist_eq_norm] using hyρ.trans_le (min_le_left δ 1)
  have hy1 : ‖y‖ ≤ 1 := hyρ.le.trans (min_le_right δ 1)
  have hpow : ‖s - t‖ ^ N ≤ ‖y‖ ^ N := by
    rw [← hnorm, ← pow_mul]
    exact pow_le_pow_of_le_one (norm_nonneg y) hy1 (by nlinarith : N ≤ e * N)
  have hbH := (hbδ hyδ).le
  have hty : t + y ^ e = s := by rw [hy]; ring
  have hbmul : ‖s - t‖ ^ N * ‖F s‖ ≤ ‖H 0‖ + 1 := by
    calc
      _ ≤ ‖y‖ ^ N * ‖F s‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = ‖H y‖ := by simp [H, norm_smul, hty]
      _ ≤ _ := hbH
  exact (le_div_iff₀ (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) N)).mpr
    (by simpa [mul_comm] using hbmul)

theorem caf_polynomial_of_sphere_growth (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (N : ℕ) (C : ℝ)
    (hb : ∀ᶠ R : ℝ in atTop, ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C * R ^ N) :
    ∃ P : Polynomial ℂ, ∀ z, f z = P.eval z := by
  classical
  let p : FormalMultilinearSeries ℂ ℂ ℂ := cauchyPowerSeries f 0 (1 : ℝ)

  have hp : HasFPowerSeriesOnBall f p 0 ⊤ := by
    simpa only [p, NNReal.coe_one] using! (hf.hasFPowerSeriesOnBall (R := 1) 0 (by norm_num))

  have hz (n : ℕ) (hn : N < n) : p.coeff n = 0 := by
    have hb' : ∀ᶠ R : ℝ in atTop, ‖p n‖ ≤ C / R ^ (n - N) := by
      filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with R hR hRpos

      have hpR := hf.hasFPowerSeriesOnBall 0 (show (0 : NNReal) < ⟨R, hRpos.le⟩ from hRpos)
      have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hpR.hasFPowerSeriesAt

      have hbound : ∀ z ∈ sphere (0 : ℂ) R,
          ‖(z - 0)⁻¹ ^ n • (z - 0)⁻¹ • f z‖ ≤ C * R ^ N / (R ^ n * R) := by
        intro z hz
        have hnz : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
        calc
          _ = R⁻¹ ^ n * (R⁻¹ * ‖f z‖) := by simp only [norm_smul, norm_pow, norm_inv, sub_zero, hnz]
          _ ≤ R⁻¹ ^ n * (R⁻¹ * (C * R ^ N)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hR z hz) (by positivity)) (by positivity)
          _ = _ := by rw [inv_pow]; field_simp

      have hi := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hRpos.le hbound
      rw [heq]
      change ‖ContinuousMultilinearMap.mkPiRing ℂ (Fin n) _‖ ≤ _
      rw [ContinuousMultilinearMap.norm_mkPiRing]
      refine hi.trans_eq ?_
      have hpow : R ^ n = R ^ N * R ^ (n - N) := by rw [← pow_add, Nat.add_sub_of_le hn.le]
      rw [hpow]
      field_simp
      <;> ring

    have hlim : Tendsto (fun R : ℝ ↦ C / R ^ (n - N)) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop (Nat.sub_pos_of_lt hn).ne')
    have hn0 : ‖p n‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hb'
    apply FormalMultilinearSeries.coeff_eq_zero.mpr
    exact norm_eq_zero.mp (le_antisymm hn0 (norm_nonneg _))

  refine ⟨∑ n ∈ Finset.range (N + 1), Polynomial.monomial n (p.coeff n), ?_⟩
  intro z
  have hsum := hp.hasSum (y := z) (by simp)
  have hfinite : (∑' n, p n (fun _ ↦ z)) = ∑ n ∈ Finset.range (N + 1), p n (fun _ ↦ z) := by
    apply tsum_eq_sum
    intro n hn
    have hn' : N < n := by exact Nat.lt_of_succ_le (not_lt.mp (by simpa only [Finset.mem_range] using hn))
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, hz n hn', smul_zero]

  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_fin, smul_eq_mul, mul_comm, zero_add] using
    hsum.tsum_eq.symm.trans hfinite

theorem caf_polynomial_of_entire_inv (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hinf : MeromorphicAt (fun w : ℂ ↦ f w⁻¹) 0) :
    ∃ P : Polynomial ℂ, ∀ z, f z = P.eval z := by
  obtain ⟨N, hN⟩ := hinf
  let H : ℂ → ℂ := fun w ↦ (w - 0) ^ N • f w⁻¹
  have hbound : ∀ᶠ w in 𝓝 (0 : ℂ), ‖H w‖ < ‖H 0‖ + 1 :=
    (show ContinuousAt H 0 from hN.continuousAt).norm (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hbδ⟩ := Metric.eventually_nhds_iff.mp hbound
  apply caf_polynomial_of_sphere_growth f hf N (‖H 0‖ + 1)
  have hev : ∀ᶠ R : ℝ in atTop, R⁻¹ < δ :=
    tendsto_inv_atTop_zero (gt_mem_nhds hδ)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with R hR hRp z hz
  have hnz : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hnz ▸ hRp)
  have hbz := (hbδ (show dist z⁻¹ 0 < δ by simpa [dist_eq_norm, norm_inv, hnz] using hR)).le
  have hprod : R⁻¹ ^ N * ‖f z‖ ≤ ‖H 0‖ + 1 := by
    simpa only [H, norm_smul, sub_zero, norm_pow, norm_inv, hnz, inv_inv] using hbz
  have hp : 0 < R ^ N := pow_pos hRp N
  apply (div_le_iff₀ hp).mp
  simpa only [div_eq_inv_mul, inv_pow] using hprod

theorem caf_ratFunc_eval_div (P Q : Polynomial ℂ) (z : ℂ) (hQ : Q.eval z ≠ 0) :
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q).eval
      (RingHom.id ℂ) z = P.eval z / Q.eval z := by
  let r := algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q
  have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQ
  have hd : r.denom.eval z ≠ 0 := fun h ↦ hQ
    (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd P Q) h)
  have heq := (RatFunc.num_mul_eq_mul_denom_iff hQ0).mpr (show r = _ from rfl)
  have hev := congrArg (Polynomial.eval z) heq
  simp only [Polynomial.eval_mul] at hev
  change r.num.eval₂ (RingHom.id ℂ) z / r.denom.eval₂ (RingHom.id ℂ) z = _
  simp only [Polynomial.eval₂_id]
  exact (div_eq_div_iff hd hQ).mpr hev

theorem caf_meromorphic_polynomial_inv (P : Polynomial ℂ) :
    MeromorphicAt (fun w : ℂ ↦ P.eval w⁻¹) 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add, Pi.add_apply] using! hp.add hq
  | monomial n a => simpa only [Polynomial.eval_monomial, smul_eq_mul] using!
      (MeromorphicAt.const a (0 : ℂ)).mul ((MeromorphicAt.id 0).inv.pow n)

theorem caf_ratFunc_of_meromorphic_aux (f : ℂ → ℂ) (S : Finset ℂ)
    (hf : ∀ z ∉ S, AnalyticAt ℂ f z) (hS : ∀ z ∈ S, MeromorphicAt f z)
    (hinf : MeromorphicAt (fun w : ℂ ↦ f w⁻¹) 0) :
    ∃ r : RatFunc ℂ, ∀ z ∉ S, f z = r.eval (RingHom.id ℂ) z := by
  classical
  let N : ℂ → ℕ := fun z ↦ if hz : z ∈ S then (hS z hz).choose else 0
  let Q : Polynomial ℂ := ∏ s ∈ S, (Polynomial.X - Polynomial.C s) ^ N s
  let H : ℂ → ℂ := fun z ↦ Q.eval z * f z
  have hH (z : ℂ) : AnalyticAt ℂ H z := by
    by_cases hz : z ∈ S
    · have hN : AnalyticAt ℂ (fun w ↦ (w - z) ^ N z • f w) z := by
        simpa only [N, dite_eq_left hz] using (hS z hz).choose_spec
      have hprod : Q = (Polynomial.X - Polynomial.C z) ^ N z *
          ∏ s ∈ S.erase z, (Polynomial.X - Polynomial.C s) ^ N s := by
        exact (Finset.mul_prod_erase S _ hz).symm
      have ha := (AnalyticOnNhd.eval_polynomial
        (∏ s ∈ S.erase z, (Polynomial.X - Polynomial.C s) ^ N s) z (mem_univ _)).mul hN
      convert ha using 1
      ext w
      simp only [H, hprod, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul, Pi.mul_apply]
      ring
    · exact (AnalyticOnNhd.eval_polynomial Q z (mem_univ _)).mul (hf z hz)
  have hHi : MeromorphicAt (fun w : ℂ ↦ H w⁻¹) 0 :=
    (caf_meromorphic_polynomial_inv Q).mul hinf
  obtain ⟨P, hP⟩ := caf_polynomial_of_entire_inv H (fun z ↦ (hH z).differentiableAt) hHi
  refine ⟨algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q, ?_⟩
  intro z hz
  have hQz : Q.eval z ≠ 0 := by
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Finset.prod_ne_zero_iff]
    intro s hs
    exact pow_ne_zero _ (sub_ne_zero.mpr (by intro h; exact hz (h ▸ hs)))
  rw [caf_ratFunc_eval_div P Q z hQz, ← hP z]
  dsimp [H]
  field_simp

theorem caf_polynomial_eval_inv (p : Polynomial ℂ) (w : ℂ) (hw : w ≠ 0) :
    p.eval w⁻¹ = w ^ (-(p.natDegree : ℤ)) * p.reverse.eval w := by
  let : Invertible w⁻¹ := invertibleOfNonzero (inv_ne_zero hw)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) w⁻¹ p
  simpa [invOf_eq_inv, Polynomial.eval₂_at_apply, zpow_neg, zpow_natCast, mul_comm] using h.symm

theorem caf_meromorphicOrderAt_inv_aux (r : RatFunc ℂ) (hr : r ≠ 0) :
    MeromorphicAt (fun w : ℂ ↦ r.eval (RingHom.id ℂ) w⁻¹) 0 ∧
      meromorphicOrderAt (fun w : ℂ ↦ r.eval (RingHom.id ℂ) w⁻¹) 0 =
        ((-r.intDegree : ℤ) : WithTop ℤ) := by
  let g : ℂ → ℂ := fun w ↦ r.num.reverse.eval w / r.denom.reverse.eval w
  have hn : r.num.reverse.eval (0 : ℂ) ≠ 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse] using Polynomial.leadingCoeff_ne_zero.mpr (r.num_ne_zero hr)
  have hd : r.denom.reverse.eval (0 : ℂ) ≠ 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse] using Polynomial.leadingCoeff_ne_zero.mpr r.denom_ne_zero
  have hg : AnalyticAt ℂ g 0 := by
    exact (AnalyticOnNhd.eval_polynomial r.num.reverse 0 (mem_univ _)).div
      (AnalyticOnNhd.eval_polynomial r.denom.reverse 0 (mem_univ _)) hd
  have heq : (fun w : ℂ ↦ r.eval (RingHom.id ℂ) w⁻¹) =ᶠ[𝓝[≠] 0]
      fun w ↦ (w - 0) ^ (-r.intDegree) • g w := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w ≠ 0 := hw
    simp only [RatFunc.eval, Polynomial.eval₂_id, caf_polynomial_eval_inv _ w hw',
      RatFunc.intDegree, neg_sub, sub_zero, smul_eq_mul, g]
    rw [zpow_sub₀ hw']
    simp only [zpow_natCast, zpow_neg]
    field_simp
  have hm : MeromorphicAt (fun w : ℂ ↦ r.eval (RingHom.id ℂ) w⁻¹) 0 :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨_, g, hg, heq⟩
  refine ⟨hm, (meromorphicOrderAt_eq_int_iff hm).mpr ⟨g, hg, div_ne_zero hn hd, heq⟩⟩

end HodgeLean.Foundations.Program
