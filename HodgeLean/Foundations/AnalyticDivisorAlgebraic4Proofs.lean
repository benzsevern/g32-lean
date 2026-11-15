import HodgeLean.Foundations.AnalyticDivisorAlgebraic3
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import HodgeLean.Foundations.AnalyticDivisorAlgebraic4Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.Polynomial.Vieta

/-! # Proof obligations for the analytic divisor spec, fourth stage

One obligation per statement of `HodgeLean.Foundations.AnalyticDivisorAlgebraic4`. All seventeen
are open.
-/

noncomputable section

open Set Filter Topology Metric Complex

open scoped Real

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic4

section ArgumentPrinciple

private lemma frequently_mem_ball_nhdsNE {c x : ℂ} {r : ℝ} (hr : 0 < r) (hx : x ∈ closedBall c r) :
    ∃ᶠ y in 𝓝[≠] x, y ∈ ball c r := by
  by_cases hxb : x ∈ ball c r
  · exact Filter.Eventually.frequently (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hxb))
  · rw [← mem_closure_ne_iff_frequently_within, sdiff_singleton_eq_self hxb, closure_ball c hr.ne']
    exact hx

private lemma exists_factor_closedBall {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hne : ∀ w ∈ sphere c r, g w ≠ 0) :
    ∃ S : Finset ℂ, ∃ k : ℂ → ℂ, (↑S ⊆ ball c r) ∧
      (∀ a ∈ ball c r, analyticOrderNatAt g a ≠ 0 → a ∈ S) ∧
      AnalyticOnNhd ℂ k (closedBall c r) ∧ (∀ x ∈ closedBall c r, k x ≠ 0) ∧
      ∀ x ∈ closedBall c r,
        g =ᶠ[𝓝 x] fun w => (∏ u ∈ S, (w - u) ^ analyticOrderNatAt g u) * k w := by
  classical
  set U := closedBall c r with hU
  have hmero : MeromorphicOn g U := fun x hx => (hg x hx).meromorphicAt
  have hx₀ : c + (r : ℂ) ∈ sphere c r := by
    simp [abs_of_pos hr]
  have hfin : ∀ x ∈ U, analyticOrderAt g x ≠ ⊤ := fun x hx =>
    hg.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c r).isPreconnected
      (sphere_subset_closedBall hx₀) hx
      (by rw [(hg _ (sphere_subset_closedBall hx₀)).analyticOrderAt_eq_zero.2 (hne _ hx₀)]; simp)
  have hmord : ∀ u : U, meromorphicOrderAt g u ≠ ⊤ := by
    intro u
    rw [(hg u u.2).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt (hfin u u.2)]
    simp
  have hD : ∀ u ∈ U, MeromorphicOn.divisor g U u = analyticOrderNatAt g u := by
    intro u hu
    rw [MeromorphicOn.divisor_apply hmero hu, (hg u hu).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (hfin u hu)]
    simp
  have hord0 : ∀ u ∈ U, analyticOrderNatAt g u ≠ 0 → u ∈ ball c r := by
    intro u hu h0
    have hgu : g u = 0 := by
      by_contra hgu
      apply h0
      simp [analyticOrderNatAt, (hg u hu).analyticOrderAt_eq_zero.2 hgu]
    rw [mem_ball]
    refine lt_of_le_of_ne (mem_closedBall.1 hu) fun h => hne u ?_ hgu
    exact mem_sphere.2 h
  have hsupp : (MeromorphicOn.divisor g U).support.Finite :=
    (MeromorphicOn.divisor g U).finiteSupport (isCompact_closedBall c r)
  set S := hsupp.toFinset with hS
  have hSU : ∀ u, u ∈ S ↔ u ∈ U ∧ analyticOrderNatAt g u ≠ 0 := by
    intro u
    rw [hS, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · intro h
      have huU : u ∈ U := by
        by_contra hu
        exact h ((MeromorphicOn.divisor g U).apply_eq_zero_of_notMem hu)
      refine ⟨huU, fun h0 => h ?_⟩
      rw [hD u huU, h0]; rfl
    · rintro ⟨huU, h0⟩
      rw [hD u huU]
      exact_mod_cast h0
  obtain ⟨k, hk, hkne, heq⟩ := hmero.extract_zeros_poles hmord hsupp
  refine ⟨S, k, fun u hu => hord0 u ((hSU u).1 hu).1 ((hSU u).1 hu).2,
    fun a ha h0 => (hSU a).2 ⟨ball_subset_closedBall ha, h0⟩,
    hk, fun x hx => hkne ⟨x, hx⟩, ?_⟩
  set Q : ℂ → ℂ := fun w => (∏ u ∈ S, (w - u) ^ analyticOrderNatAt g u) * k w with hQ
  have hfp : (∏ᶠ u, (· - u) ^ MeromorphicOn.divisor g U u) • k = Q := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · ext w
      simp only [Pi.smul_apply', Finset.prod_apply, smul_eq_mul, hQ]
      congr 1
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [hD u ((hSU u).1 hu).1, zpow_natCast, Pi.pow_apply]
    · intro u hu
      by_contra huS
      apply hu
      have : MeromorphicOn.divisor g U u = 0 := by
        by_contra h
        exact huS (by rw [hS, Finset.mem_coe, Set.Finite.mem_toFinset]; exact h)
      simp only [this, zpow_zero]
  rw [hfp] at heq
  intro x hx
  have hQan : AnalyticAt ℂ Q x := by
    refine AnalyticAt.mul ?_ (hk x hx)
    exact (Differentiable.analyticAt (by fun_prop) x)
  rcases (hg x hx).eventually_eq_or_eventually_ne hQan with h | h
  · exact h
  · exfalso
    have hdisj := (mem_codiscreteWithin.1 heq) x hx
    rw [Filter.disjoint_principal_right] at hdisj
    obtain ⟨y, hyb, hyne, hy⟩ :=
      ((frequently_mem_ball_nhdsNE hr hx).and_eventually (h.and hdisj)).exists
    exact hy ⟨ball_subset_closedBall hyb, hyne⟩

theorem spec_circleIntegral_mul_logDeriv_aux {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hh : AnalyticOnNhd ℂ h (closedBall c r))
    (hne : ∀ w ∈ sphere c r, g w ≠ 0) :
    (∮ w in C(c, r), h w * deriv g w / g w) =
      2 * π * I * ∑ᶠ (a : ℂ) (_ : a ∈ ball c r), (analyticOrderNatAt g a : ℂ) * h a := by
  classical
  obtain ⟨S, k, hSb, hSord, hk, hkne, heq⟩ := exists_factor_closedBall hr hg hne
  set m : ℂ → ℕ := fun u => analyticOrderNatAt g u with hm
  have hsph : ∀ w ∈ sphere c r, w ∉ ball c r := fun w hw hwb => by
    rw [mem_sphere] at hw; rw [mem_ball] at hwb; linarith
  -- the integrand on the circle
  have hkey : EqOn (fun w => h w * deriv g w / g w)
      (fun w => (∑ u ∈ S, (w - u)⁻¹ • ((m u : ℂ) * h w)) + h w * deriv k w / k w)
      (sphere c r) := by
    intro w hw
    have hwS : ∀ u ∈ S, w - u ≠ 0 := fun u hu h0 =>
      hsph w hw (by rw [sub_eq_zero] at h0; rw [h0]; exact hSb hu)
    have hwc := sphere_subset_closedBall hw
    let F : ℂ → ℂ → ℂ := fun u w => (w - u) ^ m u
    have hPk : (fun w => (∏ u ∈ S, (w - u) ^ analyticOrderNatAt g u) * k w) =
        (∏ u ∈ S, F u) * k := by
      ext w; simp [F, m, Finset.prod_apply]
    have hPne : ∀ u ∈ S, F u w ≠ 0 := fun u hu => pow_ne_zero _ (hwS u hu)
    have hFd : ∀ u ∈ S, DifferentiableAt ℂ (F u) w := fun u _ => by fun_prop
    have hlog : logDeriv g w = logDeriv (∏ u ∈ S, F u) w + logDeriv k w := by
      have : logDeriv g w = logDeriv ((∏ u ∈ S, F u) * k) w := by
        rw [logDeriv_apply, logDeriv_apply, (heq w hwc).deriv_eq, (heq w hwc).eq_of_nhds, hPk]
        congr 1
        exact congrFun hPk w
      rw [this]
      refine logDeriv_mul (f := ∏ u ∈ S, F u) (g := k) w ?_ (hkne w hwc) ?_
        ((hk w hwc).differentiableAt)
      · rw [Finset.prod_apply]; exact Finset.prod_ne_zero_iff.2 hPne
      · have : (∏ u ∈ S, F u) = fun w => ∏ u ∈ S, F u w := by ext; simp [Finset.prod_apply]
        rw [this]; fun_prop
    rw [logDeriv_prod hPne hFd] at hlog
    have hF : ∀ u ∈ S, logDeriv (F u) w = (m u : ℂ) * (w - u)⁻¹ := by
      intro u _
      rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply, deriv_sub_const, deriv_id'']
      simp [div_eq_mul_inv]
    rw [Finset.sum_congr rfl hF] at hlog
    simp only
    rw [mul_div_assoc, ← logDeriv_apply, hlog, mul_add, Finset.mul_sum, logDeriv_apply,
      mul_div_assoc]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]; ring
  have hcontS : ∀ u ∈ S, CircleIntegrable (fun w => (w - u)⁻¹ • ((m u : ℂ) * h w)) c r := by
    intro u hu
    refine ContinuousOn.circleIntegrable hr.le fun w hw => ?_
    have hwu : w - u ≠ 0 := fun h0 =>
      hsph w hw (by rw [sub_eq_zero] at h0; rw [h0]; exact hSb hu)
    have := (hh w (sphere_subset_closedBall hw)).continuousAt
    exact (((continuousAt_id.sub continuousAt_const).inv₀ hwu).smul
      (continuousAt_const.mul this)).continuousWithinAt
  have hkan : ∀ x ∈ closedBall c r, AnalyticAt ℂ (fun w => h w * deriv k w / k w) x :=
    fun x hx => ((hh x hx).mul (hk.deriv x hx)).div (hk x hx) (hkne x hx)
  have hlast : (∮ w in C(c, r), h w * deriv k w / k w) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      (fun x hx => (hkan x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hkan x (ball_subset_closedBall hx.1)).differentiableAt)
  have hsumI : CircleIntegrable (fun w => ∑ u ∈ S, (w - u)⁻¹ • ((m u : ℂ) * h w)) c r := by
    have := CircleIntegrable.sum S hcontS
    convert this using 1
    ext w; simp [Finset.sum_apply]
  rw [circleIntegral.integral_congr hr.le hkey, circleIntegral.integral_add hsumI
      (ContinuousOn.circleIntegrable hr.le fun x hx =>
        (hkan x (sphere_subset_closedBall hx)).continuousAt.continuousWithinAt),
    hlast, add_zero, circleIntegral.integral_fun_sum hcontS]
  have hdisc : ∀ u ∈ S, (∮ w in C(c, r), (w - u)⁻¹ • ((m u : ℂ) * h w)) =
      (2 * π * I) • ((m u : ℂ) * h u) := fun u hu =>
    DifferentiableOn.circleIntegral_sub_inv_smul
      ((differentiableOn_const _).mul hh.differentiableOn) (hSb hu)
  rw [Finset.sum_congr rfl hdisc, ← Finset.smul_sum, smul_eq_mul]
  congr 1
  rw [finsum_mem_inter_support_eq _ (ball c r) (S : Set ℂ), finsum_mem_coe_finset]
  ext a
  simp only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe]
  constructor
  · rintro ⟨ha, h0⟩
    refine ⟨hSord a ha fun hz => h0 ?_, h0⟩
    simp [hz]
  · rintro ⟨ha, h0⟩
    exact ⟨hSb ha, h0⟩

private lemma natCast_finsum_mem_complex (f : ℂ → ℕ) (s : Set ℂ) :
    ((∑ᶠ (a : ℂ) (_ : a ∈ s), f a : ℕ) : ℂ) = ∑ᶠ (a : ℂ) (_ : a ∈ s), (f a : ℂ) := by
  have hsupp : Function.support (fun a => (f a : ℂ)) = Function.support f := by
    ext a; simp
  by_cases hfin : (s ∩ Function.support f).Finite
  · rw [← finsum_mem_inter_support f s, Nat.cast_finsum_mem hfin,
      ← finsum_mem_inter_support (fun a => (f a : ℂ)) s, hsupp]
  · rw [finsum_mem_eq_zero_of_infinite hfin,
      finsum_mem_eq_zero_of_infinite (by rwa [hsupp]), Nat.cast_zero]

theorem spec_circleIntegral_logDeriv_eq_zeroCount_aux {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hne : ∀ w ∈ sphere c r, g w ≠ 0) :
    (∮ w in C(c, r), deriv g w / g w) = 2 * π * I * (zeroCount g c r : ℂ) := by
  have := spec_circleIntegral_mul_logDeriv_aux hr hg (analyticOnNhd_const (v := (1 : ℂ))) hne
  simp only [one_mul, mul_one] at this
  rw [this, zeroCount, natCast_finsum_mem_complex]

theorem spec_circleIntegral_logDeriv_ne_of_zero_on_sphere_aux :
    (∮ w in C(0, 1), deriv (fun w : ℂ => w * (w - 1)) w / (w * (w - 1))) ≠
      2 * π * I * (zeroCount (fun w : ℂ => w * (w - 1)) 0 1 : ℂ) := by
  have hd : ∀ w : ℂ, deriv (fun w : ℂ => w * (w - 1)) w = 2 * w - 1 := by
    intro w
    have : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (w - 1) + w * 1) w :=
      (hasDerivAt_id' w).mul ((hasDerivAt_id' w).sub_const 1)
    rw [this.deriv]; ring
  have hcount : zeroCount (fun w : ℂ => w * (w - 1)) 0 1 = 1 := by
    have han : AnalyticAt ℂ (fun w : ℂ => w * (w - 1)) 0 :=
      (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
    have h0 : analyticOrderNatAt (fun w : ℂ => w * (w - 1)) 0 = 1 := by
      have : analyticOrderAt (fun w : ℂ => w * (w - 1)) 0 = (1 : ℕ) := by
        rw [han.analyticOrderAt_eq_natCast]
        exact ⟨fun w => w - 1, analyticAt_id.sub analyticAt_const, by norm_num,
          Eventually.of_forall fun w => by simp [smul_eq_mul]⟩
      simp [analyticOrderNatAt, this]
    classical
    unfold zeroCount
    rw [finsum_eq_single _ (0 : ℂ)]
    · rw [finsum_eq_if]; simp [h0]
    · intro x hx
      rw [finsum_eq_if]
      split_ifs with hxb
      · have hx1 : x - 1 ≠ 0 := by
          intro h
          have : x = 1 := by linear_combination h
          simp [this] at hxb
        have hax : AnalyticAt ℂ (fun w : ℂ => w * (w - 1)) x :=
          (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
        have : analyticOrderAt (fun w : ℂ => w * (w - 1)) x = 0 :=
          hax.analyticOrderAt_eq_zero.2 (mul_ne_zero hx hx1)
        simp [analyticOrderNatAt, this]
      · rfl
  have hnot : ¬ CircleIntegrable (fun w => deriv (fun w : ℂ => w * (w - 1)) w / (w * (w - 1))) 0 1 := by
    intro hF
    have hinv : CircleIntegrable (fun w : ℂ => (w - 0)⁻¹) 0 1 := by
      rw [circleIntegrable_sub_inv_iff]; right; simp
    have h1 : CircleIntegrable (fun w : ℂ => (w - 1)⁻¹) 0 1 := by
      have := hF.sub hinv
      unfold CircleIntegrable at this ⊢
      refine (intervalIntegrable_congr_uIoo fun θ hθ => ?_).1 this
      rw [uIoo_of_le (by positivity)] at hθ
      have hne : ∀ k : ℂ, k = 0 ∨ k = 1 → circleMap 0 1 θ ≠ k := by
        rintro k hk h
        rcases hk with rfl | rfl
        · exact circleMap_ne_center one_ne_zero h
        · rw [circleMap_zero, Complex.ofReal_one, one_mul, Complex.exp_eq_one_iff] at h
          obtain ⟨n, hn⟩ := h
          have hθn : (θ : ℂ) = (2 * π * n : ℝ) := by
            have := congrArg (· * (-I)) hn
            push_cast
            linear_combination this + ((θ : ℂ) - 2 * π * n) * I_sq
          have hθ' : θ = 2 * π * n := by exact_mod_cast hθn
          rcases hθ with ⟨h0, h2⟩
          rw [hθ'] at h0 h2
          have hpi := Real.pi_pos
          have hn0 : (0 : ℝ) < n := by nlinarith
          have hn1 : (n : ℝ) < 1 := by nlinarith
          have : (0 : ℤ) < n := by exact_mod_cast hn0
          have : n < (1 : ℤ) := by exact_mod_cast hn1
          omega
      have h0 := hne 0 (Or.inl rfl)
      have h1 := hne 1 (Or.inr rfl)
      set w := circleMap 0 1 θ
      have h1' : w - 1 ≠ 0 := sub_ne_zero.2 h1
      simp only [Pi.sub_apply, hd, sub_zero]
      field_simp
      ring
    rw [circleIntegrable_sub_inv_iff] at h1
    simp at h1
  rw [circleIntegral.integral_undef hnot, hcount]
  simp [Real.pi_ne_zero, I_ne_zero]

theorem spec_analyticOrderAt_polynomial_eval_aux {p : Polynomial ℂ} (hp : p ≠ 0) (α : ℂ) :
    analyticOrderAt (fun w => p.eval w) α = p.rootMultiplicity α := by
  obtain ⟨q, hpq, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp α
  have han : ∀ r : Polynomial ℂ, AnalyticAt ℂ (fun w => r.eval w) α := fun r =>
    (Polynomial.differentiable r).analyticAt α
  rw [(han p).analyticOrderAt_eq_natCast]
  refine ⟨fun w => q.eval w, han q, ?_, Eventually.of_forall fun w => ?_⟩
  · rwa [Polynomial.dvd_iff_isRoot] at hndvd
  · conv_lhs => rw [hpq]
    simp [smul_eq_mul]

end ArgumentPrinciple

section Count

variable {n : ℕ}

theorem spec_exists_weierstrass_radii_aux {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ} {w₀ : ℂ}
    {d : ℕ} (hf : AnalyticAt ℂ f (z₀, w₀)) (hd : analyticOrderAt (fun w => f (z₀, w)) w₀ = d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ ∃ δ, 0 < δ ∧
      AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall w₀ r) ∧
      (∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere w₀ r, f (z, w) ≠ 0) ∧
      ∀ w ∈ closedBall w₀ r, f (z₀, w) = 0 → w = w₀ := by
  obtain ⟨ρ, hρ, hfρ⟩ := hf.exists_ball_analyticOnNhd
  have hg : AnalyticAt ℂ (fun w => f (z₀, w)) w₀ :=
    hf.comp₂ analyticAt_const analyticAt_id
  have hnt : ¬ ∀ᶠ w in 𝓝 w₀, f (z₀, w) = 0 := by
    rw [← analyticOrderAt_eq_top, hd]; exact ENat.natCast_ne_top d
  obtain ⟨ρ', hρ', hρ'g⟩ : ∃ ρ', 0 < ρ' ∧ ∀ w ∈ ball w₀ ρ', w ≠ w₀ → f (z₀, w) ≠ 0 := by
    have h := (hg.eventually_eq_zero_or_eventually_ne_zero).resolve_left hnt
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h
    obtain ⟨ρ', hρ', h⟩ := h
    exact ⟨ρ', hρ', fun w hw hne => h w hw hne⟩
  set r := min (ε / 2) (min (ρ' / 2) (ρ / 2)) with hr_def
  have hr : 0 < r := by positivity
  have hrε : r < ε := by
    have := min_le_left (ε / 2) (min (ρ' / 2) (ρ / 2)); linarith
  have hrρ' : r < ρ' := by
    have := (min_le_right (ε / 2) (min (ρ' / 2) (ρ / 2))).trans (min_le_left _ _); linarith
  have hrρ : r < ρ := by
    have := (min_le_right (ε / 2) (min (ρ' / 2) (ρ / 2))).trans (min_le_right _ _); linarith
  have hsph : ∀ w ∈ sphere w₀ r, f (z₀, w) ≠ 0 := by
    intro w hw
    have hw' : dist w w₀ = r := hw
    refine hρ'g w (by rw [mem_ball]; linarith) ?_
    rintro rfl; simp at hw'; linarith
  set O := ball (z₀, w₀) ρ ∩ f ⁻¹' {0}ᶜ
  have hO : IsOpen O :=
    hfρ.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hKO : ({z₀} ×ˢ sphere w₀ r : Set ((Fin n → ℂ) × ℂ)) ⊆ O := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    rw [mem_singleton_iff] at hz; subst hz
    refine ⟨?_, hsph w hw⟩
    rw [mem_ball, Prod.dist_eq, dist_self]
    have hw' : dist w w₀ = r := hw
    rw [hw', max_eq_right hr.le]; exact hrρ
  obtain ⟨δ', hδ', hδ'O⟩ :=
    (isCompact_singleton.prod (isCompact_sphere w₀ r)).exists_cthickening_subset_open hO hKO
  set δ := min δ' (ρ / 2)
  have hδ : 0 < δ := by positivity
  refine ⟨r, hr, hrε, δ, hδ, ?_, ?_, ?_⟩
  · rintro ⟨z, w⟩ ⟨hz, hw⟩
    apply hfρ
    rw [mem_ball, Prod.dist_eq]
    have h1 : dist z z₀ ≤ δ := hz
    have h2 : dist w w₀ ≤ r := hw
    have : δ ≤ ρ / 2 := min_le_right _ _
    exact max_lt (by linarith) (by linarith)
  · intro z hz w hw
    have hmem : (z, w) ∈ cthickening δ' ({z₀} ×ˢ sphere w₀ r) := by
      refine mem_cthickening_of_dist_le (z, w) (z₀, w) δ' _ ⟨rfl, hw⟩ ?_
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact (show dist z z₀ ≤ δ from hz).trans (min_le_left _ _)
    exact (hδ'O hmem).2
  · intro w hw h0
    by_contra hne
    exact hρ'g w (by rw [mem_ball]; exact lt_of_le_of_lt hw hrρ') hne h0

theorem gaga4b_continuousOn_circleIntegral_param {X : Type*} [TopologicalSpace X]
    {F : X × ℂ → ℂ} {s : Set X} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hF : ContinuousOn F (s ×ˢ sphere c r)) :
    ContinuousOn (fun x => ∮ w in C(c, r), F (x, w)) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  unfold circleIntegral
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : s) θ => deriv (circleMap c r) θ • F ((x : X), circleMap c r θ)) ?_ _ _
  simp only [deriv_circleMap]
  refine Continuous.smul (((continuous_circleMap 0 r).comp continuous_snd).mul continuous_const) ?_
  refine hF.comp_continuous (by fun_prop) fun p => ⟨p.1.2, circleMap_mem_sphere c hr p.2⟩

theorem gaga4b_deriv_slice_eq {f : (Fin n → ℂ) × ℂ → ℂ} {q : (Fin n → ℂ) × ℂ}
    (hf : DifferentiableAt ℂ f q) :
    deriv (fun w => f (q.1, w)) q.2 = fderiv ℂ f q (0, 1) := by
  have h1 : HasDerivAt (fun w : ℂ => (q.1, w)) ((0 : Fin n → ℂ), (1 : ℂ)) q.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  exact (hf.hasFDerivAt.comp_hasDerivAt (x := q.2) h1).deriv

theorem gaga4b_zeroCount_of_nonpos {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : r ≤ 0) :
    zeroCount g c r = 0 := by
  simp [zeroCount, ball_eq_empty.2 hr]

theorem spec_zeroCount_eq_of_sphere_ne_zero_aux {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ}
    {δ : ℝ} {c : ℂ} {r : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, f (z, w) ≠ 0) {z : Fin n → ℂ}
    (hz : z ∈ ball z₀ δ) :
    zeroCount (fun w => f (z, w)) c r = zeroCount (fun w => f (z₀, w)) c r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [gaga4b_zeroCount_of_nonpos hr, gaga4b_zeroCount_of_nonpos hr]
  have hδ : 0 < δ := dist_nonneg.trans_lt hz
  set H : (Fin n → ℂ) × ℂ → ℂ := fun q => fderiv ℂ f q (0, 1) / f q
  have hslice : ∀ z' ∈ closedBall z₀ δ, AnalyticOnNhd ℂ (fun w => f (z', w)) (closedBall c r) :=
    fun z' hz' w hw => (hf (z', w) ⟨hz', hw⟩).comp₂ analyticAt_const analyticAt_id
  have hcount : ∀ z' ∈ closedBall z₀ δ,
      (∮ w in C(c, r), H (z', w)) = 2 * π * I * (zeroCount (fun w => f (z', w)) c r : ℂ) := by
    intro z' hz'
    rw [← spec_circleIntegral_logDeriv_eq_zeroCount_aux hr (hslice z' hz') (hne z' hz')]
    refine circleIntegral.integral_congr hr.le fun w hw => ?_
    simp only [H]
    rw [gaga4b_deriv_slice_eq (q := (z', w))
      ((hf (z', w) ⟨hz', sphere_subset_closedBall hw⟩).differentiableAt)]
  have hHc : ContinuousOn H (closedBall z₀ δ ×ˢ sphere c r) := by
    rintro ⟨z', w⟩ ⟨hz', hw⟩
    have ha := hf (z', w) ⟨hz', sphere_subset_closedBall hw⟩
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div ?_ ha.continuousAt (hne z' hz' w hw)
    exact (ha.fderiv.continuousAt).clm_apply continuousAt_const
  have hG := gaga4b_continuousOn_circleIntegral_param hr.le hHc
  set N : (Fin n → ℂ) → ℕ := fun z' => zeroCount (fun w => f (z', w)) c r
  have hNc : ContinuousOn N (ball z₀ δ) := by
    rw [Nat.isClosedEmbedding_coe_real.isInducing.continuousOn_iff]
    have h2 : ContinuousOn (fun z' => ((∮ w in C(c, r), H (z', w)) / (2 * π * I)).re)
        (ball z₀ δ) :=
      Complex.continuous_re.comp_continuousOn
        ((hG.mono ball_subset_closedBall).div_const _)
    refine h2.congr fun z' hz' => ?_
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    simp only [Function.comp, hcount z' (ball_subset_closedBall hz'), mul_div_cancel_left₀ _ hpi,
      Complex.natCast_re, N]
  exact (convex_ball z₀ δ).isPreconnected.constant hNc hz (mem_ball_self hδ)

theorem spec_exists_zeroCount_eq_order_aux {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ}
    {w₀ : ℂ} {d : ℕ} (hf : AnalyticAt ℂ f (z₀, w₀))
    (hd : analyticOrderAt (fun w => f (z₀, w)) w₀ = d) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ ∃ δ, 0 < δ ∧
      AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall w₀ r) ∧
      (∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere w₀ r, f (z, w) ≠ 0) ∧
      ∀ z ∈ ball z₀ δ, zeroCount (fun w => f (z, w)) w₀ r = d := by
  obtain ⟨r, hr, hrε, δ, hδ, han, hsph, huniq⟩ := spec_exists_weierstrass_radii_aux hf hd hε
  refine ⟨r, hr, hrε, δ, hδ, han, hsph, fun z hz => ?_⟩
  classical
  rw [spec_zeroCount_eq_of_sphere_ne_zero_aux han hsph hz, zeroCount,
    finsum_eq_single _ w₀]
  · simp [finsum_eq_if, mem_ball_self hr, analyticOrderNatAt, hd]
  · intro w hne
    rw [finsum_eq_if]
    split_ifs with hw
    · have h0 : f (z₀, w) ≠ 0 := fun h => hne (huniq w (ball_subset_closedBall hw) h)
      have : analyticOrderAt (fun w => f (z₀, w)) w = 0 := analyticOrderAt_eq_zero.2 (Or.inr h0)
      simp [analyticOrderNatAt, this]
    · rfl

end Count

section Coefficients

variable {n : ℕ}

theorem spec_analyticOnNhd_circleIntegral_aux {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {F : V × ℂ → ℂ} {U : Set V} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere c r)) :
    AnalyticOnNhd ℂ (fun z => ∮ w in C(c, r), F (z, w)) U := by
  intro z hz
  set O : Set (V × ℂ) := {p | AnalyticAt ℂ F p}
  have hO : IsOpen O := isOpen_analyticAt ℂ F
  have hKO : ({z} ×ˢ sphere c r : Set (V × ℂ)) ⊆ O := by
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    rw [mem_singleton_iff] at hx; subst hx
    exact hF _ ⟨hz, hw⟩
  obtain ⟨η, hη, hηO⟩ :=
    (isCompact_singleton.prod (isCompact_sphere c r)).exists_cthickening_subset_open hO hKO
  set K : Set (V × ℂ) := closedBall z η ×ˢ sphere c r
  have hKc : IsCompact K := (isCompact_closedBall z η).prod (isCompact_sphere c r)
  have hK : K ⊆ O := by
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    refine hηO (mem_cthickening_of_dist_le (x, w) (z, w) η _ ⟨rfl, hw⟩ ?_)
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hx
  have hFc : ContinuousOn F K := fun p hp => (hK hp).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn (fderiv ℂ F) K :=
    fun p hp => (hK hp).fderiv.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hF'c
  set ε := η / 2
  have hε : 0 < ε := half_pos hη
  have hsub : ∀ x₁ ∈ ball z ε, ∀ x ∈ ball x₁ ε, x ∈ closedBall z η := by
    intro x₁ hx₁ x hx
    rw [mem_ball] at hx₁ hx; rw [mem_closedBall]
    have : ε = η / 2 := rfl
    linarith [dist_triangle x x₁ z]
  have hmemK : ∀ x ∈ closedBall z η, ∀ θ : ℝ, (x, circleMap c r θ) ∈ K :=
    fun x hx θ => ⟨hx, circleMap_mem_sphere c hr.le θ⟩
  have hcont : ∀ x ∈ closedBall z η,
      Continuous fun θ : ℝ => deriv (circleMap c r) θ • F (x, circleMap c r θ) := by
    intro x hx
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 r).mul continuous_const).smul
      (hFc.comp_continuous (by fun_prop) (hmemK x hx))
  have hdiff : DifferentiableOn ℂ (fun x => ∮ w in C(c, r), F (x, w)) (ball z ε) := by
    intro x₁ hx₁
    refine HasFDerivAt.differentiableAt (f' := ∫ θ in (0 : ℝ)..2 * π,
      deriv (circleMap c r) θ • (fderiv ℂ F (x₁, circleMap c r θ)).comp
        (ContinuousLinearMap.inl ℂ V ℂ)) ?_ |>.differentiableWithinAt
    show HasFDerivAt (fun x => ∫ θ in (0 : ℝ)..2 * π,
      deriv (circleMap c r) θ • F (x, circleMap c r θ)) _ x₁
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (E := ℂ) (H := V) (μ := MeasureTheory.volume)
      (F := fun x θ => deriv (circleMap c r) θ • F (x, circleMap c r θ))
      (F' := fun x θ => deriv (circleMap c r) θ • (fderiv ℂ F (x, circleMap c r θ)).comp
        (ContinuousLinearMap.inl ℂ V ℂ))
      (bound := fun _ => r * (C * ‖ContinuousLinearMap.inl ℂ V ℂ‖)) (ball_mem_nhds x₁ hε)
      ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [ball_mem_nhds x₁ hε] with x hx
      exact (hcont x (hsub x₁ hx₁ x hx)).aestronglyMeasurable
    · exact (hcont x₁ (hsub x₁ hx₁ x₁ (mem_ball_self hε))).intervalIntegrable _ _
    · have hx₁K := hsub x₁ hx₁ x₁ (mem_ball_self hε)
      simp only [deriv_circleMap]
      refine Continuous.aestronglyMeasurable ?_
      refine ((continuous_circleMap 0 r).mul continuous_const).smul ?_
      exact (ContinuousLinearMap.compL ℂ V (V × ℂ) ℂ).flip (ContinuousLinearMap.inl ℂ V ℂ)
        |>.continuous.comp (hF'c.comp_continuous (by fun_prop) (hmemK x₁ hx₁K))
    · refine Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one,
        abs_of_pos hr]
      refine mul_le_mul_of_nonneg_left ?_ hr.le
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hC _ (hmemK x (hsub x₁ hx₁ x hx) θ)) (norm_nonneg _)
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ x hx => ?_
      have hd := (hK (hmemK x (hsub x₁ hx₁ x hx) θ)).differentiableAt.hasFDerivAt
      exact (hd.comp x (hasFDerivAt_prodMk_left (𝕜 := ℂ) x (circleMap c r θ))).const_smul (deriv (circleMap c r) θ)
  exact AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn isOpen_ball hdiff z
    (mem_ball_self hε)

open Finset in
private theorem gaga4b_multiset_mul_esymm_eq_sum (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  classical
  set f : Fin (Multiset.card s) → ℂ := fun i => s.toList.get ⟨i, by simp⟩ with hf
  have hs : (univ.val.map f) = s := by
    rw [Fin.univ_val_map]
    conv_rhs => rw [← Multiset.coe_toList s]
    congr 1
    apply List.ext_get <;> simp [hf]
  have h := congrArg (MvPolynomial.aeval (R := ℂ) f)
    (MvPolynomial.mul_esymm_eq_sum (Fin (Multiset.card s)) ℂ k)
  simp only [map_mul, map_pow, map_neg, map_one, map_sum, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X, hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  conv_rhs => rw [← hs]
  simp [Function.comp_def, Finset.sum_eq_multiset_sum]

theorem spec_analyticOnNhd_coeff_of_powerSum_aux {S : (Fin n → ℂ) → Multiset ℂ}
    {U : Set (Fin n → ℂ)} {d : ℕ} (hU : IsOpen U) (hcard : ∀ z ∈ U, Multiset.card (S z) = d)
    (hpow : ∀ k, 1 ≤ k → k ≤ d → AnalyticOnNhd ℂ (fun z => ((S z).map (· ^ k)).sum) U)
    (j : ℕ) :
    AnalyticOnNhd ℂ
      (fun z => ((S z).map (fun α => Polynomial.X - Polynomial.C α)).prod.coeff j) U := by
  classical
  have he : ∀ k, k ≤ d → AnalyticOnNhd ℂ (fun z => (S z).esymm k) U := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa using (analyticOnNhd_const (v := (1 : ℂ)) (s := U))
      have hG : AnalyticOnNhd ℂ (fun z => (k : ℂ)⁻¹ * ((-1) ^ (k + 1) *
          ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
            (-1) ^ a.1 * (S z).esymm a.1 * ((S z).map (· ^ a.2)).sum)) U := by
        refine analyticOnNhd_const.mul (analyticOnNhd_const.mul ?_)
        refine Finset.analyticOnNhd_fun_sum _ fun a ha => ?_
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        refine (analyticOnNhd_const.mul (ih a.1 ha.2 (by omega))).mul (hpow a.2 (by omega) (by omega))
      refine hG.congr hU fun z _ => ?_
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
      rw [← gaga4b_multiset_mul_esymm_eq_sum, inv_mul_cancel_left₀ hk']
  by_cases hj : j ≤ d
  · have hG : AnalyticOnNhd ℂ (fun z => (-1 : ℂ) ^ (d - j) * (S z).esymm (d - j)) U :=
      analyticOnNhd_const.mul (he _ (by omega))
    refine hG.congr hU fun z hz => ?_
    rw [Multiset.prod_X_sub_C_coeff _ (by rw [hcard z hz]; exact hj), hcard z hz]
  · refine (analyticOnNhd_const (v := (0 : ℂ))).congr hU fun z hz => ?_
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard z hz]
    omega

private theorem c_finite_support_analyticOrderNatAt {g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) :
    (ball c r ∩ Function.support (analyticOrderNatAt g)).Finite := by
  refine (MeromorphicOn.divisor_ball_support_finite hg.meromorphicOn).subset ?_
  rintro a ⟨ha, ha0⟩
  rw [Function.mem_support] at ha0 ⊢
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hg.mono ball_subset_closedBall) ha]
  unfold analyticOrderNatAt at ha0
  cases h : analyticOrderAt g a with
  | top => rw [h] at ha0; simp at ha0
  | coe k =>
    rw [h] at ha0
    simp only [ENat.toNat_natCast] at ha0
    simp [ha0]

private theorem c_analyticOrderAt_ne_top {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hne : ∀ w ∈ sphere c r, g w ≠ 0) {a : ℂ}
    (ha : a ∈ closedBall c r) : analyticOrderAt g a ≠ ⊤ := by
  have hy : c + r ∈ sphere c r := by simp [abs_of_pos hr]
  refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hg
    (convex_closedBall c r).isPreconnected (sphere_subset_closedBall hy) ha ?_
  rw [analyticOrderAt_eq_zero.2 (Or.inr (hne _ hy))]
  exact ENat.zero_ne_top

private theorem c_eval_eq_monic_form {Q : Polynomial ℂ} {d : ℕ} (hQ : Q.Monic)
    (hdeg : Q.natDegree = d) (w : ℂ) :
    Q.eval w = w ^ d + ∑ j : Fin d, Q.coeff j * w ^ (j : ℕ) := by
  rw [Polynomial.eval_eq_sum_range, hdeg, Finset.sum_range_succ, ← hdeg, hQ.coeff_natDegree,
    hdeg, one_mul, add_comm, Fin.sum_univ_eq_sum_range (fun j => Q.coeff j * w ^ j)]

private theorem c_deriv_slice {n : ℕ} {f : (Fin n → ℂ) × ℂ → ℂ} {z : Fin n → ℂ} {w : ℂ}
    (hf : DifferentiableAt ℂ f (z, w)) :
    deriv (fun w => f (z, w)) w = fderiv ℂ f (z, w) (0, 1) := by
  have h1 : HasDerivAt (fun w : ℂ => (z, w)) ((0 : Fin n → ℂ), (1 : ℂ)) w :=
    (hasDerivAt_const w z).prodMk (hasDerivAt_id w)
  exact (hf.hasFDerivAt.comp_hasDerivAt w h1).deriv

theorem spec_exists_monicInLast_orders_aux {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ}
    {δ : ℝ} {c : ℂ} {r : ℝ} {d : ℕ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, f (z, w) ≠ 0)
    (hd : zeroCount (fun w => f (z₀, w)) c r = d) :
    ∃ a : Fin d → (Fin n → ℂ) → ℂ, (∀ j, AnalyticOnNhd ℂ (a j) (ball z₀ δ)) ∧
      ∀ z ∈ ball z₀ δ, (∀ w, monicInLast a (z, w) = 0 → w ∈ ball c r) ∧
        ∀ w ∈ ball c r, analyticOrderAt (fun w => monicInLast a (z, w)) w =
          analyticOrderAt (fun w => f (z, w)) w := by
  classical
  by_cases hr : 0 < r
  swap
  · have hb : ball c r = ∅ := ball_eq_empty.2 (not_lt.1 hr)
    have hd0 : d = 0 := by
      rw [← hd]
      simp [zeroCount, hb]
    subst hd0
    refine ⟨fun j => j.elim0, fun j => j.elim0, fun z _ => ⟨fun w hw => ?_, by simp [hb]⟩⟩
    simp [monicInLast] at hw
  have hslice : ∀ z ∈ closedBall z₀ δ, AnalyticOnNhd ℂ (fun w => f (z, w)) (closedBall c r) :=
    fun z hz ζ hζ =>
      AnalyticAt.comp_of_eq (hf (z, ζ) ⟨hz, hζ⟩) (analyticAt_const.prod analyticAt_id) rfl
  have hT : ∀ z, ∃ T : Finset ℂ, z ∈ closedBall z₀ δ →
      (T : Set ℂ) = ball c r ∩ Function.support (analyticOrderNatAt (fun w => f (z, w))) := by
    intro z
    by_cases hz : z ∈ closedBall z₀ δ
    · exact ⟨(c_finite_support_analyticOrderNatAt (hslice z hz)).toFinset, fun _ => by simp⟩
    · exact ⟨∅, fun h => absurd h hz⟩
  choose T hT using hT
  let S : (Fin n → ℂ) → Multiset ℂ := fun z =>
    ∑ a ∈ T z, Multiset.replicate (analyticOrderNatAt (fun w => f (z, w)) a) a
  have hfin : ∀ z ∈ closedBall z₀ δ, ∀ {M : Type} [AddCommMonoid M] (F : ℂ → M),
      Function.support F ⊆ Function.support (analyticOrderNatAt (fun w => f (z, w))) →
      ∑ᶠ (a : ℂ) (_ : a ∈ ball c r), F a = ∑ a ∈ T z, F a := by
    intro z hz M _ F hF
    refine finsum_mem_eq_sum_of_inter_support_eq F ?_
    rw [hT z hz, inter_assoc, inter_eq_right.2 hF]
  have hcard : ∀ z ∈ ball z₀ δ, Multiset.card (S z) = d := by
    intro z hz
    have hz' := ball_subset_closedBall hz
    simp only [S, Multiset.card_sum, Multiset.card_replicate]
    rw [← hfin z hz' _ subset_rfl, ← hd, ← spec_zeroCount_eq_of_sphere_ne_zero_aux hf hne hz]
    rfl
  have hpowsum : ∀ k : ℕ, ∀ z ∈ ball z₀ δ, ((S z).map (· ^ k)).sum =
      (2 * π * I)⁻¹ * ∮ w in C(c, r), w ^ k * deriv (fun w => f (z, w)) w / f (z, w) := by
    intro k z hz
    have hz' := ball_subset_closedBall hz
    rw [spec_circleIntegral_mul_logDeriv_aux (h := fun w : ℂ => w ^ k) hr (hslice z hz')
      (fun w _ => by fun_prop) (fun w hw => hne z hz' w hw)]
    have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]
    rw [hfin z hz' _ (fun a ha => by
      rw [Function.mem_support] at ha ⊢
      intro h0
      apply ha
      simp [h0])]
    simp only [S]
    have hhom : ∀ s : Multiset ℂ, (s.map (· ^ k)).sum =
        (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom (· ^ k))) s := fun s => rfl
    rw [hhom, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
  have hpowan : ∀ k : ℕ, AnalyticOnNhd ℂ (fun z => ((S z).map (· ^ k)).sum) (ball z₀ δ) := by
    intro k
    let G : (Fin n → ℂ) × ℂ → ℂ := fun q => q.2 ^ k * fderiv ℂ f q ((0 : Fin n → ℂ), (1 : ℂ)) / f q
    have hG : AnalyticOnNhd ℂ G (ball z₀ δ ×ˢ sphere c r) := by
      rintro ⟨z, w⟩ ⟨hz, hw⟩
      have hfq := hf (z, w) ⟨ball_subset_closedBall hz, sphere_subset_closedBall hw⟩
      refine AnalyticAt.div ((analyticAt_snd.pow k).mul ?_) hfq
        (hne z (ball_subset_closedBall hz) w hw)
      exact ((ContinuousLinearMap.apply ℂ ℂ ((0 : Fin n → ℂ), (1 : ℂ))).analyticAt _).comp
        hfq.fderiv
    have hint := spec_analyticOnNhd_circleIntegral_aux hr hG
    refine ((analyticOnNhd_const (v := (2 * π * I : ℂ)⁻¹)).mul hint).congr isOpen_ball
      fun z hz => ?_
    rw [hpowsum k z hz]
    congr 1
    refine circleIntegral.integral_congr hr.le fun w hw => ?_
    have hfq := hf (z, w) ⟨ball_subset_closedBall hz, sphere_subset_closedBall hw⟩
    simp only [G]
    rw [c_deriv_slice hfq.differentiableAt]
  let a : Fin d → (Fin n → ℂ) → ℂ := fun j z =>
    ((S z).map (fun α => Polynomial.X - Polynomial.C α)).prod.coeff j
  have ha : ∀ j, AnalyticOnNhd ℂ (a j) (ball z₀ δ) := fun j =>
    spec_analyticOnNhd_coeff_of_powerSum_aux isOpen_ball hcard (fun k _ _ => hpowan k) j
  refine ⟨a, ha, fun z hz => ?_⟩
  have hz' := ball_subset_closedBall hz
  set Q : Polynomial ℂ := ((S z).map (fun α => Polynomial.X - Polynomial.C α)).prod with hQ_def
  have hQm : Q.Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun α _ => Polynomial.monic_X_sub_C α
  have hQd : Q.natDegree = d := by
    rw [hQ_def, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard z hz]
  have hQe : (fun w => monicInLast a (z, w)) = fun w => Q.eval w := by
    funext w
    rw [c_eval_eq_monic_form hQm hQd]
    rfl
  have hroots : Q.roots = S z := Polynomial.roots_multiset_prod_X_sub_C (S z)
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have hw' : Q.IsRoot w := by
      have := congrFun hQe w
      rw [this] at hw
      exact hw
    have hmem : w ∈ S z := by
      rw [← hroots, Polynomial.mem_roots hQm.ne_zero]
      exact hw'
    obtain ⟨b, hb, hwb⟩ := Multiset.mem_sum.1 hmem
    rw [Multiset.eq_of_mem_replicate hwb]
    have : b ∈ (T z : Set ℂ) := hb
    rw [hT z hz'] at this
    exact this.1
  · rw [hQe, spec_analyticOrderAt_polynomial_eval_aux hQm.ne_zero w, ← Polynomial.count_roots,
      hroots]
    simp only [S, Multiset.count_sum', Multiset.count_replicate]
    rw [Finset.sum_ite_eq' (T z) w]
    rw [← Nat.cast_analyticOrderNatAt (c_analyticOrderAt_ne_top hr (hslice z hz')
      (fun x hx => hne z hz' x hx) (ball_subset_closedBall hw))]
    split_ifs with hwT
    · rfl
    · have : w ∉ ball c r ∩ Function.support (analyticOrderNatAt (fun w => f (z, w))) := by
        rw [← hT z hz']
        exact hwT
      simp only [mem_inter_iff, Function.mem_support, not_and, not_not] at this
      rw [this hw]

private theorem c_div_eventuallyEq_analytic {g h : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x)
    (hh : AnalyticAt ℂ h x) (hord : analyticOrderAt h x ≤ analyticOrderAt g x) :
    ∃ θ : ℂ → ℂ, AnalyticAt ℂ θ x ∧ (g / h) =ᶠ[𝓝[≠] x] θ := by
  cases hk : analyticOrderAt g x with
  | top =>
    refine ⟨0, analyticAt_const, ?_⟩
    filter_upwards [(analyticOrderAt_eq_top.1 hk).filter_mono nhdsWithin_le_nhds] with z hz
    simp [hz]
  | coe k =>
    rw [hk] at hord
    cases hm : analyticOrderAt h x with
    | top => rw [hm] at hord; simp at hord
    | coe m =>
      rw [hm] at hord
      have hmk : m ≤ k := by exact_mod_cast hord
      obtain ⟨g₁, hg₁, hg₁0, hgf⟩ := hg.analyticOrderAt_eq_natCast.1 hk
      obtain ⟨h₁, hh₁, hh₁0, hhf⟩ := hh.analyticOrderAt_eq_natCast.1 hm
      refine ⟨fun z => (z - x) ^ (k - m) * g₁ z / h₁ z, by fun_prop (disch := assumption), ?_⟩
      filter_upwards [hgf.filter_mono nhdsWithin_le_nhds, hhf.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z hz1 hz2 hz3
      have hzx : z - x ≠ 0 := sub_ne_zero.2 hz3
      simp only [Pi.div_apply, hz1, hz2, smul_eq_mul]
      rw [show k = (k - m) + m by omega, pow_add]
      rw [Nat.add_sub_cancel]
      by_cases hz4 : h₁ z = 0
      · simp [hz4]
      · field_simp


private theorem c_exists_analytic_div_extension {g h : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hh : AnalyticOnNhd ℂ h (closedBall c r))
    (hne : ∀ x ∈ sphere c r, h x ≠ 0)
    (hord : ∀ x ∈ ball c r, analyticOrderAt h x ≤ analyticOrderAt g x) :
    ∃ ψ : ℂ → ℂ, AnalyticOnNhd ℂ ψ (closedBall c r) ∧
      ∀ x ∈ closedBall c r, h x ≠ 0 → ψ x = g x / h x := by
  have hM : MeromorphicOn (g / h) (closedBall c r) :=
    fun y hy => (hg y hy).meromorphicAt.div (hh y hy).meromorphicAt
  refine ⟨toMeromorphicNFOn (g / h) (closedBall c r), fun x hx => ?_, fun x hx hx0 => ?_⟩
  · have hord' : analyticOrderAt h x ≤ analyticOrderAt g x := by
      rcases (mem_closedBall.1 hx).lt_or_eq with hlt | heq
      · exact hord x (mem_ball.2 hlt)
      · have : analyticOrderAt h x = 0 :=
          analyticOrderAt_eq_zero.2 (Or.inr (hne x (mem_sphere.2 heq)))
        rw [this]
        exact zero_le
    obtain ⟨θ, hθ, hθe⟩ := c_div_eventuallyEq_analytic (hg x hx) (hh x hx) hord'
    have h1 := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hM hx
    have h2 : toMeromorphicNFAt (g / h) x =ᶠ[𝓝 x] θ :=
      (meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
        hθ.meromorphicNFAt).1 ((hM x hx).eq_nhdsNE_toMeromorphicNFAt.symm.trans hθe)
    exact (analyticAt_congr (h1.trans h2)).2 hθ
  · have hA : AnalyticAt ℂ (g / h) x := (hg x hx).div (hh x hx) hx0
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM hx,
      toMeromorphicNFAt_eq_self.2 hA.meromorphicNFAt]
    rfl

private theorem c_circleIntegral_div_eq {g h : ℂ → ℂ} {c w : ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hh : AnalyticOnNhd ℂ h (closedBall c r))
    (hne : ∀ x ∈ sphere c r, h x ≠ 0)
    (hord : ∀ x ∈ ball c r, analyticOrderAt h x ≤ analyticOrderAt g x) (hw : w ∈ ball c r)
    (hw0 : h w ≠ 0) :
    (∮ ζ in C(c, r), g ζ / (h ζ * (ζ - w))) = 2 * π * I * (g w / h w) := by
  have hr : 0 < r := (dist_nonneg.trans_lt (mem_ball.1 hw))
  obtain ⟨ψ, hψ, hψe⟩ := c_exists_analytic_div_extension hg hh hne hord
  have hcauchy := hψ.differentiableOn.circleIntegral_sub_inv_smul hw
  rw [hψe w (ball_subset_closedBall hw) hw0, smul_eq_mul] at hcauchy
  rw [← hcauchy]
  refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
  have hζw : ζ - w ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    subst h0
    rw [mem_sphere] at hζ
    rw [mem_ball] at hw
    linarith
  simp only [smul_eq_mul]
  rw [hψe ζ (sphere_subset_closedBall hζ) (hne ζ hζ)]
  field_simp

theorem spec_exists_analytic_quotient_aux {f P : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ}
    {δ : ℝ} {c : ℂ} {r : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hP : AnalyticOnNhd ℂ P (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, P (z, w) ≠ 0)
    (hord : ∀ z ∈ ball z₀ δ, ∀ w ∈ ball c r,
      analyticOrderAt (fun w => P (z, w)) w ≤ analyticOrderAt (fun w => f (z, w)) w) :
    ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticOnNhd ℂ u (ball z₀ δ ×ˢ ball c r) ∧
      ∀ p ∈ ball z₀ δ ×ˢ ball c r, f p = u p * P p := by
  by_cases hr : 0 < r
  swap
  · have hb : ball c r = ∅ := ball_eq_empty.2 (not_lt.1 hr)
    exact ⟨0, by simp [hb], by simp [hb]⟩
  have hslice : ∀ {G : (Fin n → ℂ) × ℂ → ℂ},
      AnalyticOnNhd ℂ G (closedBall z₀ δ ×ˢ closedBall c r) → ∀ z ∈ ball z₀ δ,
        AnalyticOnNhd ℂ (fun ζ => G (z, ζ)) (closedBall c r) := by
    intro G hG z hz ζ hζ
    exact AnalyticAt.comp_of_eq (hG (z, ζ) ⟨ball_subset_closedBall hz, hζ⟩)
      (analyticAt_const.prod analyticAt_id) rfl
  let F : ((Fin n → ℂ) × ℂ) × ℂ → ℂ := fun q => f (q.1.1, q.2) / (P (q.1.1, q.2) * (q.2 - q.1.2))
  have hF : AnalyticOnNhd ℂ F ((ball z₀ δ ×ˢ ball c r) ×ˢ sphere c r) := by
    rintro ⟨⟨z, w⟩, ζ⟩ ⟨⟨hz, hw⟩, hζ⟩
    have hm : AnalyticAt ℂ (fun q : ((Fin n → ℂ) × ℂ) × ℂ => (q.1.1, q.2)) ((z, w), ζ) :=
      (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
    have hmem : (z, ζ) ∈ closedBall z₀ δ ×ˢ closedBall c r :=
      ⟨ball_subset_closedBall hz, sphere_subset_closedBall hζ⟩
    have hζw : ζ - w ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      subst h0
      rw [mem_sphere] at hζ
      rw [mem_ball] at hw
      linarith
    refine AnalyticAt.div (AnalyticAt.comp_of_eq (hf _ hmem) hm rfl)
      ((AnalyticAt.comp_of_eq (hP _ hmem) hm rfl).mul
        (analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst))) ?_
    exact mul_ne_zero (hne z (ball_subset_closedBall hz) ζ hζ) hζw
  refine ⟨fun p => (2 * π * I)⁻¹ * ∮ ζ in C(c, r), F (p, ζ),
    fun p hp => analyticAt_const.mul (spec_analyticOnNhd_circleIntegral_aux hr hF p hp), ?_⟩
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  have hg := hslice hf z hz
  have hh := hslice hP z hz
  by_cases hPw : P (z, w) = 0
  · have h1 : analyticOrderAt (fun ζ => P (z, ζ)) w ≠ 0 :=
      analyticOrderAt_ne_zero.2 ⟨hh w (ball_subset_closedBall hw), hPw⟩
    have h2 : analyticOrderAt (fun ζ => f (z, ζ)) w ≠ 0 := by
      intro h0
      have := hord z hz w hw
      rw [h0] at this
      exact h1 (le_antisymm this zero_le)
    have := apply_eq_zero_of_analyticOrderAt_ne_zero h2
    rw [this, hPw, mul_zero]
  · have := c_circleIntegral_div_eq hg hh (fun x hx => hne z (ball_subset_closedBall hz) x hx)
      (hord z hz) hw hPw
    simp only [F]
    rw [this]
    have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    field_simp

end Coefficients

section Preparation

variable {n : ℕ}

private theorem c_monicInLast_zero_left {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, a j 0 = 0)
    (w : ℂ) : monicInLast a (0, w) = w ^ d := by
  simp [monicInLast, ha]

private theorem c_coeff_eq_zero_of_analyticOrderAt {d : ℕ} (b : Fin d → ℂ)
    (h : analyticOrderAt (fun w : ℂ => w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) 0 = d) (j : Fin d) :
    b j = 0 := by
  classical
  set p : Polynomial ℂ :=
    Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ) with hp_def
  have hdeg : (∑ i : Fin d, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)).degree < (d : WithBot ℕ) :=
    Polynomial.degree_sum_fin_lt b
  have hmon : p.Monic := Polynomial.monic_X_pow_add hdeg
  have heval : (fun w : ℂ => p.eval w) = fun w : ℂ => w ^ d + ∑ i : Fin d, b i * w ^ (i : ℕ) := by
    funext w
    simp [hp_def, Polynomial.eval_finsetSum]
  have hroot : p.rootMultiplicity 0 = d := by
    have := spec_analyticOrderAt_polynomial_eval_aux hmon.ne_zero 0
    rw [heval, h] at this
    exact_mod_cast this.symm
  have hdvd : (Polynomial.X : Polynomial ℂ) ^ d ∣ p := by
    have := Polynomial.pow_rootMultiplicity_dvd p 0
    simpa [hroot] using this
  have hnat : p.natDegree ≤ d := by
    rw [hp_def, Polynomial.natDegree_add_eq_left_of_degree_lt
      (by rwa [Polynomial.degree_X_pow])]
    simp
  have hpX : p = Polynomial.X ^ d :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (Polynomial.monic_X_pow d) hmon hdvd
      (by simpa using hnat)
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff j) hpX
  simp only [hp_def, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow] at hc
  have hj : (j : ℕ) ≠ d := j.isLt.ne
  simp only [hj, ite_false, zero_add] at hc
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [Fin.val_inj, Ne.symm hij])
    (by simp)] at hc
  simpa using hc

private theorem c_analyticOrderAt_slice_mul_pow {u : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ}
    (hu : AnalyticAt ℂ u 0) :
    analyticOrderAt (fun w : ℂ => u (0, w) * w ^ d) 0 =
      analyticOrderAt (fun w : ℂ => u (0, w)) 0 + d := by
  have hu' : AnalyticAt ℂ (fun w : ℂ => u (0, w)) 0 := by
    have : AnalyticAt ℂ (fun w : ℂ => ((0 : Fin n → ℂ), w)) 0 := by fun_prop
    exact AnalyticAt.comp_of_eq hu this (by simp)
  rw [show (fun w : ℂ => u (0, w) * w ^ d) = (fun w : ℂ => u (0, w)) * fun w => w ^ d from rfl,
    analyticOrderAt_mul hu' (by fun_prop)]
  have h1 : analyticOrderAt (fun w : ℂ => w ^ d) 0 = d := by
    have h := analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := 0) (n := d)
    simp only [sub_zero] at h
    exact h
  rw [h1]

private theorem c_slice_eventuallyEq {f u : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, a j 0 = 0)
    (hfu : f =ᶠ[𝓝 0] fun p => u p * monicInLast a p) :
    (fun w => f (0, w)) =ᶠ[𝓝 0] fun w => u (0, w) * w ^ d := by
  have hc : Continuous fun w : ℂ => ((0 : Fin n → ℂ), w) := by fun_prop
  have := hc.tendsto 0
  simp only [Prod.mk_zero_zero] at this
  filter_upwards [this.eventually hfu] with w hw
  rw [hw, c_monicInLast_zero_left ha]

theorem spec_weierstrass_preparation_aux {f : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f 0) (hd : analyticOrderAt (fun w => f (0, w)) 0 = d) :
    ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∃ a : Fin d → (Fin n → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0) ∧
        f =ᶠ[𝓝 0] fun p => u p * monicInLast a p := by
  have hf' : AnalyticAt ℂ f ((0 : Fin n → ℂ), (0 : ℂ)) := by
    rw [Prod.mk_zero_zero]; exact hf
  obtain ⟨r, hr, -, δ, hδ, hfan, hne, hcount⟩ :=
    spec_exists_zeroCount_eq_order_aux hf' hd one_pos
  obtain ⟨a, ha, hroots⟩ :=
    spec_exists_monicInLast_orders_aux hfan hne (hcount 0 (mem_ball_self hδ))
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hsub : closedBall (0 : Fin n → ℂ) (δ / 2) ⊆ ball 0 δ :=
    closedBall_subset_ball (half_lt_self hδ)
  have hPan : AnalyticOnNhd ℂ (monicInLast a) (closedBall 0 (δ / 2) ×ˢ closedBall 0 r) := by
    intro p hp
    have haj : ∀ j, AnalyticAt ℂ (fun q : (Fin n → ℂ) × ℂ => a j q.1) p :=
      fun j => (ha j p.1 (hsub hp.1)).comp analyticAt_fst
    show AnalyticAt ℂ (fun q : (Fin n → ℂ) × ℂ => q.2 ^ d + ∑ j : Fin d, a j q.1 * q.2 ^ (j : ℕ)) p
    exact (analyticAt_snd.pow d).add
      (Finset.analyticAt_fun_sum _ fun j _ => (haj j).mul (analyticAt_snd.pow _))
  have hneP : ∀ z ∈ closedBall (0 : Fin n → ℂ) (δ / 2), ∀ w ∈ sphere (0 : ℂ) r,
      monicInLast a (z, w) ≠ 0 := by
    intro z hz w hw h0
    have := (hroots z (hsub hz)).1 w h0
    rw [mem_sphere] at hw
    rw [mem_ball] at this
    linarith
  have hord : ∀ z ∈ ball (0 : Fin n → ℂ) (δ / 2), ∀ w ∈ ball (0 : ℂ) r,
      analyticOrderAt (fun w => monicInLast a (z, w)) w ≤ analyticOrderAt (fun w => f (z, w)) w :=
    fun z hz w hw => ((hroots z (ball_subset_ball (half_le_self hδ.le) hz)).2 w hw).le
  obtain ⟨u, hu, hfu⟩ := spec_exists_analytic_quotient_aux
    (hfan.mono (prod_mono (closedBall_subset_closedBall (half_le_self hδ.le)) subset_rfl))
    hPan hneP hord
  have hmem : (0 : (Fin n → ℂ) × ℂ) ∈ ball (0 : Fin n → ℂ) (δ / 2) ×ˢ ball (0 : ℂ) r :=
    ⟨mem_ball_self hδ2, mem_ball_self hr⟩
  have hnhds : ball (0 : Fin n → ℂ) (δ / 2) ×ˢ ball (0 : ℂ) r ∈ 𝓝 (0 : (Fin n → ℂ) × ℂ) :=
    (isOpen_ball.prod isOpen_ball).mem_nhds hmem
  have hfuP : f =ᶠ[𝓝 0] fun p => u p * monicInLast a p := by
    filter_upwards [hnhds] with p hp
    exact hfu p hp
  have ha0 : ∀ j, a j 0 = 0 := by
    intro j
    refine c_coeff_eq_zero_of_analyticOrderAt (fun j => a j 0) ?_ j
    have := (hroots 0 (mem_ball_self hδ)).2 0 (mem_ball_self hr)
    rw [hd] at this
    exact this
  have hu0 : u 0 ≠ 0 := by
    intro hu0
    have h1 := c_analyticOrderAt_slice_mul_pow (d := d) (hu 0 hmem)
    rw [← analyticOrderAt_congr (c_slice_eventuallyEq ha0 hfuP), hd] at h1
    have h2 : analyticOrderAt (fun w : ℂ => u (0, w)) 0 ≠ 0 := by
      rw [analyticOrderAt_ne_zero]
      refine ⟨?_, by rw [Prod.mk_zero_zero]; exact hu0⟩
      have : AnalyticAt ℂ (fun w : ℂ => ((0 : Fin n → ℂ), w)) 0 := by fun_prop
      exact AnalyticAt.comp_of_eq (hu 0 hmem) this (by simp)
    revert h1 h2
    generalize analyticOrderAt (fun w : ℂ => u (0, w)) 0 = x
    induction x using ENat.recTopCoe with
    | top => simp
    | coe x =>
      intro h1 h2
      norm_cast at h1 h2
      omega
  exact ⟨u, hu 0 hmem, hu0, a, fun j => ⟨ha j 0 (mem_ball_self hδ), ha0 j⟩, hfuP⟩

theorem spec_analyticOrderAt_of_preparation_aux {f u : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (ha : ∀ j, a j 0 = 0) (hfu : f =ᶠ[𝓝 0] fun p => u p * monicInLast a p) :
    analyticOrderAt (fun w => f (0, w)) 0 = d := by
  rw [analyticOrderAt_congr (c_slice_eventuallyEq ha hfu), c_analyticOrderAt_slice_mul_pow hu]
  have h0 : analyticOrderAt (fun w : ℂ => u (0, w)) 0 = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr (by rw [← Prod.mk_zero_zero] at hu0; exact hu0))
  rw [h0, zero_add]

theorem spec_not_exists_preparation_coord_aux :
    ¬ ∃ (d : ℕ) (u : (Fin 1 → ℂ) × ℂ → ℂ) (a : Fin d → (Fin 1 → ℂ) → ℂ),
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧ (∀ j, a j 0 = 0) ∧
      (fun p : (Fin 1 → ℂ) × ℂ => p.1 0) =ᶠ[𝓝 0] fun p => u p * monicInLast a p := by
  rintro ⟨d, u, a, hu, hu0, ha, hfu⟩
  have h := spec_analyticOrderAt_of_preparation_aux hu hu0 ha hfu
  have htop : analyticOrderAt (fun w : ℂ => ((0 : Fin 1 → ℂ), w).1 0) 0 = ⊤ :=
    analyticOrderAt_eq_top.mpr (Eventually.of_forall fun w => by simp)
  rw [htop] at h
  exact ENat.top_ne_natCast d h

theorem spec_monicInLast_roots_small_aux {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    (ha : ∀ j, ContinuousAt (a j) 0) (ha0 : ∀ j, a j 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 0, ∀ w, monicInLast a (z, w) = 0 → ‖w‖ < ε := by
  set t := min ε 1 with ht
  have ht0 : 0 < t := lt_min hε one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  set η := t ^ d / (d + 1) with hη
  have hη0 : 0 < η := by positivity
  have hev : ∀ᶠ z in 𝓝 0, ∀ j, ‖a j z‖ < η := by
    rw [Filter.eventually_all]
    intro j
    have := (ha j).eventually (Metric.ball_mem_nhds (a j 0) hη0)
    filter_upwards [this] with z hz
    simpa [ha0 j, Metric.mem_ball, dist_zero_right] using hz
  filter_upwards [hev] with z hz w hw
  by_contra hlt
  push Not at hlt
  have htw : t ≤ ‖w‖ := (min_le_left _ _).trans hlt
  have hw0 : 0 < ‖w‖ := ht0.trans_le htw
  have hroot : w ^ d = -∑ j : Fin d, a j z * w ^ (j : ℕ) := by
    simp only [monicInLast] at hw; linear_combination hw
  have hterm : ∀ j : Fin d, ‖a j z * w ^ (j : ℕ)‖ ≤ η * (‖w‖ ^ d / t ^ d) := by
    intro j
    rw [norm_mul, norm_pow]
    apply mul_le_mul (hz j).le _ (by positivity) hη0.le
    rw [le_div_iff₀ (by positivity)]
    have hj : (j : ℕ) ≤ d := j.2.le
    calc ‖w‖ ^ (j : ℕ) * t ^ d = ‖w‖ ^ (j : ℕ) * (t ^ (j : ℕ) * t ^ (d - j)) := by
          rw [← pow_add, Nat.add_sub_cancel' hj]
      _ ≤ ‖w‖ ^ (j : ℕ) * (1 * ‖w‖ ^ (d - j)) := by
          gcongr
          · exact pow_le_one₀ ht0.le ht1
      _ = ‖w‖ ^ d := by rw [one_mul, ← pow_add, Nat.add_sub_cancel' hj]
  have hsum : ‖w‖ ^ d ≤ d * (η * (‖w‖ ^ d / t ^ d)) := by
    calc ‖w‖ ^ d = ‖w ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ j : Fin d, a j z * w ^ (j : ℕ)‖ := by rw [hroot, norm_neg]
      _ ≤ ∑ j : Fin d, ‖a j z * w ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin d, η * (‖w‖ ^ d / t ^ d) := Finset.sum_le_sum fun j _ => hterm j
      _ = d * (η * (‖w‖ ^ d / t ^ d)) := by simp
  have hcalc : (d : ℝ) * (η * (‖w‖ ^ d / t ^ d)) = d / (d + 1) * ‖w‖ ^ d := by
    rw [hη]; field_simp
  rw [hcalc] at hsum
  have hpos : 0 < ‖w‖ ^ d := by positivity
  have : (d : ℝ) / (d + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  nlinarith

/-- The coefficient of `w ^ j` in `(P (ζ) - P (w)) / (ζ - w)` for the monic polynomial
`P (X) = X ^ d + ∑_{m < d} A m X ^ m`: `ζ ^ (d - 1 - j) + ∑_{j < m < d} A m ζ ^ (m - 1 - j)`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, Theorem 1
(proof of Weierstrass division, the difference quotient of the Weierstrass polynomial). -/
private def divCoeff {d : ℕ} (A : Fin d → ℂ) (ζ : ℂ) (j : Fin d) : ℂ :=
  ζ ^ (d - 1 - j) + ∑ m : Fin d, A m * (if (j : ℕ) < m then ζ ^ ((m : ℕ) - 1 - j) else 0)

example (ζ : ℂ) : divCoeff (fun _ : Fin 1 => (0 : ℂ)) ζ 0 = 1 := by
  simp [divCoeff]

private lemma geom_fin {d k : ℕ} (hk : k ≤ d) (ζ w : ℂ) :
    (ζ - w) * ∑ j : Fin d, (if (j : ℕ) < k then ζ ^ (k - 1 - j) * w ^ (j : ℕ) else 0) =
      ζ ^ k - w ^ k := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then ζ ^ (k - 1 - i) * w ^ i else 0),
    ← Finset.sum_filter]
  have hf : (Finset.range d).filter (· < k) = Finset.range k := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf]
  have := geom_sum₂_mul w ζ k
  linear_combination (-1 : ℂ) * this +
    (ζ - w) * (Finset.sum_congr rfl fun i _ => mul_comm (ζ ^ (k - 1 - i)) (w ^ i) :
      ∑ i ∈ Finset.range k, ζ ^ (k - 1 - i) * w ^ i = ∑ i ∈ Finset.range k, w ^ i * ζ ^ (k - 1 - i))

private lemma sub_eq_mul_divCoeff {d : ℕ} (A : Fin d → ℂ) (ζ w : ℂ) :
    (ζ ^ d + ∑ m : Fin d, A m * ζ ^ (m : ℕ)) - (w ^ d + ∑ m : Fin d, A m * w ^ (m : ℕ)) =
      (ζ - w) * ∑ j : Fin d, divCoeff A ζ j * w ^ (j : ℕ) := by
  have h1 : ∑ j : Fin d, divCoeff A ζ j * w ^ (j : ℕ) =
      ∑ j : Fin d, (if (j : ℕ) < d then ζ ^ (d - 1 - j) * w ^ (j : ℕ) else 0) +
      ∑ m : Fin d, A m *
        ∑ j : Fin d, (if (j : ℕ) < m then ζ ^ ((m : ℕ) - 1 - j) * w ^ (j : ℕ) else 0) := by
    simp only [divCoeff, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by simp [j.2]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
  rw [h1, mul_add, geom_fin le_rfl, Finset.mul_sum]
  have h2 : ∀ m : Fin d, (ζ - w) * (A m *
      ∑ j : Fin d, (if (j : ℕ) < m then ζ ^ ((m : ℕ) - 1 - j) * w ^ (j : ℕ) else 0)) =
      A m * ζ ^ (m : ℕ) - A m * w ^ (m : ℕ) := by
    intro m
    rw [mul_left_comm, geom_fin m.2.le]; ring
  simp only [h2, Finset.sum_sub_distrib]
  ring

private lemma analyticAt_monicInLast {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z) (ζ : ℂ) : AnalyticAt ℂ (monicInLast a) (z, ζ) := by
  show AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => p.2 ^ d + ∑ j : Fin d, a j p.1 * p.2 ^ (j : ℕ))
    (z, ζ)
  exact (analyticAt_snd.pow d).add (Finset.analyticAt_fun_sum _ fun j _ =>
    ((ha j).comp analyticAt_fst).mul (analyticAt_snd.pow _))

private lemma analyticAt_divCoeff {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z) (ζ : ℂ) (j : Fin d) :
    AnalyticAt ℂ (fun x : (Fin n → ℂ) × ℂ => divCoeff (fun m => a m x.1) x.2 j) (z, ζ) := by
  unfold divCoeff
  refine (analyticAt_snd.pow _).add (Finset.analyticAt_fun_sum _ fun m _ =>
    ((ha m).comp analyticAt_fst).mul ?_)
  split_ifs
  · exact analyticAt_snd.pow _
  · exact analyticAt_const

theorem spec_weierstrass_division_aux {g : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (hg : AnalyticAt ℂ g 0) (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (ha0 : ∀ j, a j 0 = 0) :
    ∃ q : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∃ b : Fin d → (Fin n → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (b j) 0) ∧
        g =ᶠ[𝓝 0] fun p => q p * monicInLast a p + ∑ j, b j p.1 * p.2 ^ (j : ℕ) := by
  obtain ⟨ρ, hρ, hgρ⟩ := hg.exists_ball_analyticOnNhd
  have haev : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j, AnalyticAt ℂ (a j) z :=
    eventually_all.mpr fun j => (ha j).eventually_analyticAt
  set r := ρ / 2 with hrdef
  have hr : 0 < r := half_pos hρ
  obtain ⟨δ₀, hδ₀, hδ₀h⟩ := Metric.eventually_nhds_iff_ball.mp
    (haev.and (spec_monicInLast_roots_small_aux (fun j => (ha j).continuousAt) ha0 hr))
  set δ := min δ₀ ρ with hδdef
  have hδ : 0 < δ := lt_min hδ₀ hρ
  have hzδ : ∀ z : Fin n → ℂ, ‖z‖ < δ →
      (∀ j, AnalyticAt ℂ (a j) z) ∧ ∀ w, monicInLast a (z, w) = 0 → ‖w‖ < r := fun z hz =>
    hδ₀h z (mem_ball_zero_iff.mpr (hz.trans_le (min_le_left _ _)))
  have hgat : ∀ z ζ, ‖z‖ < δ → ‖ζ‖ ≤ r → AnalyticAt ℂ g (z, ζ) := fun z ζ hz hζ =>
    hgρ _ (mem_ball_zero_iff.mpr (by
      rw [Prod.norm_mk]
      exact max_lt (hz.trans_le (min_le_right _ _)) (hζ.trans_lt (half_lt_self hρ))))
  have hPne : ∀ z ζ, ‖z‖ < δ → ‖ζ‖ = r → monicInLast a (z, ζ) ≠ 0 := fun z ζ hz hζ h0 =>
    ((hzδ z hz).2 ζ h0).ne hζ
  set Fq : ((Fin n → ℂ) × ℂ) × ℂ → ℂ :=
    fun x => g (x.1.1, x.2) / (monicInLast a (x.1.1, x.2) * (x.2 - x.1.2)) with hFqdef
  set Fb : Fin d → (Fin n → ℂ) × ℂ → ℂ :=
    fun j x => g x / monicInLast a x * divCoeff (fun m => a m x.1) x.2 j with hFbdef
  set s := min δ r with hsdef
  have hs : 0 < s := lt_min hδ hr
  have hFq : AnalyticOnNhd ℂ Fq (ball 0 s ×ˢ sphere 0 r) := by
    rintro ⟨⟨z, w⟩, ζ⟩ ⟨hp, hζ⟩
    rw [mem_ball_zero_iff, Prod.norm_mk] at hp
    rw [mem_sphere_zero_iff_norm] at hζ
    change ‖ζ‖ = r at hζ
    have hz : ‖z‖ < δ := (le_max_left _ _).trans_lt (hp.trans_le (min_le_left _ _))
    have hw : ‖w‖ < r := (le_max_right _ _).trans_lt (hp.trans_le (min_le_right _ _))
    have hmap : AnalyticAt ℂ (fun x : ((Fin n → ℂ) × ℂ) × ℂ => (x.1.1, x.2)) ((z, w), ζ) :=
      (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
    have hg' : AnalyticAt ℂ (fun x : ((Fin n → ℂ) × ℂ) × ℂ => g (x.1.1, x.2)) ((z, w), ζ) :=
      (hgat z ζ hz hζ.le).comp_of_eq hmap rfl
    have hP' : AnalyticAt ℂ (fun x : ((Fin n → ℂ) × ℂ) × ℂ => monicInLast a (x.1.1, x.2))
        ((z, w), ζ) :=
      (analyticAt_monicInLast (hzδ z hz).1 ζ).comp_of_eq hmap rfl
    have hsub : AnalyticAt ℂ (fun x : ((Fin n → ℂ) × ℂ) × ℂ => x.2 - x.1.2) ((z, w), ζ) :=
      analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)
    refine hg'.div (hP'.mul hsub) ?_
    refine mul_ne_zero (hPne z ζ hz hζ) (sub_ne_zero.mpr ?_)
    intro h; change ζ = w at h; subst h; exact hw.ne hζ
  have hFb : ∀ j, AnalyticOnNhd ℂ (Fb j) (ball 0 δ ×ˢ sphere 0 r) := by
    rintro j ⟨z, ζ⟩ ⟨hz, hζ⟩
    rw [mem_ball_zero_iff] at hz
    rw [mem_sphere_zero_iff_norm] at hζ
    exact ((hgat z ζ hz hζ.le).div (analyticAt_monicInLast (hzδ z hz).1 ζ)
      (hPne z ζ hz hζ)).mul (analyticAt_divCoeff (hzδ z hz).1 ζ j)
  have hq8 := spec_analyticOnNhd_circleIntegral_aux hr hFq
  have hb8 := fun j => spec_analyticOnNhd_circleIntegral_aux hr (hFb j)
  refine ⟨fun p => (2 * π * I)⁻¹ * ∮ ζ in C(0, r), Fq (p, ζ),
    analyticAt_const.mul (hq8 0 (mem_ball_self hs)),
    fun j z => (2 * π * I)⁻¹ * ∮ ζ in C(0, r), Fb j (z, ζ),
    fun j => analyticAt_const.mul (hb8 j 0 (mem_ball_self hδ)), ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hs)] with p hp
  obtain ⟨z, w⟩ := p
  have hp' := hp
  rw [mem_ball_zero_iff, Prod.norm_mk] at hp'
  have hz : ‖z‖ < δ := (le_max_left _ _).trans_lt (hp'.trans_le (min_le_left _ _))
  have hw : ‖w‖ < r := (le_max_right _ _).trans_lt (hp'.trans_le (min_le_right _ _))
  have hC : (∮ ζ in C(0, r), (ζ - w)⁻¹ • g (z, ζ)) = (2 * π * I : ℂ) • g (z, w) := by
    refine DifferentiableOn.circleIntegral_sub_inv_smul (fun ζ hζ => ?_)
      (mem_ball_zero_iff.mpr hw)
    rw [mem_closedBall_zero_iff] at hζ
    exact ((hgat z ζ hz hζ).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
      ).differentiableAt.differentiableWithinAt
  have hFqc : ContinuousOn (fun ζ => Fq ((z, w), ζ)) (sphere 0 r) := fun ζ hζ =>
    ((hFq ((z, w), ζ) ⟨hp, hζ⟩).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hFbc : ∀ j, ContinuousOn (fun ζ => Fb j (z, ζ)) (sphere 0 r) := fun j ζ hζ =>
    ((hFb j (z, ζ) ⟨mem_ball_zero_iff.mpr hz, hζ⟩).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hEq : EqOn (fun ζ => (ζ - w)⁻¹ • g (z, ζ))
      (fun ζ => monicInLast a (z, w) * Fq ((z, w), ζ) +
        ∑ j : Fin d, w ^ (j : ℕ) * Fb j (z, ζ)) (sphere 0 r) := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    have hP := hPne z ζ hz hζ
    have hζw : ζ - w ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hw.ne hζ)
    have key := sub_eq_mul_divCoeff (fun m => a m z) ζ w
    simp only [hFqdef, hFbdef, smul_eq_mul]
    simp only [monicInLast] at hP ⊢
    have hs2 : ∑ j : Fin d, w ^ (j : ℕ) * (g (z, ζ) / (ζ ^ d + ∑ j : Fin d, a j z * ζ ^ (j : ℕ)) *
        divCoeff (fun m => a m z) ζ j) = g (z, ζ) / (ζ ^ d + ∑ j : Fin d, a j z * ζ ^ (j : ℕ)) *
        ∑ j : Fin d, divCoeff (fun m => a m z) ζ j * w ^ (j : ℕ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs2]
    field_simp
    linear_combination g (z, ζ) * key
  have hI : (∮ ζ in C(0, r), (ζ - w)⁻¹ • g (z, ζ)) = monicInLast a (z, w) *
      (∮ ζ in C(0, r), Fq ((z, w), ζ)) + ∑ j : Fin d, w ^ (j : ℕ) * ∮ ζ in C(0, r), Fb j (z, ζ) := by
    have i1 : CircleIntegrable (fun ζ => monicInLast a (z, w) * Fq ((z, w), ζ)) 0 r :=
      (continuousOn_const.mul hFqc).circleIntegrable hr.le
    have i2 : ∀ j : Fin d, CircleIntegrable (fun ζ => w ^ (j : ℕ) * Fb j (z, ζ)) 0 r :=
      fun j => (continuousOn_const.mul (hFbc j)).circleIntegrable hr.le
    have i3 : CircleIntegrable (fun ζ => ∑ j : Fin d, w ^ (j : ℕ) * Fb j (z, ζ)) 0 r :=
      (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul (hFbc j)).circleIntegrable
        hr.le
    rw [circleIntegral.integral_congr hr.le hEq, circleIntegral.integral_add i1 i3,
      circleIntegral.integral_const_mul, circleIntegral.integral_fun_sum fun j _ => i2 j]
    simp only [circleIntegral.integral_const_mul]
  rw [hC, smul_eq_mul] at hI
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hsum : ∑ j : Fin d, ((2 * π * I)⁻¹ * ∮ ζ in C(0, r), Fb j ((z, w).1, ζ)) * (z, w).2 ^ (j : ℕ)
      = (2 * π * I)⁻¹ * ∑ j : Fin d, w ^ (j : ℕ) * ∮ ζ in C(0, r), Fb j (z, ζ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  field_simp
  linear_combination hI

/-- The monic polynomial `X ^ d + ∑_{j < d} C (a j z) X ^ j` in `ℂ[X]` whose evaluation at `w` is
`monicInLast a (z, w)`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B,
Definition 2 (a Weierstrass polynomial as a monic polynomial over the coefficient values). -/
private def monicPoly {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (a j z) * Polynomial.X ^ (j : ℕ)

example (a : Fin 0 → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : monicPoly a z = 1 := by
  simp [monicPoly]

private lemma monicPoly_eval {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (w : ℂ) :
    (monicPoly a z).eval w = monicInLast a (z, w) := by
  simp [monicPoly, monicInLast, Polynomial.eval_finsetSum]

private lemma monicPoly_monic {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (monicPoly a z).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)

private lemma monicPoly_natDegree {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (monicPoly a z).natDegree = d := by
  unfold monicPoly
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact Polynomial.degree_sum_fin_lt _

private lemma coeff_sum_fin {d : ℕ} (b : Fin d → ℂ) (j : Fin d) :
    (∑ i : Fin d, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)).coeff j = b j := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]
  simp

/-- For one parameter `z`: if `q (z, ·) · P (z, ·) + R_z = 0` on `ball 0 ρ`, `q (z, ·)` is analytic
there, every root of `P (z, ·)` lies in `ball 0 ρ` and `R_z` has degree `< d`, then `R_z = 0` and
`q (z, ·) = 0` on `ball 0 ρ`. -/
private lemma division_unique_fiber {d : ℕ} {a b : Fin d → (Fin n → ℂ) → ℂ}
    {q : (Fin n → ℂ) × ℂ → ℂ} {z : Fin n → ℂ} {ρ : ℝ}
    (hq : ∀ w, ‖w‖ < ρ → AnalyticAt ℂ (fun w => q (z, w)) w)
    (hid : ∀ w, ‖w‖ < ρ →
      q (z, w) * monicInLast a (z, w) + ∑ j, b j z * w ^ (j : ℕ) = 0)
    (hroots : ∀ w, monicInLast a (z, w) = 0 → ‖w‖ < ρ) :
    (∀ j, b j z = 0) ∧ ∀ w, ‖w‖ < ρ → q (z, w) = 0 := by
  set p := monicPoly a z with hpdef
  set R : Polynomial ℂ := ∑ i : Fin d, Polynomial.C (b i z) * Polynomial.X ^ (i : ℕ) with hRdef
  have hp0 : p ≠ 0 := (monicPoly_monic a z).ne_zero
  have hReval : ∀ w, R.eval w = ∑ j, b j z * w ^ (j : ℕ) := by
    intro w; simp [hRdef, Polynomial.eval_finsetSum]
  have hRzero : R = 0 := by
    by_contra hR
    have hle : p.roots ≤ R.roots := by
      rw [Multiset.le_iff_count]
      intro α
      by_cases hα : α ∈ p.roots
      · have hα' : monicInLast a (z, α) = 0 := by
          rw [← monicPoly_eval]; exact (Polynomial.mem_roots hp0).mp hα
        have hαρ := hroots α hα'
        rw [Polynomial.count_roots, Polynomial.count_roots]
        have h4p := spec_analyticOrderAt_polynomial_eval_aux hp0 α
        have h4R := spec_analyticOrderAt_polynomial_eval_aux hR α
        have hev : (fun w => R.eval w) =ᶠ[𝓝 α] fun w => (-q (z, w)) * p.eval w := by
          filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hαρ)] with w hw
          rw [mem_ball_zero_iff] at hw
          rw [hReval, monicPoly_eval]
          linear_combination hid w hw
        have hm := analyticOrderAt_mul (hq α hαρ).neg ((Polynomial.differentiable p).analyticAt α)
        rw [show ((-fun w => q (z, w)) * fun w => p.eval w) =
          fun w => -q (z, w) * p.eval w from rfl] at hm
        rw [analyticOrderAt_congr hev, hm, h4p] at h4R
        exact_mod_cast (le_add_self : (p.rootMultiplicity α : ℕ∞) ≤ _).trans h4R.le
      · rw [Multiset.count_eq_zero_of_notMem hα]; exact Nat.zero_le _
    have h1 := Multiset.card_le_card hle
    rw [IsAlgClosed.card_roots_eq_natDegree, monicPoly_natDegree] at h1
    have h2 := (Polynomial.card_roots' R).trans_lt
      ((Polynomial.natDegree_lt_iff_degree_lt hR).mpr (Polynomial.degree_sum_fin_lt _))
    omega
  have hb : ∀ j, b j z = 0 := by
    intro j
    rw [← coeff_sum_fin (fun i => b i z) j]
    change R.coeff j = 0
    rw [hRzero, Polynomial.coeff_zero]
  refine ⟨hb, fun w hw => ?_⟩
  have hev : ∀ᶠ w' in 𝓝 w, q (z, w') * p.eval w' = 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw)] with w' hw'
    rw [mem_ball_zero_iff] at hw'
    have := hid w' hw'
    rw [hpdef, monicPoly_eval]
    simpa [hb] using this
  have htop := analyticOrderAt_eq_top.mpr hev
  have hm := analyticOrderAt_mul (hq w hw) ((Polynomial.differentiable p).analyticAt w)
  rw [show ((fun w => q (z, w)) * fun w => p.eval w) =
    fun w => q (z, w) * p.eval w from rfl] at hm
  rw [hm, spec_analyticOrderAt_polynomial_eval_aux hp0 w, ENat.add_eq_top] at htop
  rcases htop with h | h
  · exact (analyticOrderAt_eq_top.mp h).self_of_nhds
  · exact absurd h (ENat.natCast_ne_top _)

theorem spec_weierstrass_division_unique_aux {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    (ha : ∀ j, ContinuousAt (a j) 0) (ha0 : ∀ j, a j 0 = 0) {q : (Fin n → ℂ) × ℂ → ℂ}
    (hq : AnalyticAt ℂ q 0) {b : Fin d → (Fin n → ℂ) → ℂ}
    (h : ∀ᶠ p in 𝓝 0, q p * monicInLast a p + ∑ j, b j p.1 * p.2 ^ (j : ℕ) = 0) :
    (∀ᶠ p in 𝓝 0, q p = 0) ∧ ∀ j, ∀ᶠ z in 𝓝 0, b j z = 0 := by
  obtain ⟨η, hη, hqη⟩ := hq.exists_ball_analyticOnNhd
  obtain ⟨κ, hκ, hκh⟩ := Metric.eventually_nhds_iff_ball.mp h
  set ρ := min η κ with hρ
  have hρ0 : 0 < ρ := lt_min hη hκ
  have hgood : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      (∀ j, b j z = 0) ∧ ∀ w, ‖w‖ < ρ → q (z, w) = 0 := by
    filter_upwards [spec_monicInLast_roots_small_aux ha ha0 hρ0,
      isOpen_ball.mem_nhds (mem_ball_self hρ0)] with z hz hzb
    rw [mem_ball_zero_iff] at hzb
    have hmem : ∀ w, ‖w‖ < ρ → ((z, w) : (Fin n → ℂ) × ℂ) ∈ ball 0 ρ := fun w hw => by
      rw [mem_ball_zero_iff, Prod.norm_mk]; exact max_lt hzb hw
    refine division_unique_fiber (fun w hw => ?_) (fun w hw => ?_) hz
    · have := hqη _ (ball_subset_ball (min_le_left _ _) (hmem w hw))
      exact this.comp_of_eq (AnalyticAt.prod analyticAt_const analyticAt_id) rfl
    · exact hκh _ (ball_subset_ball (min_le_right _ _) (hmem w hw))
  refine ⟨?_, fun j => hgood.mono fun z hz => hz.1 j⟩
  have h1 : ∀ᶠ p in 𝓝 (0 : (Fin n → ℂ) × ℂ), (∀ j, b j p.1 = 0) ∧
      ∀ w, ‖w‖ < ρ → q (p.1, w) = 0 :=
    (continuous_fst.tendsto ((0 : Fin n → ℂ), (0 : ℂ))).eventually hgood
  filter_upwards [h1, isOpen_ball.mem_nhds (mem_ball_self hρ0)] with p hp hpb
  rw [mem_ball_zero_iff, Prod.norm_def] at hpb
  exact hp.2 p.2 (lt_of_le_of_lt (le_max_right _ _) hpb)

end Preparation

end HodgeLean.Foundations.AnalyticDivisorAlgebraic4
