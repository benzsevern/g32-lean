import HodgeLean.Foundations.DivisorClassHodgeDefs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5
import HodgeLean.Foundations.AnalyticDivisorAlgebraic11
import HodgeLean.Foundations.AnalyticDivisorAlgebraic6
import Mathlib.RingTheory.Radical.Basic
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-! # Germs and factors of automorphy: helper lemmas (DC1-e)

Helpers for the DC1 statements on reduced equations and their factors: the factorial germ ring at
any point, squarefree reduction by the radical, translation of squarefree germs, and the
holomorphic logarithm of a nowhere-vanishing entire function on `ℂⁿ` (a continuous lift through
the covering `exp`, holomorphic by a local branch of `log`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11

namespace HodgeLean.Foundations

variable {n : ℕ}

/-- The germ ring at any point of `ℂⁿ` is factorial, transported from the origin.
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, II.B, Theorem 6. -/
theorem dcf_ufd (n : ℕ) (p : Fin n → ℂ) : UniqueFactorizationMonoid (AnalyticGermAt n p) := by
  obtain ⟨e, -, -⟩ := spec_germ_translation_equiv n p
  exact e.symm.toMulEquiv.uniqueFactorizationMonoid
    (AnalyticDivisorAlgebraic6.spec_analyticGerm_ufd n)

/-- An element of the germ ring at `p` is the germ of an analytic representative. -/
theorem dcf_germ_rep (p : Fin n → ℂ) (G : AnalyticGermAt n p) :
    ∃ (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p), G = ⟨Filter.Germ.ofFun g, g, hg, rfl⟩ := by
  obtain ⟨g, hg, hgG⟩ := G.2
  exact ⟨g, hg, Subtype.ext hgG.symm⟩

/-- A germ equation `G = A * B` holds pointwise near `p` for representatives. -/
theorem dcf_eventually_mul (p : Fin n → ℂ) (g a b : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p)
    (ha : AnalyticAt ℂ a p) (hb : AnalyticAt ℂ b p)
    (h : (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) =
      ⟨Filter.Germ.ofFun a, a, ha, rfl⟩ * ⟨Filter.Germ.ofFun b, b, hb, rfl⟩) :
    ∀ᶠ z in 𝓝 p, g z = a z * b z := by
  have := congrArg Subtype.val h
  exact Filter.Germ.coe_eq.mp this

/-- A germ that is not zero has a squarefree germ with the same zero germ: the radical.
Source: Gunning–Rossi, II.B, Theorem 6 (factoriality) and III.A (zero sets of factors). -/
theorem dcf_squarefree_reduction (p : Fin n → ℂ) (g : (Fin n → ℂ) → ℂ)
    (hg : AnalyticAt ℂ g p) (hne : ¬ ∀ᶠ z in 𝓝 p, g z = 0) :
    ∃ (g' : (Fin n → ℂ) → ℂ) (hg' : AnalyticAt ℂ g' p),
      Squarefree (⟨Filter.Germ.ofFun g', g', hg', rfl⟩ : AnalyticGermAt n p) ∧
        ∀ᶠ z in 𝓝 p, (g' z = 0 ↔ g z = 0) := by
  classical
  have := dcf_ufd n p
  let _ : StrongNormalizationMonoid (AnalyticGermAt n p) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  set G : AnalyticGermAt n p := ⟨Filter.Germ.ofFun g, g, hg, rfl⟩ with hGdef
  have hG : G ≠ 0 := by
    intro h
    apply hne
    have h0 : (0 : AnalyticGermAt n p) = ⟨Filter.Germ.ofFun (fun _ ↦ (0 : ℂ)), fun _ ↦ 0,
        analyticAt_const, rfl⟩ := rfl
    rw [h0] at h
    exact Filter.Germ.coe_eq.mp (congrArg Subtype.val h)
  obtain ⟨r, hr, hR⟩ := dcf_germ_rep p (UniqueFactorizationMonoid.radical G)
  refine ⟨r, hr, hR ▸ UniqueFactorizationMonoid.squarefree_radical, ?_⟩
  obtain ⟨C, hC⟩ := UniqueFactorizationMonoid.radical_dvd_self (a := G)
  obtain ⟨c, hc, rfl⟩ := dcf_germ_rep p C
  obtain ⟨k, D, hD⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow hG
  obtain ⟨d, hd, rfl⟩ := dcf_germ_rep p D
  rw [hR] at hC hD
  have h1 := dcf_eventually_mul p g r c hg hr hc hC
  have hpow : (⟨Filter.Germ.ofFun r, r, hr, rfl⟩ : AnalyticGermAt n p) ^ k =
      ⟨Filter.Germ.ofFun (fun z ↦ r z ^ k), fun z ↦ r z ^ k, hr.pow k, rfl⟩ := by
    apply Subtype.ext
    rfl
  rw [hpow] at hD
  have h2 := dcf_eventually_mul p (fun z ↦ r z ^ k) g d (hr.pow k) hg hd hD
  filter_upwards [h1, h2] with z hz1 hz2
  constructor
  · intro hrz
    rw [hz1, hrz, zero_mul]
  · intro hgz
    have : r z ^ k = 0 := by rw [hz2, hgz, zero_mul]
    exact eq_zero_of_pow_eq_zero this

/-- Squarefreeness is preserved by multiplicative equivalences. -/
theorem dcf_squarefree_map {R S : Type*} [Monoid R] [Monoid S] (e : R ≃* S) (x : R)
    (hx : Squarefree x) : Squarefree (e x) := by
  intro y hy
  have h : e.symm y * e.symm y ∣ x := by
    have := map_dvd e.symm hy
    rwa [map_mul, MulEquiv.symm_apply_apply] at this
  have hu := hx _ h
  simpa using hu.map e

/-- Translating an entire function moves its germ at `p + v` to the germ of the translate at `p`,
so squarefreeness is preserved.
Source: Gunning–Rossi, II.B, Definition 1 (translation of germs). -/
theorem dcf_squarefree_translate (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (v p : Fin n → ℂ) (hfv : AnalyticAt ℂ (fun z ↦ f (z + v)) p)
    (hsq : Squarefree (⟨Filter.Germ.ofFun f, f, hf (p + v) (mem_univ _), rfl⟩ :
      AnalyticGermAt n (p + v))) :
    Squarefree (⟨Filter.Germ.ofFun (fun z ↦ f (z + v)), fun z ↦ f (z + v), hfv, rfl⟩ :
      AnalyticGermAt n p) := by
  obtain ⟨e₁, -, he₁⟩ := spec_germ_translation_equiv n (p + v)
  obtain ⟨e₂, -, he₂⟩ := spec_germ_translation_equiv n p
  have ht : AnalyticAt ℂ (fun z ↦ f (p + v + z)) 0 :=
    (hf _ (mem_univ _)).comp_of_eq
      ((analyticAt_const (v := p + v)).add analyticAt_id) (add_zero _)
  have ht' : AnalyticAt ℂ (fun z ↦ (fun z ↦ f (z + v)) (p + z)) 0 := by
    have : (fun z ↦ (fun z ↦ f (z + v)) (p + z)) = fun z ↦ f (p + v + z) := by
      funext z; simp only; congr 1; abel
    rw [this]; exact ht
  have h₁ := he₁ f (hf _ (mem_univ _)) ht
  have h₂ := he₂ (fun z ↦ f (z + v)) hfv ht'
  have heq : e₂ ⟨Filter.Germ.ofFun (fun z ↦ f (z + v)), fun z ↦ f (z + v), hfv, rfl⟩ =
      e₁ ⟨Filter.Germ.ofFun f, f, hf (p + v) (mem_univ _), rfl⟩ := by
    rw [h₁, h₂]
    apply Subtype.ext
    change (Filter.Germ.ofFun _ : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = Filter.Germ.ofFun _
    congr 1
    funext z; congr 1; abel
  have := dcf_squarefree_map e₁.toMulEquiv _ hsq
  have h3 := dcf_squarefree_map e₂.symm.toMulEquiv _ (heq ▸ this : Squarefree (e₂ _))
  convert h3 using 1
  exact (e₂.symm_apply_apply _).symm

/-- A squarefree germ is not zero, so the points where a representative does not vanish
accumulate at the base point. -/
theorem dcf_neBot_of_squarefree (p : Fin n → ℂ) (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
    (hsq : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p)) :
    (𝓝[{w | f w ≠ 0}] p).NeBot := by
  have hne := hsq.ne_zero
  apply mem_closure_iff_nhdsWithin_neBot.mp
  apply mem_closure_iff_frequently.mpr
  intro hev
  apply hne
  apply Subtype.ext
  change (Filter.Germ.ofFun f : Filter.Germ (𝓝 p) ℂ) = Filter.Germ.ofFun (fun _ ↦ (0 : ℂ))
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hev] with w hw
  simpa using hw

/-- Where `f (· + l)` is `u * f` near `z`, with `u` analytic at `z`, the factor `dc1_factor f L l`
agrees with `u` near `z`. -/
theorem dcf_factor_eventuallyEq (f : (Fin n → ℂ) → ℂ) (L : Submodule ℤ (Fin n → ℂ)) (l : L)
    (hne : ∀ w, (𝓝[{w | f w ≠ 0}] w).NeBot) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : AnalyticAt ℂ u z) (heq : (fun w ↦ f (w + l)) =ᶠ[𝓝 z] fun w ↦ u w * f w) :
    dc1_factor f L l =ᶠ[𝓝 z] u := by
  filter_upwards [hu.eventually_analyticAt, heq.eventually_nhds] with w hw hweq
  haveI := hne w
  apply Tendsto.limUnder_eq
  have h1 : Tendsto u (𝓝[{w | f w ≠ 0}] w) (𝓝 (u w)) :=
    hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply h1.congr'
  filter_upwards [nhdsWithin_le_nhds hweq, self_mem_nhdsWithin] with y hy hy0
  rw [hy, mul_div_cancel_right₀ _ hy0]

/-- A nowhere-vanishing entire function on `ℂⁿ` has an entire logarithm: a continuous lift through
the covering `exp : ℂ → ℂ \ {0}` (`ℂⁿ` is simply connected), holomorphic because near each point
it differs from a branch of `log` by a constant.
Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §3.4; Hatcher, *Algebraic Topology*,
Proposition 1.33 (lifting criterion). -/
theorem dcf_exists_log (g : (Fin n → ℂ) → ℂ) (hg : Differentiable ℂ g) (hg0 : ∀ z, g z ≠ 0) :
    ∃ h : (Fin n → ℂ) → ℂ, Differentiable ℂ h ∧ ∀ z, Complex.exp (h z) = g z := by
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨g, hg.continuous⟩ : C(Fin n → ℂ, ℂ)) (a₀ := 0) (e₀ := Complex.log (g 0))
    (Complex.exp_log (hg0 0)) (fun a ↦ hg0 a)
  have hFg : ∀ z, Complex.exp (F z) = g z := fun z ↦ congrFun hF z
  refine ⟨F, fun z ↦ ?_, hFg⟩
  have hcont : ContinuousAt (fun w ↦ F w - F z) z :=
    (F.continuous.sub continuous_const).continuousAt
  have hev : ∀ᶠ w in 𝓝 z, F w - F z ∈ Metric.ball (0 : ℂ) 1 :=
    hcont.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hloc : ∀ᶠ w in 𝓝 z, F w = F z + Complex.log (g w / g z) := by
    filter_upwards [hev] with w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have him : |(F w - F z).im| < 1 := (Complex.abs_im_le_norm _).trans_lt hw
    have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    have hlog : Complex.log (g w / g z) = F w - F z := by
      rw [← hFg w, ← hFg z, ← Complex.exp_sub, Complex.log_exp]
      · linarith [(abs_lt.mp him).1]
      · linarith [(abs_lt.mp him).2]
    rw [hlog]; ring
  have hd : DifferentiableAt ℂ (fun w ↦ F z + Complex.log (g w / g z)) z := by
    apply DifferentiableAt.const_add
    have h1 : DifferentiableAt ℂ (fun y ↦ g y / g z) z := by
      simp_rw [div_eq_mul_inv]; exact (hg z).mul_const _
    exact h1.clog (by rw [div_self (hg0 z)]; exact Complex.one_mem_slitPlane)
  exact hd.congr_of_eventuallyEq hloc

/-- The integral of the logarithmic derivative along the segment from `0` to `z` is the increment
of an entire logarithm.
Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §3.4; the fundamental theorem of calculus. -/
theorem dcf_integral_logDeriv (g h : (Fin n → ℂ) → ℂ) (hh : Differentiable ℂ h)
    (hgh : ∀ z, Complex.exp (h z) = g z) (z : Fin n → ℂ) :
    ∫ t in (0 : ℝ)..1, deriv (fun s : ℝ ↦ g (s • z)) t / g (t • z) = h z - h 0 := by
  obtain ⟨H, hHdef⟩ : ∃ H : ℂ → ℂ, H = fun c ↦ h (c • z) := ⟨_, rfl⟩
  have hHc : ∀ c, H c = h (c • z) := fun c ↦ by rw [hHdef]
  have hH : Differentiable ℂ H := hHdef ▸ hh.comp (differentiable_id.smul_const z)
  have hsmul : ∀ s : ℝ, s • z = (s : ℂ) • z := fun s ↦ (Complex.coe_smul s z).symm
  have hderH : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ H s) (deriv H t) t :=
    fun t ↦ (hH t).hasDerivAt.comp_ofReal
  have hfun : (fun s : ℝ ↦ g (s • z)) = fun s : ℝ ↦ Complex.exp (H s) := by
    funext s; rw [hHc, ← hsmul, hgh]
  have hint : ∀ t : ℝ, deriv (fun s : ℝ ↦ g (s • z)) t / g (t • z) = deriv H t := by
    intro t
    have ht : g (t • z) = Complex.exp (H t) := congrFun hfun t
    rw [hfun, (hderH t).cexp.deriv, ht]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  simp_rw [hint]
  have hcd : Continuous (deriv H) := (contDiff_one_iff_deriv.mp (hH.contDiff (n := 1))).2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderH t)
    ((hcd.comp Complex.continuous_ofReal).intervalIntegrable 0 1)]
  simp [hHc]

end HodgeLean.Foundations
