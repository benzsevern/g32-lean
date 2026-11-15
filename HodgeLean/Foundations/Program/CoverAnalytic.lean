import HodgeLean.Foundations.Program.CoverAnalyticProofs

/-! # Complex-analytic foundations for the cover dictionary, stage 1 (FROZEN SPEC)

Seven one-variable statements, prefix `caf_`, used by the route of `docs/notes/spec-caf-routes.md`
toward bodies for `b65g_dictionary_aux` and `b65g_cover_solutions_aux`. Each is general
complex analysis, stated with Mathlib's `MeromorphicAt`, `meromorphicOrderAt`, `AnalyticAt`
and `RatFunc` only; none mentions a cover, a Schlesinger system or a 5c record.

Claimed: a polynomial bound on a punctured disc gives a meromorphic function with the
corresponding order bound; a solution of a linear equation `f' = B f` with `‖B z‖ ≤ K/|z − z₀|`
on a punctured disc is meromorphic at `z₀` (regular singular growth, by Grönwall); the order of a
meromorphic solution of `(z − z₀) f' = (A₀ + (z − z₀) G) f` is an eigenvalue of `A₀` (indicial
equation); a holomorphic germ that transforms by the character `ζᵏ` under `y ↦ ζ y` is
`yᵏ g(yᵉ)`; a function holomorphic on a punctured disc is meromorphic once its pullback by
`y ↦ t + yᵉ` is; a function holomorphic off a finite set of `ℂ`, meromorphic at that set and at
`∞`, is rational there; and the order at `∞` of a nonzero rational function is minus its
`intDegree`.

Not claimed: any statement about a Riemann surface, a cover, the record `b65g_Solutions` or the
dictionary itself (later stages; see the note); existence of solutions of linear equations and
the non-resonant normal form at a regular singular point (not restated: `b65f_segment_solution`
and `b65f_local_normal_form`; later stages reuse these established results).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Polynomial growth gives a pole.** A function holomorphic on a punctured neighbourhood of
`z₀` with `‖f z‖ ≤ C / |z − z₀|ᴺ` there is meromorphic at `z₀`, of order at least `−N`.
Source: Ahlfors, *Complex Analysis*, 3rd ed., ch. 4, §3.1–3.2 (removable singularities;
poles), Riemann's theorem applied to `(z − z₀)ᴺ f`; Mathlib
`Complex.differentiableOn_update_limUnder_of_bddAbove`. -/
theorem caf_meromorphicAt_of_norm_le [FiniteDimensional ℂ E] (f : ℂ → E) (z₀ : ℂ) (N : ℕ)
    (C : ℝ) (hf : ∀ᶠ z in 𝓝[≠] z₀, AnalyticAt ℂ f z)
    (hb : ∀ᶠ z in 𝓝[≠] z₀, ‖f z‖ ≤ C / ‖z - z₀‖ ^ N) :
    MeromorphicAt f z₀ ∧ ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z₀ :=
  caf_meromorphicAt_of_norm_le_aux f z₀ N C hf hb


/-- The bound is attained by `1/z`: `‖z⁻¹‖ ≤ 1/|z|¹` near `0`, so the hypotheses of
`caf_meromorphicAt_of_norm_le` hold with `N = 1`, `C = 1`. -/
example : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z⁻¹‖ ≤ 1 / ‖z - 0‖ ^ 1 :=
  Eventually.of_forall fun z ↦ by simp

/-- **Regular singular growth.** If `f' = B f` on the punctured disc `0 < |z − z₀| < r`, with
`‖B z‖ ≤ K / |z − z₀|`, then `f` is meromorphic at `z₀`.
Source: Coddington–Levinson, *Theory of Ordinary Differential Equations*, ch. 4 (singularities
of the first kind: solutions grow at most like a power, by the Grönwall estimate
`‖f(z₀ + ρω)‖ ≤ ‖f(z₀ + ρ₀ω)‖ (ρ₀/ρ)ᴷ` along rays; Mathlib `norm_le_gronwallBound_of_norm_deriv_right_le`);
then `caf_meromorphicAt_of_norm_le`. -/
theorem caf_meromorphicAt_of_linear_ode [FiniteDimensional ℂ E] (f : ℂ → E)
    (B : ℂ → E →L[ℂ] E) (z₀ : ℂ) (r K : ℝ) (hr : 0 < r)
    (hode : ∀ z ∈ ball z₀ r \ {z₀}, HasDerivAt f (B z (f z)) z)
    (hB : ∀ z ∈ ball z₀ r \ {z₀}, ‖B z‖ ≤ K / ‖z - z₀‖) :
    MeromorphicAt f z₀ :=
  caf_meromorphicAt_of_linear_ode_aux f B z₀ r K hr hode hB


/-- **The indicial equation.** If `f` is meromorphic at `z₀` of finite order `m` and
`(z − z₀) f'(z) = A₀ f(z) + (z − z₀) G(z) f(z)` near `z₀`, with `G` continuous at `z₀`, then `m`
is an eigenvalue of `A₀`: writing `f = (z − z₀)ᵐ g` with `g(z₀) ≠ 0`, the equation at `z₀` reads
`m g(z₀) = A₀ g(z₀)`.
Source: Coddington–Levinson, ch. 4 (the indicial equation at a singularity of the first kind);
Mathlib `meromorphicOrderAt_eq_int_iff`. -/
theorem caf_order_eigenvalue [CompleteSpace E] (f : ℂ → E) (z₀ : ℂ) (A₀ : E →L[ℂ] E)
    (G : ℂ → E →L[ℂ] E) (m : ℤ) (hf : MeromorphicAt f z₀)
    (hm : meromorphicOrderAt f z₀ = (m : WithTop ℤ)) (hG : ContinuousAt G z₀)
    (hode : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) • deriv f z = A₀ (f z) + (z - z₀) • G z (f z)) :
    ∃ v : E, v ≠ 0 ∧ A₀ v = (m : ℂ) • v :=
  caf_order_eigenvalue_aux f z₀ A₀ G m hf hm hG hode


/-- The equation is satisfiable: `f z = z²` solves `z f' = 2 f` (`A₀ = 2`, `G = 0`), and `2` is
an eigenvalue of multiplication by `2`. -/
example : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (z - 0) • deriv (fun z : ℂ ↦ z ^ 2) z =
    (2 : ℂ →L[ℂ] ℂ) (z ^ 2) + (z - 0) • (0 : ℂ →L[ℂ] ℂ) (z ^ 2) :=
  Eventually.of_forall fun z ↦ by
    rw [show deriv (fun z : ℂ ↦ z ^ 2) z = 2 * z by simp]
    simp only [sub_zero, smul_eq_mul, ContinuousLinearMap.ofNat_apply, zero_apply, mul_zero,
      add_zero]
    ring

/-- **Characters of a rotation.** A holomorphic germ at `0` with `f(ζ y) = ζᵏ f(y)`, for `ζ` a
primitive `e`-th root of unity and `k < e`, is `yᵏ g(yᵉ)` with `g` holomorphic at `0`: only the
Taylor coefficients of index `≡ k (mod e)` survive.
Source: Forster, *Lectures on Riemann Surfaces*, §2, Theorem 2.1 (local form `z ↦ zᵏ` of a
holomorphic map); comparison of Taylor coefficients of `f(ζ y)` and `ζᵏ f(y)`, Mathlib
`HasFPowerSeriesAt.eq_formalMultilinearSeries`. -/
theorem caf_rotation_factor [FiniteDimensional ℂ E] (f : ℂ → E) (e k : ℕ) (hk : k < e)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ e) (hf : AnalyticAt ℂ f 0)
    (hrot : ∀ᶠ y in 𝓝 (0 : ℂ), f (ζ * y) = ζ ^ k • f y) :
    ∃ g : ℂ → E, AnalyticAt ℂ g 0 ∧ ∀ᶠ y in 𝓝 (0 : ℂ), f y = y ^ k • g (y ^ e) :=
  caf_rotation_factor_aux f e k hk ζ hζ hf hrot


/-- The rotation hypothesis is satisfiable with `k ≠ 0`: `y ↦ y³` and `ζ = −1`, `e = 2`,
`k = 1`. -/
example : ∀ᶠ y in 𝓝 (0 : ℂ), (-1 * y) ^ 3 = (-1 : ℂ) ^ 1 • y ^ 3 :=
  Eventually.of_forall fun y ↦ by simp only [pow_one, smul_eq_mul]; ring

/-- **Descent along `y ↦ t + yᵉ`.** A function holomorphic on a punctured neighbourhood of `t`
whose pullback by `y ↦ t + yᵉ` (`e ≥ 1`) is meromorphic at `0` is meromorphic at `t`. (The order
is then given by Mathlib `MeromorphicAt.meromorphicOrderAt_comp`.)
Source: Forster, §2, Theorem 2.1 (local form of a holomorphic map); the bound
`‖F(s)‖ ≤ C |s − t|^(−N/e)` from the pullback and `caf_meromorphicAt_of_norm_le`. -/
theorem caf_meromorphicAt_of_comp_pow [FiniteDimensional ℂ E] (F : ℂ → E) (t : ℂ) (e : ℕ)
    (he : 0 < e) (hF : ∀ᶠ s in 𝓝[≠] t, AnalyticAt ℂ F s)
    (hm : MeromorphicAt (fun y : ℂ ↦ F (t + y ^ e)) 0) :
    MeromorphicAt F t :=
  caf_meromorphicAt_of_comp_pow_aux F t e he hF hm


/-- **Meromorphic functions on the Riemann sphere are rational.** A function holomorphic on `ℂ`
off a finite set `S`, meromorphic at the points of `S` and at `∞` (that is, `w ↦ f(1/w)` is
meromorphic at `0`), agrees off `S` with the evaluation of a rational function.
Source: Ahlfors, ch. 4, §3.2 (a function meromorphic in the extended plane is rational);
Forster, §2 (meromorphic functions on `ℙ¹`): multiply by `∏ (z − s)^{N_s}` and apply Liouville
with polynomial growth (Cauchy estimates, Mathlib
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`). -/
theorem caf_ratFunc_of_meromorphic (f : ℂ → ℂ) (S : Finset ℂ)
    (hf : ∀ z ∉ S, AnalyticAt ℂ f z) (hS : ∀ z ∈ S, MeromorphicAt f z)
    (hinf : MeromorphicAt (fun w : ℂ ↦ f w⁻¹) 0) :
    ∃ r : RatFunc ℂ, ∀ z ∉ S, f z = r.eval (RingHom.id ℂ) z :=
  caf_ratFunc_of_meromorphic_aux f S hf hS hinf


/-- The hypotheses hold for `z ↦ z` with `S = ∅`, and `RatFunc.X` represents it. -/
example : ∀ z : ℂ, z = (RatFunc.X : RatFunc ℂ).eval (RingHom.id ℂ) z := fun z ↦ by
  simp [RatFunc.eval_X]

/-- **The order at infinity of a rational function.** For `r ≠ 0`, `w ↦ r(1/w)` is meromorphic
at `0` of order `−intDegree r = deg denom − deg num`; so `ord_∞ r ≥ 2` in the sense of
`b65q_rSpace` (`intDegree ≤ −2`) is the analytic condition `ord_0 r(1/w) ≥ 2`.
Source: Ahlfors, ch. 4, §3.2 (the order of a rational function at `∞`); Mathlib
`RatFunc.intDegree`, `RatFunc.eval`. -/
theorem caf_meromorphicOrderAt_inv (r : RatFunc ℂ) (hr : r ≠ 0) :
    MeromorphicAt (fun w : ℂ ↦ r.eval (RingHom.id ℂ) w⁻¹) 0 ∧
      meromorphicOrderAt (fun w : ℂ ↦ r.eval (RingHom.id ℂ) w⁻¹) 0 =
        ((-r.intDegree : ℤ) : WithTop ℤ) :=
  caf_meromorphicOrderAt_inv_aux r hr


/-- Consistency of the sign: `RatFunc.X` has `intDegree 1`, so the predicted order of `1/w` at `0`
is `−1`. -/
example : (-(RatFunc.X : RatFunc ℂ).intDegree : ℤ) = -1 := by
  rw [RatFunc.intDegree_X]


/-- Statement 1: all premises for the inverse function. -/
example : (∀ᶠ z in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ (fun z : ℂ ↦ z⁻¹) z) ∧
    (∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z⁻¹‖ ≤ 1 / ‖z - 0‖ ^ 1) := by
  refine ⟨?_, Eventually.of_forall fun z ↦ by simp⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact analyticAt_id.inv (by simpa using hz)

/-- Statement 2: all premises for a quadratic solution. -/
example : (0 : ℝ) < 1 ∧
    (∀ z ∈ ball (0 : ℂ) 1 \ {0}, HasDerivAt (fun z : ℂ ↦ z ^ 2)
      (((2 / z) • (1 : ℂ →L[ℂ] ℂ)) (z ^ 2)) z) ∧
    (∀ z ∈ ball (0 : ℂ) 1 \ {0}, ‖(2 / z) • (1 : ℂ →L[ℂ] ℂ)‖ ≤ 2 / ‖z - 0‖) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro z hz
    have hn : z ≠ 0 := by simpa using hz.2
    have heq : (((2 / z) • (1 : ℂ →L[ℂ] ℂ)) (z ^ 2)) = 2 * z := by
      simp only [smul_apply, one_apply_eq_self, smul_eq_mul]
      field_simp
    rw [heq]
    simpa using! (hasDerivAt_id z).fun_pow 2
  · intro z hz
    simp [norm_smul]

/-- Statement 3: all premises for the indicial equation of a quadratic. -/
example : MeromorphicAt (fun z : ℂ ↦ z ^ 2) 0 ∧
    meromorphicOrderAt (fun z : ℂ ↦ z ^ 2) 0 = ((2 : ℤ) : WithTop ℤ) ∧
    ContinuousAt (fun _ : ℂ ↦ (0 : ℂ →L[ℂ] ℂ)) 0 ∧
    (∀ᶠ z in 𝓝[≠] (0 : ℂ), (z - 0) • deriv (fun z : ℂ ↦ z ^ 2) z =
      (2 : ℂ →L[ℂ] ℂ) (z ^ 2) + (z - 0) • (0 : ℂ →L[ℂ] ℂ) (z ^ 2)) := by
  refine ⟨(analyticAt_id.pow 2).meromorphicAt, ?_, continuousAt_const, ?_⟩
  · simpa using! (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (n := 2) (x := 0))
  · exact Eventually.of_forall fun z ↦ by simp [smul_eq_mul]; ring

/-- Statement 4: all premises for the odd cubic character. -/
example : 1 < (2 : ℕ) ∧ IsPrimitiveRoot (-1 : ℂ) 2 ∧
    AnalyticAt ℂ (fun y : ℂ ↦ y ^ 3) 0 ∧
    (∀ᶠ y in 𝓝 (0 : ℂ), (-1 * y) ^ 3 = (-1 : ℂ) ^ 1 • y ^ 3) := by
  refine ⟨by norm_num, ?_, analyticAt_id.pow 3, Eventually.of_forall fun y ↦ ?_⟩
  · exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  · simp only [pow_one, smul_eq_mul]; ring

/-- Statement 5: all premises for the inverse function under a quadratic pullback. -/
example : 0 < (2 : ℕ) ∧
    (∀ᶠ s in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ (fun s : ℂ ↦ s⁻¹) s) ∧
    MeromorphicAt (fun y : ℂ ↦ ((0 : ℂ) + y ^ 2)⁻¹) 0 := by
  refine ⟨by norm_num, ?_, ((analyticAt_const.add (analyticAt_id.pow 2)).meromorphicAt.inv)⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact analyticAt_id.inv (by simpa using hs)

/-- Statement 6: all premises for the identity with an empty exceptional set. -/
example : (∀ z ∉ (∅ : Finset ℂ), AnalyticAt ℂ (fun z : ℂ ↦ z) z) ∧
    (∀ z ∈ (∅ : Finset ℂ), MeromorphicAt (fun z : ℂ ↦ z) z) ∧
    MeromorphicAt (fun w : ℂ ↦ w⁻¹) 0 := by
  exact ⟨fun _ _ ↦ analyticAt_id, by simp, analyticAt_id.meromorphicAt.inv⟩

/-- Statement 7: the nonzero premise for the polynomial variable. -/
example : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero

end HodgeLean.Foundations.Program
