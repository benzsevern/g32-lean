import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsLasso

/-! # Loops in punctured discs about the apparent poles and about infinity

Transport is translation invariant for a periodic coefficient and depends only on endpoints in a
convex set; lifting through `w ↦ p + exp w` shows that every loop in a punctured disc about `p`
has trivial transport once one circle has. At `3`, `1`, `−2` the circle transport is conjugate
to `x⁴ = 1` or `y³ = 1`; near infinity `b65r_phi` maps a large circle into a disc about `1`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Bornology
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65t_iterated_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {B : ℂ → E →L[ℂ] E} {c : ℂ} (hB : ∀ z, B (z + c) = B z) (u v : ℂ) :
    ∀ m t, b65f_iterated E B (u + c) (v + c) m t = b65f_iterated E B u v m t := by
  intro m
  induction m with
  | zero => intro t; rfl
  | succ m ih =>
    intro t
    simp only [b65f_iterated]
    congr 1
    funext q
    rw [show v + c - (u + c) = v - u by ring,
      show u + c + (q : ℂ) * (v - u) = (u + q * (v - u)) + c by ring, hB, ih]

/-- Transport is invariant under a translation that preserves the coefficient. -/
theorem b65t_transport_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {B : ℂ → E →L[ℂ] E} {c : ℂ} (hB : ∀ z, B (z + c) = B z) (γ : ℝ → ℂ) :
    b65f_transport E B (fun t ↦ γ t + c) = b65f_transport E B γ := by
  apply b65t_transport_eq_of_segments
  refine ⟨0, fun n _ i _ ↦ ?_⟩
  unfold b65f_segment
  congr 1
  funext m
  exact b65t_iterated_translate hB _ _ m 1


/-- Straight path between two points of a convex set. -/
def b65t_segPath {W : Set ℂ} (hW : Convex ℝ W) (a b : W) : Path a b where
  toFun t := ⟨a + (t : ℝ) • ((b : ℂ) - a), hW.add_smul_sub_mem a.2 b.2 ⟨t.2.1, t.2.2⟩⟩
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by ext; simp

/-- In a convex open set, transport along a path depends only on its endpoints, and is
multiplicative and trivial on constant paths. -/
theorem b65t_convex_transport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : ℂ → E →L[ℂ] E} {W : Set ℂ} (hWo : IsOpen W)
    (hW : Convex ℝ W) (hB : AnalyticOnNhd ℂ B W) {a b : W} (γ δ : Path a b) :
    b65f_transport E B (fun t ↦ (γ.extend t).val) =
      b65f_transport E B (fun t ↦ (δ.extend t).val) := by
  have : ContractibleSpace W := hW.contractibleSpace ⟨a, a.2⟩
  exact b65f_homotopy_invariance E W hWo B hB a b γ δ (SimplyConnectedSpace.paths_homotopic γ δ)

theorem b65t_symm_transport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : ℂ → E →L[ℂ] E} {W : Set ℂ} (hWo : IsOpen W)
    (hB : AnalyticOnNhd ℂ B W) {a b : W} (γ : Path a b) :
    b65f_transport E B (fun t ↦ (γ.symm.extend t).val) *
      b65f_transport E B (fun t ↦ (γ.extend t).val) = 1 := by
  rw [← b65f_path_composition E W hWo B hB a b a γ γ.symm,
    ← b65f_homotopy_invariance E W hWo B hB a a _ _ ⟨Path.Homotopy.reflTransSymm γ⟩]
  exact b65t_transport_refl B a


/-- On a convex open set stable under translation by `c`, with a `c`-periodic coefficient, if one
path from `w₁` to `w₁ + c` has trivial transport, then every path from `a` to `a + n c` does. -/
theorem b65t_periodic_transport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : ℂ → E →L[ℂ] E} {W : Set ℂ} (hWo : IsOpen W)
    (hW : Convex ℝ W) (hB : AnalyticOnNhd ℂ B W) (c : ℂ) (hper : ∀ z, B (z + c) = B z)
    (hsh : ∀ w ∈ W, ∀ n : ℤ, w + n * c ∈ W) (w₁ : W)
    (h₁ : b65f_transport E B
      (fun t ↦ ((b65t_segPath hW w₁ ⟨w₁ + (1 : ℤ) * c, hsh _ w₁.2 1⟩).extend t).val) = 1)
    (a : W) (n : ℤ) (γ : Path a ⟨a + n * c, hsh _ a.2 n⟩) :
    b65f_transport E B (fun t ↦ (γ.extend t).val) = 1 := by
  let T : ∀ {u v : W}, Path u v → E →L[ℂ] E :=
    fun γ ↦ b65f_transport E B (fun t ↦ (γ.extend t).val)
  have hconv : ∀ {u v : W} (γ δ : Path u v), T γ = T δ := fun γ δ ↦
    b65t_convex_transport hWo hW hB γ δ
  have hcomp : ∀ {u v w : W} (γ : Path u v) (δ : Path v w), T (γ.trans δ) = T δ * T γ :=
    fun γ δ ↦ b65f_path_composition E W hWo B hB _ _ _ γ δ
  let sh : W → ℤ → W := fun u m ↦ ⟨u + m * c, hsh _ u.2 m⟩
  -- one step from any base point
  have hstep : ∀ (u : W) (γ : Path u (sh u 1)), T γ = 1 := by
    intro u γ
    have htr : T (b65t_segPath hW (sh w₁ 1) (sh u 1)) = T (b65t_segPath hW w₁ u) := by
      have : (fun t ↦ ((b65t_segPath hW (sh w₁ 1) (sh u 1)).extend t).val) =
          fun t ↦ ((b65t_segPath hW w₁ u).extend t).val + (1 : ℤ) * c := by
        funext t
        simp only [Path.extend, b65t_segPath, sh, IccExtend, Path.coe_mk', ContinuousMap.coe_mk,
          Function.comp_apply]
        push_cast
        module
      change b65f_transport E B _ = b65f_transport E B _
      rw [this]
      exact b65t_transport_translate (fun z ↦ by rw [Int.cast_one, one_mul]; exact hper z) _
    have hback : T (b65t_segPath hW w₁ u) * T (b65t_segPath hW u w₁) = 1 := by
      rw [← hcomp, hconv _ (Path.refl u)]
      exact b65t_transport_refl B u
    calc T γ = T ((b65t_segPath hW u w₁).trans ((b65t_segPath hW w₁ (sh w₁ 1)).trans
          (b65t_segPath hW (sh w₁ 1) (sh u 1)))) := hconv _ _
      _ = T (b65t_segPath hW w₁ u) * T (b65t_segPath hW w₁ (sh w₁ 1)) *
          T (b65t_segPath hW u w₁) := by rw [hcomp, hcomp, htr, mul_assoc]
      _ = 1 := by
          rw [show T (b65t_segPath hW w₁ (sh w₁ 1)) = 1 from h₁, mul_one, hback]
  -- natural multiples
  have hnat : ∀ (u : W) (m : ℕ) (γ : Path u (sh u m)), T γ = 1 := by
    intro u m
    induction m with
    | zero =>
        intro γ
        have he : sh u ((0 : ℕ) : ℤ) = u := by ext; simp [sh]
        rw [hconv γ ((Path.refl u).cast rfl he)]
        exact b65t_transport_refl B u
    | succ m ih =>
        intro γ
        have he : sh (sh u m) 1 = sh u ((m + 1 : ℕ) : ℤ) := by ext; simp [sh]; ring
        let δ : Path (sh u m) (sh u ((m + 1 : ℕ) : ℤ)) :=
          (b65t_segPath hW (sh u m) (sh (sh u m) 1)).cast rfl he.symm
        rw [hconv γ ((b65t_segPath hW u (sh u m)).trans δ), hcomp, ih, mul_one]
        exact hstep (sh u m) (b65t_segPath hW (sh u m) (sh (sh u m) 1))
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact hnat a m γ
  · -- the reverse of a path from `a - m c` to `a`
    have he : sh (sh a (-(m : ℤ))) m = a := by ext; simp [sh]
    let δ : Path (sh a (-(m : ℤ))) (sh (sh a (-(m : ℤ))) m) :=
      (b65t_segPath hW (sh a (-(m : ℤ))) a).cast rfl he
    have h1 : T δ = 1 := hnat _ m δ
    have h2 := b65t_symm_transport hWo hB δ
    rw [show b65f_transport E B (fun t ↦ (δ.extend t).val) = 1 from h1, mul_one] at h2
    exact (hconv γ (δ.symm.cast he.symm rfl)).trans h2


/-- Loops in a region `{z ≠ p, log ‖z - p‖ ∈ J}` of the regular domain have trivial transport once
one circle about `p` in the region has. The loop is lifted through `w ↦ p + exp w` to the strip
`{w.re ∈ J}`, where the pulled-back coefficient is `2πi`-periodic. -/
theorem b65t_annulus_loop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {A : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U)
    (hA : AnalyticOnNhd ℂ A U) (p : ℂ) {J : Set ℝ} (hJo : IsOpen J) (hJc : Convex ℝ J)
    (hΩ : ∀ w : ℂ, w.re ∈ J → p + Complex.exp w ∈ U) (w₁ : ℂ) (hw₁ : w₁.re ∈ J)
    (h₁ : b65f_transport E A
      (fun t : ℝ ↦ p + Complex.exp (w₁ + (t : ℂ) * (2 * Real.pi * Complex.I))) = 1)
    (q : U) (γ : Path q q)
    (hγ : ∀ t, (γ t : ℂ) ≠ p ∧ Real.log ‖(γ t : ℂ) - p‖ ∈ J) :
    b65f_transport E A (fun t ↦ (γ.extend t).val) = 1 := by
  set c : ℂ := 2 * Real.pi * Complex.I with hc
  let W : Set ℂ := {w | w.re ∈ J}
  have hWo : IsOpen W := hJo.preimage Complex.continuous_re
  have hW : Convex ℝ W := by
    intro x hx y hy a b ha hb hab
    change (a • x + b • y).re ∈ J
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact hJc hx hy ha hb hab
  have hcre : ∀ n : ℤ, ((n : ℂ) * c).re = 0 := by
    intro n; simp [hc]
  have hsh : ∀ w ∈ W, ∀ n : ℤ, w + n * c ∈ W := by
    intro w hw n
    change (w + n * c).re ∈ J
    rw [Complex.add_re, hcre, add_zero]; exact hw
  let π : ℂ → ℂ := fun w ↦ p + Complex.exp w
  have hπ : AnalyticOnNhd ℂ π W := fun w _ ↦ analyticAt_const.add analyticAt_cexp
  have hmaps : MapsTo π W U := fun w hw ↦ hΩ w hw
  have hderiv : ∀ z, deriv π z = Complex.exp z := fun z ↦
    ((Complex.hasDerivAt_exp z).const_add p).deriv
  let P := b65t_pull E π A
  have hP : AnalyticOnNhd ℂ P W := by
    intro z hz
    exact (hπ.deriv z hz).smul ((hA (π z) (hmaps hz)).comp (hπ z hz))
  have hper : ∀ z, P (z + c) = P z := by
    intro z
    have he : Complex.exp (z + c) = Complex.exp z := Complex.exp_periodic z
    simp only [P, b65t_pull, hderiv, π, he]
  -- the circle in the strip
  let w₁' : W := ⟨w₁, hw₁⟩
  have h₁' : b65f_transport E P
      (fun t ↦ ((b65t_segPath hW w₁' ⟨w₁ + (1 : ℤ) * c, hsh _ hw₁ 1⟩).extend t).val) = 1 := by
    rw [b65t_transport_pullback_proof E U W hU hWo A hA π hπ hmaps _ _ _]
    rw [← h₁]
    apply b65t_transport_congr_Icc
    intro t ht
    simp only [Path.extend_apply _ ht, b65t_segPath, Path.coe_mk', ContinuousMap.coe_mk, π]
    congr 2
    push_cast
    simp [hc]
    ring
  -- the lift of the loop
  let γ₀ : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t ↦ ⟨(γ t : ℂ) - p, sub_ne_zero.mpr (hγ t).1⟩, by fun_prop⟩
  have hq : (q : ℂ) - p ≠ 0 := by
    have := (hγ 0).1; rw [γ.source] at this; exact sub_ne_zero.mpr this
  have h0 : γ₀ 0 = (⟨Complex.exp (Complex.log ((q : ℂ) - p)), Complex.exp_ne_zero _⟩ :
      {z : ℂ // z ≠ 0}) := by
    apply Subtype.ext
    simp [γ₀, Complex.exp_log hq]
  let Γ := Complex.isCoveringMap_exp.liftPath γ₀ (Complex.log ((q : ℂ) - p)) h0
  have hΓ : ∀ t, Complex.exp (Γ t) = (γ t : ℂ) - p := by
    intro t
    have := congrArg Subtype.val (congrFun (Complex.isCoveringMap_exp.liftPath_lifts γ₀ _ h0) t)
    exact this
  have hΓW : ∀ t, Γ t ∈ W := by
    intro t
    change (Γ t).re ∈ J
    have := (hγ t).2
    rwa [← hΓ t, Complex.norm_exp, Real.log_exp] at this
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Γ 1 = Γ 0 + n * c := by
    have e1 : Complex.exp (Γ 1) = Complex.exp (Γ 0) := by rw [hΓ, hΓ, γ.source, γ.target]
    exact Complex.exp_eq_exp_iff_exists_int.mp e1
  let a : W := ⟨Γ 0, hΓW 0⟩
  let Γp : Path a ⟨a + n * c, hsh _ a.2 n⟩ :=
    { toFun := fun t ↦ ⟨Γ t, hΓW t⟩
      continuous_toFun := by fun_prop
      source' := rfl
      target' := by ext; exact hn }
  have hT := b65t_periodic_transport hWo hW hP c hper hsh w₁' h₁' a n Γp
  rw [b65t_transport_pullback_proof E U W hU hWo A hA π hπ hmaps _ _ _] at hT
  rw [← hT]
  apply b65t_transport_congr_Icc
  intro t ht
  simp only [Path.extend_apply _ ht, π]
  change (γ ⟨t, ht⟩ : ℂ) = p + Complex.exp (Γ ⟨t, ht⟩)
  rw [hΓ]
  ring


theorem b65t_x_four : (b4b_generators 2) ^ 4 = 1 := by
  have h := b65s_gw_eq (u := [2, 2, 2, 2]) (v := []) (by decide +kernel)
  simpa [b65s_gw, pow_succ, mul_assoc] using h

theorem b65t_y_three : (b4b_generators 3) ^ 3 = 1 := by
  have h := b65s_gw_eq (u := [3, 3, 3]) (v := []) (by decide +kernel)
  simpa [b65s_gw, pow_succ, mul_assoc] using h

theorem b65t_operator_injective {n : ℕ} : Function.Injective (b65r_operator (n := n)) := by
  intro M N h
  have h' : M.mulVecLin = N.mulVecLin := LinearMap.ext fun v ↦
    congrArg (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) ↦ T v) h
  exact Matrix.toLin'.injective h'

/-- Transport around a small circle about an apparent pole is trivial. -/
theorem b65t_apparent_circle (p : ℂ) (hp : p = 3 ∨ p = 1 ∨ p = -2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      b65f_transport (Fin 4 → ℂ) b65r_pullback (b65f_circle p ρ) = 1 := by
  obtain ⟨r, hr, h⟩ := b65r_pullback_local_monodromy p (by tauto)
  have ht : b65r_localTarget p = 1 := by
    rcases hp with rfl | rfl | rfl
    · simp [b65r_localTarget, b65t_x_four]
    · simp [b65r_localTarget, b65t_y_three]
    · norm_num [b65r_localTarget, b65t_y_three]
  refine ⟨r, hr, fun ρ h0 h1 ↦ ?_⟩
  obtain ⟨K, hK⟩ := h ρ h0 h1
  rw [hK, ht, map_one]
  have : b65r_operator (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
    ext v i; simp [b65r_operator]
  rw [this, mul_one, Units.mul_inv]


theorem b65t_phi_tendsto : Tendsto b65r_phi (cobounded ℂ) (𝓝 1) := by
  let g : ℂ → ℂ := fun u ↦ (1 - 3 * u) ^ 4 / ((1 - u) ^ 3 * (1 + 2 * u) ^ 3)
  have hg : ContinuousAt g 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have h1 : Tendsto (g ∘ Inv.inv) (cobounded ℂ) (𝓝 1) := by
    have := hg.tendsto.comp tendsto_inv₀_cobounded
    simpa [g] using this
  apply h1.congr'
  filter_upwards [eventually_cobounded_le_norm (3 : ℝ)] with z hz
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hz1 : z - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hz; norm_num at hz
  have hz2 : z + 2 ≠ 0 := by
    intro h; rw [show z = -2 by linear_combination h] at hz; norm_num at hz
  simp only [g, Function.comp_apply, b65r_phi]
  field_simp

theorem b65t_phi_near_one : ∃ R₀ : ℝ, ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖b65r_phi z - 1‖ < 1 / 2 := by
  have h := b65t_phi_tendsto.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0:ℝ) < 1 / 2))
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp h
  exact ⟨R₀, fun z hz ↦ by simpa [dist_eq_norm] using hR₀ hz⟩


/-- Loops near an apparent pole have trivial pullback transport. -/
theorem b65t_loop_near_apparent (p : ℂ) (hp : p = 3 ∨ p = 1 ∨ p = -2) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z : ℂ, ‖z - p‖ < r → z ≠ p → z ∈ b65s_regular)
    (q : b65s_regular) (γ : Path q q) (hγ : ∀ t, ‖(γ t : ℂ) - p‖ < r ∧ (γ t : ℂ) ≠ p) :
    b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) = 1 := by
  obtain ⟨r₀, hr₀, hcirc⟩ := b65t_apparent_circle p hp
  set ρ := min r r₀ / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r := by rw [hρ]; linarith [min_le_left r r₀]
  have hρr₀ : ρ < r₀ := by rw [hρ]; linarith [min_le_right r r₀]
  apply b65t_annulus_loop b65t_regular_open b65t_pullback_analytic p (J := Iio (Real.log r))
    isOpen_Iio (convex_Iio _) _ ((Real.log ρ : ℝ) : ℂ) _ _ q γ
  · intro t
    refine ⟨(hγ t).2, ?_⟩
    exact Real.log_lt_log (norm_pos_iff.mpr (sub_ne_zero.mpr (hγ t).2)) (hγ t).1
  · intro w hw
    apply hball
    · rw [add_sub_cancel_left, Complex.norm_exp]
      calc Real.exp w.re < Real.exp (Real.log r) := Real.exp_lt_exp.mpr hw
        _ = r := Real.exp_log hr
    · intro h
      have : Complex.exp w = 0 := by linear_combination h
      exact Complex.exp_ne_zero w this
  · simp only [Complex.ofReal_re, mem_Iio]
    exact Real.log_lt_log hρ0 hρr
  · rw [← hcirc ρ hρ0 hρr₀]
    congr 1
    funext t
    simp only [b65f_circle, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ0]
    ring_nf

/-- Loops near infinity have trivial pullback transport. -/
theorem b65t_loop_near_infty (R : ℝ) (hR : 0 < R)
    (hball : ∀ z : ℂ, R < ‖z‖ → z ∈ b65s_regular)
    (q : b65s_regular) (γ : Path q q) (hγ : ∀ t, R < ‖(γ t : ℂ)‖) :
    b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) = 1 := by
  obtain ⟨R₀, hR₀⟩ := b65t_phi_near_one
  set ρ := max R R₀ + 1 with hρ
  have hρR : R < ρ := by rw [hρ]; linarith [le_max_left R R₀]
  have hρR₀ : R₀ ≤ ρ := by rw [hρ]; linarith [le_max_right R R₀]
  have hρ0 : 0 < ρ := hR.trans hρR
  have hnorm : ∀ t, ‖b65f_circle 0 ρ t‖ = ρ := by
    intro t
    have := b65f_circle_norm 0 ρ t
    rwa [sub_zero, abs_of_pos hρ0] at this
  have hreg : ∀ t, b65f_circle 0 ρ t ∈ b65s_regular := fun t ↦ hball _ (by rw [hnorm]; exact hρR)
  let y : b65s_regular := ⟨b65f_circle 0 ρ 0, hreg 0⟩
  let c : Path y y :=
    { toFun := fun t ↦ ⟨b65f_circle 0 ρ t, hreg t⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        unfold b65f_circle
        fun_prop
      source' := by simp [y]
      target' := by
        apply Subtype.ext
        simp only [Set.Icc.coe_one, y]
        exact b65f_circle_one_eq_zero 0 ρ }
  -- the image of the circle lies in a disc about `1` where `b65r_A` is analytic
  let D : Set ℂ := ball 1 (1 / 2)
  have hDU : D ⊆ {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> norm_num at hz
  have hcD : ∀ t, b65r_phi (c t : ℂ) ∈ D := fun t ↦ by
    rw [mem_ball, dist_eq_norm]
    exact hR₀ _ (by change R₀ ≤ ‖b65f_circle 0 ρ t‖; rw [hnorm]; exact hρR₀)
  let c' : Path (⟨b65r_phi y, hcD 0⟩ : D) ⟨b65r_phi y, hcD 0⟩ :=
    { toFun := fun t ↦ ⟨b65r_phi (c t : ℂ), hcD t⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact b65t_phi_analytic.continuousOn.comp_continuous
          (continuous_subtype_val.comp c.continuous) (fun t ↦ (c t).property)
      source' := by simp
      target' := by simp }
  have hc1 : b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (c.extend t).val) = 1 := by
    rw [b65t_pullback_transport_proof]
    change b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (c'.extend t).val) = 1
    rw [b65t_convex_transport isOpen_ball (convex_ball _ _) (b65t_A_analytic.mono hDU) c'
      (Path.refl _)]
    exact b65t_transport_refl _ _
  apply b65t_annulus_loop b65t_regular_open b65t_pullback_analytic 0 (J := Ioi (Real.log R))
    isOpen_Ioi (convex_Ioi _) _ ((Real.log ρ : ℝ) : ℂ) _ _ q γ
  · intro t
    have h := hγ t
    refine ⟨fun h0 ↦ by rw [h0, norm_zero] at h; linarith, ?_⟩
    rw [sub_zero]
    exact Real.log_lt_log hR h
  · intro w hw
    apply hball
    rw [zero_add, Complex.norm_exp]
    calc R = Real.exp (Real.log R) := (Real.exp_log hR).symm
      _ < Real.exp w.re := Real.exp_lt_exp.mpr hw
  · simp only [Complex.ofReal_re, mem_Ioi]
    exact Real.log_lt_log hR hρR
  · rw [← hc1]
    apply b65t_transport_congr_Icc
    intro t ht
    simp only [Path.extend_apply c ht]
    change 0 + Complex.exp _ = b65f_circle 0 ρ t
    simp only [b65f_circle, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ0]
    ring_nf

end HodgeLean.Foundations.Program
