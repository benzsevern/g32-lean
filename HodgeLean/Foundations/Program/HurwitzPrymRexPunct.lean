import Mathlib

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: a Galois covering over a punctured disc

Over a punctured disc parametrized by `w ↦ ε(w)` on a left half-plane (`ε` periodic of period
`2πi`, e.g. `ε = ξ ∘ exp`), the half-plane is simply connected, so `ε` lifts to `L` through any
Galois `G`-covering. Translation by `2πi` is a deck transformation of the lift:
`L (w + 2πi) = h • L w` for a unique `h ∈ G`, and every point over the disc is `g • L w`, with
`g • L w = g' • L w'` exactly when `w' = w + 2πin` and `g = g' hⁿ`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Complex

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexPunct

/-- **The half-plane** `{w | Re w < c}`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §5.10 (the universal covering of the
punctured disc by a half-plane). -/
def HP (c : ℝ) : Set ℂ := {w | w.re < c}

example : (0 : ℂ) ∈ HP 1 := by simp [HP]

theorem isOpen_HP (c : ℝ) : IsOpen (HP c) := isOpen_lt continuous_re continuous_const

theorem convex_HP (c : ℝ) : Convex ℝ (HP c) := convex_halfSpace_re_lt c

theorem nonempty_HP (c : ℝ) : (HP c).Nonempty := ⟨(c - 1 : ℝ), by simp [HP]⟩

instance (c : ℝ) : SimplyConnectedSpace (HP c) :=
  haveI := (convex_HP c).contractibleSpace (nonempty_HP c)
  SimplyConnectedSpace.ofContractible _

instance (c : ℝ) : LocallyPathConnectedSpace (HP c) := (isOpen_HP c).locallyPathConnectedSpace

/-- Translation by `2πin` on the half-plane.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §5.10 (deck transformations of `exp`). -/
def shift (c : ℝ) (n : ℤ) (w : HP c) : HP c :=
  ⟨w + n * (2 * Real.pi * I), by simpa [HP] using w.2⟩

theorem continuous_shift (c : ℝ) (n : ℤ) : Continuous (shift c n) :=
  (continuous_subtype_val.add continuous_const).subtype_mk _

theorem shift_add (c : ℝ) (m n : ℤ) (w : HP c) : shift c (m + n) w = shift c m (shift c n w) := by
  apply Subtype.ext
  simp only [shift]
  push_cast
  ring

theorem shift_zero (c : ℝ) (w : HP c) : shift c 0 w = w := by
  apply Subtype.ext
  simp [shift]

example (c : ℝ) (w : HP c) : shift c 0 w = w := shift_zero c w

variable {X U G : Type} [TopologicalSpace X] [TopologicalSpace U] [Group G] [MulAction G U]
variable {p : U → X}
variable {c : ℝ} (ε : C(HP c, X))

/-- **The lift and its deck generator.** -/
theorem exists_lift (hp : IsQuotientCoveringMap p G) (hper : ∀ w, ε (shift c 1 w) = ε w) (w₀ : HP c) (u₀ : U)
    (hu₀ : p u₀ = ε w₀) :
    ∃ (L : C(HP c, U)) (h : G), p ∘ L = ε ∧ L w₀ = u₀ ∧ ∀ w, L (shift c 1 w) = h • L w := by
  have cov := hp.isCoveringMap
  obtain ⟨L, ⟨hL0, hLp⟩, -⟩ := cov.existsUnique_continuousMap_lifts ε w₀ u₀ hu₀
  have hfib : p (L (shift c 1 w₀)) = p (L w₀) := by
    have h1 := congrFun hLp (shift c 1 w₀)
    have h2 := congrFun hLp w₀
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2, hper]
  obtain ⟨h, hh⟩ := (hp.apply_eq_iff_mem_orbit.1 hfib)
  refine ⟨L, h, hLp, hL0, fun w ↦ ?_⟩
  -- both `L ∘ shift` and `h • L` lift `ε` and agree at `w₀`
  let L₁ : C(HP c, U) := L.comp ⟨shift c 1, continuous_shift c 1⟩
  let L₂ : C(HP c, U) := ⟨fun w ↦ h • L w, (hp.continuous_const_smul h).comp L.continuous⟩
  obtain ⟨F, -, hF⟩ := cov.existsUnique_continuousMap_lifts ε w₀ (L (shift c 1 w₀))
    (by rw [hfib, hL0, hu₀])
  have e1 : L₁ = F := hF L₁ ⟨rfl, by
    funext w
    simp only [Function.comp_apply, L₁, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    rw [← hper w]
    exact congrFun hLp _⟩
  have e2 : L₂ = F := hF L₂ ⟨by simp [L₂, hh], by
    funext w
    simp only [Function.comp_apply, L₂, ContinuousMap.coe_mk]
    have := hp.apply_eq_iff_mem_orbit (e₁ := h • L w) (e₂ := L w)
    rw [this.2 ⟨h, rfl⟩]
    exact congrFun hLp w⟩
  have := congrArg (fun F : C(HP c, U) ↦ F w) (e1.trans e2.symm)
  simpa [L₁, L₂] using this

variable {ε}

theorem lift_shift_int {L : C(HP c, U)} {h : G} (hL : ∀ w, L (shift c 1 w) = h • L w) (n : ℤ)
    (w : HP c) : L (shift c n w) = h ^ n • L w := by
  induction n using Int.induction_on generalizing w with
  | zero => simp [shift_zero]
  | succ n ih =>
    rw [add_comm, shift_add, hL, ih, zpow_add, zpow_one, mul_smul]
  | pred n ih =>
    have := hL (shift c (-n - 1) w)
    rw [← shift_add, show (1 : ℤ) + (-n - 1) = -n by ring, ih] at this
    rw [show (-(n : ℤ) - 1) = -n - 1 by ring]
    have h2 : L (shift c (-n - 1) w) = h⁻¹ • h ^ (-(n : ℤ)) • L w := by
      rw [this, inv_smul_smul]
    rw [h2, ← mul_smul, ← zpow_neg_one, ← zpow_add]
    ring_nf

open Metric

/-- **Puncture data**: a punctured coordinate disc `ξ : B(0,r)∖0 → X` (an open embedding with
inverse `ψ`), and a lift `L` of `w ↦ ξ (exp w)` from the half-plane `Re w < log r` to `U`, with
deck generator `h`: `L (w + 2πi) = h • L w`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 5.10 (coverings of the punctured
disc) and §8 (filling in punctures). -/
structure Datum (p : U → X) (G : Type) [Group G] [MulAction G U] where
  r : ℝ
  hr : 0 < r
  ξ : ℂ → X
  ψ : X → ℂ
  ξ_cont : ContinuousOn ξ (ball 0 r \ {0})
  ψ_cont : ContinuousOn ψ (ξ '' (ball 0 r \ {0}))
  ψ_ξ : ∀ z ∈ ball (0 : ℂ) r \ {0}, ψ (ξ z) = z
  isOpen_image : IsOpen (ξ '' (ball 0 r \ {0}))
  L : C(HP (Real.log r), U)
  h : G
  lifts : ∀ w, p (L w) = ξ (exp w)
  shift_eq : ∀ w, L (shift _ 1 w) = h • L w

namespace Datum

variable {p : U → X} (D : Datum p G)

example : 0 < D.r := D.hr

theorem exp_mem (w : HP (Real.log D.r)) : exp (w : ℂ) ∈ ball (0 : ℂ) D.r \ {0} := by
  refine ⟨?_, exp_ne_zero _⟩
  rw [mem_ball_zero_iff, norm_exp]
  have := w.2
  simp only [HP, Set.mem_setOf_eq] at this
  calc Real.exp (w : ℂ).re < Real.exp (Real.log D.r) := Real.exp_lt_exp.2 this
    _ = D.r := Real.exp_log D.hr

/-- The ramification order `e`, the order of the deck generator.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 5.10. -/
def e : ℕ := orderOf D.h

/-- Clamp into the half-plane.
Source: the definition of a retraction onto a subset (junk outside). -/
def toHP (w : ℂ) : HP (Real.log D.r) :=
  if hw : w.re < Real.log D.r then ⟨w, hw⟩ else ⟨(Real.log D.r - 1 : ℝ), by simp [HP]⟩

example (D : Datum p G) : D.e = orderOf D.h := rfl

theorem toHP_of {w : ℂ} (hw : w.re < Real.log D.r) : (D.toHP w : ℂ) = w := by
  simp [toHP, hw]

/-- **The punctured disc of the puncture chart**: `0 < |v|`, `|v|^e < r`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 5.10. -/
def Dom : Set ℂ := {v | v ≠ 0 ∧ ‖v‖ ^ D.e < D.r}

/-- **The puncture coordinate map** `v ↦ g • L (e log v)`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 5.10. -/
def M (g : G) (v : ℂ) : U := g • D.L (D.toHP (D.e * log v))

example (g : G) (v : ℂ) : D.M g v = g • D.L (D.toHP (D.e * log v)) := rfl

example : (0 : ℂ) ∉ D.Dom := fun h ↦ h.1 rfl

theorem re_mul_log_lt {v : ℂ} (hv : v ∈ D.Dom) : ((D.e : ℂ) * log v).re < Real.log D.r := by
  obtain ⟨hv0, hvr⟩ := hv
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have : ((D.e : ℂ) * log v).re = Real.log (‖v‖ ^ D.e) := by
    rw [Real.log_pow, ← log_re]
    simp
  rw [this]
  exact Real.log_lt_log (pow_pos hpos _) hvr

variable [Finite G]

theorem e_pos : 0 < D.e := orderOf_pos D.h

theorem exp_mul_log {v : ℂ} (hv : v ≠ 0) (n : ℕ) : exp (n * log v) = v ^ n := by
  rw [exp_nat_mul, exp_log hv]


variable {D}
variable (hp : IsQuotientCoveringMap p G)
include hp

theorem p_smul (g : G) (u : U) : p (g • u) = p u := hp.apply_eq_iff_mem_orbit.2 ⟨g, rfl⟩

theorem L_shift_int (n : ℤ) (w : HP (Real.log D.r)) : D.L (shift _ n w) = D.h ^ n • D.L w :=
  lift_shift_int D.shift_eq n w

/-- `p (M g v) = ξ (v ^ e)`. -/
theorem p_M (g : G) {v : ℂ} (hv : v ∈ D.Dom) : p (D.M g v) = D.ξ (v ^ D.e) := by
  rw [M, p_smul hp, D.lifts, D.toHP_of (D.re_mul_log_lt hv), exp_mul_log hv.1]

/-- **`g • L w = g' • L w'` iff `w' = w + 2πin` and `g = g' hⁿ`.** -/
theorem smul_L_eq_iff {g g' : G} {w w' : HP (Real.log D.r)} :
    g • D.L w = g' • D.L w' ↔ ∃ n : ℤ, w' = shift _ n w ∧ g = g' * D.h ^ n := by
  constructor
  · intro heq
    have hpe := congrArg p heq
    rw [p_smul hp, p_smul hp, D.lifts, D.lifts] at hpe
    have hex : exp (w : ℂ) = exp (w' : ℂ) := by
      have := congrArg D.ψ hpe
      rwa [D.ψ_ξ _ (D.exp_mem w), D.ψ_ξ _ (D.exp_mem w')] at this
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hex.symm
    have hw' : w' = shift _ n w := by
      apply Subtype.ext
      simp only [shift]
      rw [hn]
    refine ⟨n, hw', ?_⟩
    rw [hw', L_shift_int hp, ← mul_smul] at heq
    exact hp.isCancelSMul.right_cancel _ _ _ heq
  · rintro ⟨n, rfl, rfl⟩
    rw [L_shift_int hp, ← mul_smul]

theorem M_eq_M_iff {g g' : G} {v v' : ℂ} (hv : v ∈ D.Dom) (hv' : v' ∈ D.Dom) :
    D.M g v = D.M g' v' ↔ ∃ n : ℤ, (D.e : ℂ) * log v' = D.e * log v + n * (2 * Real.pi * I) ∧
      g = g' * D.h ^ n := by
  rw [M, M, smul_L_eq_iff hp]
  constructor
  · rintro ⟨n, hn, hg⟩
    refine ⟨n, ?_, hg⟩
    have := congrArg Subtype.val hn
    simp only [shift] at this
    rwa [D.toHP_of (D.re_mul_log_lt hv'), D.toHP_of (D.re_mul_log_lt hv)] at this
  · rintro ⟨n, hn, hg⟩
    refine ⟨n, Subtype.ext ?_, hg⟩
    simp only [shift]
    rw [D.toHP_of (D.re_mul_log_lt hv'), D.toHP_of (D.re_mul_log_lt hv), hn]

/-- **`M g` is injective on the punctured disc.** -/
theorem M_injOn (g : G) : Set.InjOn (D.M g) D.Dom := by
  intro v hv v' hv' heq
  obtain ⟨n, hn, hg⟩ := (M_eq_M_iff hp hv hv').1 heq
  have hpow : D.h ^ n = 1 := by
    have := congrArg (g⁻¹ * ·) hg
    simp only [inv_mul_cancel, ← mul_assoc, one_mul] at this
    exact this.symm
  obtain ⟨m, rfl⟩ := (orderOf_dvd_iff_zpow_eq_one.2 hpow)
  have he : (D.e : ℂ) ≠ 0 := by exact_mod_cast (D.e_pos).ne'
  have hlog : log v' = log v + m * (2 * Real.pi * I) := by
    have : (D.e : ℂ) * log v' = D.e * (log v + m * (2 * Real.pi * I)) := by
      rw [hn]
      change (D.e : ℂ) * log v + ((orderOf D.h * m : ℤ) : ℂ) * (2 * Real.pi * I) = _
      push_cast
      simp only [e]
      ring
    exact mul_left_cancel₀ he this
  rw [← exp_log hv.1, ← exp_log hv'.1, hlog, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- Points `M g v = M g' v'` lie in the same coset. -/
theorem M_eq_M_coset {g g' : G} {v v' : ℂ} (hv : v ∈ D.Dom) (hv' : v' ∈ D.Dom)
    (heq : D.M g v = D.M g' v') : ∃ n : ℤ, g = g' * D.h ^ n := by
  obtain ⟨n, -, hg⟩ := (M_eq_M_iff hp hv hv').1 heq
  exact ⟨n, hg⟩

/-- The primitive `e`-th root of unity `ζ = exp (2πi/e)`.
Source: the definition of the primitive root of unity. -/
def ζ (D : Datum p G) : ℂ := exp (2 * Real.pi * I / D.e)

omit hp [Finite G] in
example : D.ζ = exp (2 * Real.pi * I / D.e) := rfl

omit hp [Finite G] in
theorem norm_ζ_pow (j : ℤ) : ‖D.ζ ^ j‖ = 1 := by
  rw [norm_zpow, ζ, norm_exp]
  simp

omit hp in
theorem mul_ζ_mem {v : ℂ} (hv : v ∈ D.Dom) (j : ℤ) : v * D.ζ ^ j ∈ D.Dom := by
  refine ⟨mul_ne_zero hv.1 (zpow_ne_zero _ (exp_ne_zero _)), ?_⟩
  rw [norm_mul, norm_ζ_pow, mul_one]
  exact hv.2

/-- **Changing the coset representative rotates the coordinate**: `M (g hʲ) v = M g (v ζʲ)`. -/
theorem M_mul_zpow (g : G) {v : ℂ} (hv : v ∈ D.Dom) (j : ℤ) :
    D.M (g * D.h ^ j) v = D.M g (v * D.ζ ^ j) := by
  have he : (D.e : ℂ) ≠ 0 := by exact_mod_cast (D.e_pos).ne'
  have hv' := mul_ζ_mem hv j
  -- `log (v ζʲ) = log v + 2πij/e + 2πim`
  have hexp : exp (log (v * D.ζ ^ j)) = exp (log v + j * (2 * Real.pi * I / D.e)) := by
    rw [exp_log hv'.1, exp_add, exp_log hv.1, ζ, ← exp_int_mul, mul_comm]
  obtain ⟨m, hm⟩ := exp_eq_exp_iff_exists_int.1 hexp
  symm
  rw [M_eq_M_iff hp hv' hv]
  refine ⟨-(j + D.e * m), ?_, ?_⟩
  · rw [hm]
    push_cast
    field_simp
    ring
  · have hhe : D.h ^ ((D.e : ℤ) * m) = 1 := by
      rw [zpow_mul, zpow_natCast]
      simp [e, pow_orderOf_eq_one]
    rw [mul_assoc, ← zpow_add, show (j : ℤ) + -(j + D.e * m) = -(D.e * m) by ring, zpow_neg,
      hhe, inv_one, mul_one]

omit hp in
theorem isOpen_Dom : IsOpen D.Dom := by
  have h1 : IsOpen {v : ℂ | v ≠ 0} := isOpen_ne
  have h2 : IsOpen {v : ℂ | ‖v‖ ^ D.e < D.r} :=
    isOpen_lt (continuous_norm.pow _) continuous_const
  exact h1.inter h2

/-- **Every point over the disc is `M g v`** with `v ^ e = z`. -/
theorem exists_M {u : U} {z : ℂ} (hz : z ∈ ball (0 : ℂ) D.r \ {0}) (hu : p u = D.ξ z) :
    ∃ g : G, ∃ v ∈ D.Dom, D.M g v = u ∧ v ^ D.e = z := by
  have he : (D.e : ℂ) ≠ 0 := by exact_mod_cast (D.e_pos).ne'
  have hz0 : z ≠ 0 := hz.2
  have hlogre : (log z).re < Real.log D.r := by
    rw [log_re]
    exact Real.log_lt_log (norm_pos_iff.2 hz0) (mem_ball_zero_iff.1 hz.1)
  set w : HP (Real.log D.r) := ⟨log z, hlogre⟩
  have hpw : p u = p (D.L w) := by rw [hu, D.lifts, exp_log hz0]
  obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.1 hpw
  set v := exp (log z / D.e)
  have hve : v ^ D.e = z := by
    rw [← exp_nat_mul, mul_div_cancel₀ _ he, exp_log hz0]
  have hvD : v ∈ D.Dom := by
    refine ⟨exp_ne_zero _, ?_⟩
    rw [← norm_pow, hve]
    exact mem_ball_zero_iff.1 hz.1
  have hexp : exp ((D.e : ℂ) * log v) = exp (log z) := by
    rw [exp_mul_log hvD.1, hve, exp_log hz0]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
  refine ⟨g * D.h ^ (-n), v, hvD, ?_, hve⟩
  have hw : D.toHP (D.e * log v) = shift _ n w := by
    apply Subtype.ext
    rw [D.toHP_of (D.re_mul_log_lt hvD)]
    simp only [shift, w]
    exact hn
  rw [M, hw, L_shift_int hp, ← mul_smul, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
    mul_one]
  exact hg

omit hp [Finite G] in
theorem continuousAt_toHP {w : ℂ} (hw : w.re < Real.log D.r) :
    ContinuousAt D.toHP w := by
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
  refine continuousAt_id.congr ?_
  filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hw] with w' hw'
  exact (D.toHP_of hw').symm

/-- **`M g` is continuous on the punctured disc**: near `v₀` it is `g • L (e ℓ v)` for the
continuous branch `ℓ v = log (v / v₀) + log v₀` of the logarithm. -/
theorem continuousAt_M (g : G) {v₀ : ℂ} (hv₀ : v₀ ∈ D.Dom) : ContinuousAt (D.M g) v₀ := by
  have he : (D.e : ℂ) ≠ 0 := by exact_mod_cast (D.e_pos).ne'
  set ℓ : ℂ → ℂ := fun v ↦ log (v / v₀) + log v₀
  have hℓ0 : ℓ v₀ = log v₀ := by simp [ℓ, div_self hv₀.1]
  have hslit : ∀ᶠ v in 𝓝 v₀, v / v₀ ∈ slitPlane := by
    have : ContinuousAt (fun v : ℂ ↦ v / v₀) v₀ := continuousAt_id.div_const _
    exact this.preimage_mem_nhds (isOpen_slitPlane.mem_nhds (by simp [div_self hv₀.1]))
  have hℓc : ContinuousAt ℓ v₀ :=
    ((continuousAt_clog (by simp [div_self hv₀.1])).comp
      (continuousAt_id.div_const v₀)).add continuousAt_const
  have hre : ((D.e : ℂ) * ℓ v₀).re < Real.log D.r := by
    rw [hℓ0]; exact D.re_mul_log_lt hv₀
  have := hp.toContinuousConstSMul
  have hF : ContinuousAt (fun v ↦ g • D.L (D.toHP (D.e * ℓ v))) v₀ := by
    refine (continuous_const_smul g).continuousAt.comp ?_
    refine D.L.continuous.continuousAt.comp ?_
    have hmul : ContinuousAt (fun v ↦ (D.e : ℂ) * ℓ v) v₀ :=
      (continuous_const_mul (D.e : ℂ)).continuousAt.comp hℓc
    exact ContinuousAt.comp (f := fun v ↦ (D.e : ℂ) * ℓ v) (D.continuousAt_toHP hre) hmul
  refine hF.congr ?_
  filter_upwards [hslit, D.isOpen_Dom.mem_nhds hv₀] with v hv hvD
  -- `log v = ℓ v + 2πik`
  have hexp : exp (log v) = exp (ℓ v) := by
    simp only [ℓ, exp_add]
    rw [exp_log hvD.1, exp_log (div_ne_zero hvD.1 hv₀.1), exp_log hv₀.1, div_mul_cancel₀ _ hv₀.1]
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 hexp
  have hreℓ : ((D.e : ℂ) * ℓ v).re < Real.log D.r := by
    have : ((D.e : ℂ) * ℓ v).re = ((D.e : ℂ) * log v).re := by
      rw [hk]; simp [mul_add]
    rw [this]; exact D.re_mul_log_lt hvD
  have hw : D.toHP (D.e * log v) = shift _ (D.e * k) (D.toHP (D.e * ℓ v)) := by
    apply Subtype.ext
    simp only [shift]
    rw [D.toHP_of (D.re_mul_log_lt hvD), D.toHP_of hreℓ, hk]
    push_cast
    ring
  have hhe : D.h ^ ((D.e : ℤ) * k) = 1 := by
    rw [zpow_mul, zpow_natCast]
    simp [e, pow_orderOf_eq_one]
  simp only [M]
  rw [hw, L_shift_int hp, hhe, one_smul]

theorem continuousOn_M (g : G) : ContinuousOn (D.M g) D.Dom := fun _ hv ↦
  (continuousAt_M hp g hv).continuousWithinAt

/-- **The `e`-th root branch through `v₀`**: `R z = v₀ (z / v₀ᵉ)^{1/e}`.
Source: Mathlib `Complex.cpow` (the principal branch). -/
def R (D : Datum p G) (v₀ z : ℂ) : ℂ := v₀ * (z / v₀ ^ D.e) ^ ((D.e : ℂ)⁻¹)

omit hp [Finite G] in
example (v₀ z : ℂ) : D.R v₀ z = v₀ * (z / v₀ ^ D.e) ^ ((D.e : ℂ)⁻¹) := rfl

omit hp in
theorem R_pow {v₀ : ℂ} (hv₀ : v₀ ≠ 0) (z : ℂ) : D.R v₀ z ^ D.e = z := by
  rw [R, mul_pow, cpow_nat_inv_pow _ (D.e_pos).ne']
  field_simp

omit hp [Finite G] in
theorem R_self {v₀ : ℂ} (hv₀ : v₀ ≠ 0) : D.R v₀ (v₀ ^ D.e) = v₀ := by
  rw [R, div_self (pow_ne_zero _ hv₀), one_cpow, mul_one]

omit hp [Finite G] in
theorem continuousAt_R {v₀ : ℂ} (hv₀ : v₀ ≠ 0) : ContinuousAt (D.R v₀) (v₀ ^ D.e) := by
  have h1 : (v₀ ^ D.e / v₀ ^ D.e) ∈ slitPlane := by
    rw [div_self (pow_ne_zero _ hv₀)]; exact one_mem_slitPlane
  have h2 : ContinuousAt (fun z : ℂ ↦ (z / v₀ ^ D.e) ^ ((D.e : ℂ)⁻¹)) (v₀ ^ D.e) :=
    ContinuousAt.comp (g := fun x : ℂ ↦ x ^ ((D.e : ℂ)⁻¹)) (f := fun z : ℂ ↦ z / v₀ ^ D.e)
      (continuousAt_cpow_const h1) (continuousAt_id.div_const _)
  exact continuousAt_const.mul h2

/-- **Local inverse of `M g`**: near `M g v₀`, every point is `M g (R v₀ (ψ (p u)))`. -/
theorem eventually_M_R (g : G) {v₀ : ℂ} (hv₀ : v₀ ∈ D.Dom) :
    ∀ᶠ u in 𝓝 (D.M g v₀), D.R v₀ (D.ψ (p u)) ∈ D.Dom ∧ D.M g (D.R v₀ (D.ψ (p u))) = u := by
  set u₀ := D.M g v₀
  have hz₀ : v₀ ^ D.e ∈ ball (0 : ℂ) D.r \ {0} :=
    ⟨mem_ball_zero_iff.2 (by rw [norm_pow]; exact hv₀.2), pow_ne_zero _ hv₀.1⟩
  have hpu₀ : p u₀ = D.ξ (v₀ ^ D.e) := p_M hp g hv₀
  have himg : p u₀ ∈ D.ξ '' (ball 0 D.r \ {0}) := ⟨_, hz₀, hpu₀.symm⟩
  have hψu₀ : D.ψ (p u₀) = v₀ ^ D.e := by rw [hpu₀, D.ψ_ξ _ hz₀]
  have hpc : ContinuousAt p u₀ := hp.continuous.continuousAt
  have hψc : ContinuousAt D.ψ (p u₀) :=
    D.ψ_cont.continuousAt (D.isOpen_image.mem_nhds himg)
  have hFc : ContinuousAt (fun u ↦ D.R v₀ (D.ψ (p u))) u₀ := by
    have hRc := D.continuousAt_R hv₀.1
    rw [← hψu₀] at hRc
    exact ContinuousAt.comp (f := fun u ↦ D.ψ (p u)) hRc (hψc.comp hpc)
  have hFu₀ : D.R v₀ (D.ψ (p u₀)) = v₀ := by rw [hψu₀, D.R_self hv₀.1]
  have hMF : ContinuousAt (fun u ↦ D.M g (D.R v₀ (D.ψ (p u)))) u₀ := by
    have hMc := continuousAt_M hp g hv₀
    rw [← hFu₀] at hMc
    exact ContinuousAt.comp (f := fun u ↦ D.R v₀ (D.ψ (p u))) hMc hFc
  obtain ⟨σ, hσu, hσ⟩ := hp.isCoveringMap.isLocalHomeomorph u₀
  have h1 : ∀ᶠ u in 𝓝 u₀, D.R v₀ (D.ψ (p u)) ∈ D.Dom :=
    hFc.preimage_mem_nhds (by rw [hFu₀]; exact D.isOpen_Dom.mem_nhds hv₀)
  have h2 : ∀ᶠ u in 𝓝 u₀, D.M g (D.R v₀ (D.ψ (p u))) ∈ σ.source :=
    hMF.preimage_mem_nhds (by
      rw [hFu₀]; exact σ.open_source.mem_nhds hσu)
  have h3 : ∀ᶠ u in 𝓝 u₀, u ∈ σ.source := σ.open_source.mem_nhds hσu
  have h4 : ∀ᶠ u in 𝓝 u₀, p u ∈ D.ξ '' (ball 0 D.r \ {0}) :=
    hpc.preimage_mem_nhds (D.isOpen_image.mem_nhds himg)
  filter_upwards [h1, h2, h3, h4] with u hu1 hu2 hu3 hu4
  refine ⟨hu1, σ.injOn hu2 hu3 ?_⟩
  rw [← hσ, p_M hp g hu1, D.R_pow hv₀.1]
  obtain ⟨z, hz, hzu⟩ := hu4
  rw [← hzu, D.ψ_ξ _ hz]

/-- The root-branch inverse is continuous at `M g v₀`. -/
theorem continuousAt_R_ψ_p (g : G) {v₀ : ℂ} (hv₀ : v₀ ∈ D.Dom) :
    ContinuousAt (fun u ↦ D.R v₀ (D.ψ (p u))) (D.M g v₀) := by
  have hz₀ : v₀ ^ D.e ∈ ball (0 : ℂ) D.r \ {0} :=
    ⟨mem_ball_zero_iff.2 (by rw [norm_pow]; exact hv₀.2), pow_ne_zero _ hv₀.1⟩
  have hpu₀ : p (D.M g v₀) = D.ξ (v₀ ^ D.e) := p_M hp g hv₀
  have himg : p (D.M g v₀) ∈ D.ξ '' (ball 0 D.r \ {0}) := ⟨_, hz₀, hpu₀.symm⟩
  have hψu₀ : D.ψ (p (D.M g v₀)) = v₀ ^ D.e := by rw [hpu₀, D.ψ_ξ _ hz₀]
  have hψc : ContinuousAt D.ψ (p (D.M g v₀)) :=
    D.ψ_cont.continuousAt (D.isOpen_image.mem_nhds himg)
  have hRc := D.continuousAt_R hv₀.1
  rw [← hψu₀] at hRc
  exact ContinuousAt.comp (f := fun u ↦ D.ψ (p u)) hRc (hψc.comp hp.continuous.continuousAt)

/-- **The image of `M g` is open.** -/
theorem isOpen_image_M (g : G) : IsOpen (D.M g '' D.Dom) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨v₀, hv₀, rfl⟩
  filter_upwards [eventually_M_R hp g hv₀] with u hu
  exact ⟨_, hu.1, hu.2⟩

end Datum

end HurwitzPrymRexPunct

end HodgeLean.Foundations.Program
