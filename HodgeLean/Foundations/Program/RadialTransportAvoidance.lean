import HodgeLean.Foundations.Program.RadialTransportSquareComparison
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.ContinuousMap.Compact

/-! # Relative approximation and buffered radial detours

Bernstein approximation and small perturbations in one complex coordinate avoid
a prescribed point while retaining the endpoints. A radial expansion supported
in a buffered ball then gives relative avoidance of that ball.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology Polynomial
namespace HodgeLean.Foundations.Program

theorem rtc_polynomial_point_avoidance (f : C(unitInterval, Fin 10 → ℂ))
    (c : Fin 10 → ℂ) (h0 : f 0 ≠ c) (h1 : f 1 ≠ c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(unitInterval, Fin 10 → ℂ), g 0 = f 0 ∧ g 1 = f 1 ∧
      (∀ t, g t ≠ c) ∧ ∀ t, dist (g t) (f t) < ε := by
  have hev : ∀ᶠ n : ℕ in atTop, dist (bernsteinApproximation n f) f < ε / 2 :=
    (Metric.tendsto_nhds.mp (bernsteinApproximation_uniform f)) _ (by positivity)
  obtain ⟨n, hn, happ⟩ := ((eventually_gt_atTop 0).and hev).exists
  let q := bernsteinApproximation n f
  have hq0 : q 0 = f 0 := bernsteinApproximation.apply_zero n f
  have hq1 : q 1 = f 1 := bernsteinApproximation.apply_one (by omega) f
  let p : ℝ[X] := ∑ k : Fin (n + 1),
    bernsteinPolynomial ℝ n k * Polynomial.C ((f (bernstein.z k) 0).re)
  have hp (t : unitInterval) : p.eval (t : ℝ) = (q t 0).re := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      q, bernsteinApproximation.apply, Finset.sum_apply, Complex.re_sum,
      Pi.smul_apply, Complex.real_smul]
    apply Finset.sum_congr rfl
    intro k _
    simp [bernstein, Complex.mul_re]
  have hd : ∃ δ : ℝ, |δ| ≤ ε / 8 ∧
      (p + Polynomial.C δ * Polynomial.X * (1 - Polynomial.X) -
        Polynomial.C (c 0).re).eval (1 / 2) ≠ 0 := by
    by_cases h : (p + Polynomial.C (ε / 8) * Polynomial.X * (1 - Polynomial.X) -
        Polynomial.C (c 0).re).eval (1 / 2) = 0
    · refine ⟨ε / 16, by rw [abs_of_pos (by positivity)]; linarith, ?_⟩
      simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] at h ⊢
      intro he
      nlinarith
    · exact ⟨ε / 8, by rw [abs_of_pos (by positivity)], h⟩
  obtain ⟨δ, hδ, hδp⟩ := hd
  let d := p + Polynomial.C δ * Polynomial.X * (1 - Polynomial.X) -
    Polynomial.C (c 0).re
  have hdne : d ≠ 0 := by
    intro he
    apply hδp
    change d.eval (1 / 2) = 0
    rw [he, Polynomial.eval_zero]
  let bad : Set ℝ := (fun x : ℝ ↦ ((c 0).im -
    (q (Set.projIcc 0 1 zero_le_one x) 0).im) / (x * (1 - x))) ''
      (↑d.roots.toFinset : Set ℝ)
  have hbad : bad.Finite := d.roots.toFinset.finite_toSet.image _
  obtain ⟨η, hη, hηbad⟩ :=
    ((Set.Ioo_infinite (show -(ε / 8) < ε / 8 by linarith)).sdiff hbad).nonempty
  have hηabs : |η| < ε / 8 := abs_lt.mpr hη
  let v : C(unitInterval, Fin 10 → ℂ) :=
    ⟨fun t i ↦ if i = 0 then ((t : ℝ) * (1 - (t : ℝ))) •
      ((δ : ℂ) + (η : ℂ) * Complex.I) else 0, by
        apply continuous_pi
        intro i
        split_ifs <;> fun_prop⟩
  let g := q + v
  have hv0 : v 0 = 0 := by ext i; simp [v]
  have hv1 : v 1 = 0 := by ext i; simp [v]
  refine ⟨g, by simp only [g, ContinuousMap.add_apply, hv0, add_zero, hq0],
    by simp only [g, ContinuousMap.add_apply, hv1, add_zero, hq1], ?_, ?_⟩
  · intro t he
    have ht0 : t ≠ 0 := by
      intro ht
      subst t
      apply h0
      simpa only [g, ContinuousMap.add_apply, hv0, add_zero, hq0] using he
    have ht1 : t ≠ 1 := by
      intro ht
      subst t
      apply h1
      simpa only [g, ContinuousMap.add_apply, hv1, add_zero, hq1] using he
    have htn0 : (t : ℝ) ≠ 0 := fun h ↦ ht0 (Subtype.ext h)
    have htn1 : 1 - (t : ℝ) ≠ 0 := by
      intro h
      apply ht1
      apply Subtype.ext
      change (t : ℝ) = 1
      linarith
    have hc := congrFun he 0
    have hre : d.eval (t : ℝ) = 0 := by
      have hr := congrArg Complex.re hc
      simp [g, v, Complex.mul_re, Complex.mul_im] at hr
      simp only [d, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, hp]
      linarith
    apply hηbad
    refine ⟨(t : ℝ), ?_, ?_⟩
    · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hdne).mpr hre)
    · have hi := congrArg Complex.im hc
      simp [g, v, Complex.mul_re, Complex.mul_im] at hi
      change ((c 0).im - (q (Set.projIcc 0 1 zero_le_one (t : ℝ)) 0).im) /
        ((t : ℝ) * (1 - (t : ℝ))) = η
      rw [Set.projIcc_val]
      apply (div_eq_iff (mul_ne_zero htn0 htn1)).mpr
      nlinarith
  · intro t
    have hv : ‖v t‖ ≤ ε / 4 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      dsimp [v]
      split_ifs with hi
      · have hw : ‖(δ : ℂ) + (η : ℂ) * Complex.I‖ ≤ ε / 4 := by
          calc
            _ ≤ ‖(δ : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := norm_add_le _ _
            _ = |δ| + |η| := by simp [Complex.norm_real, Real.norm_eq_abs]
            _ ≤ ε / 4 := by linarith [hηabs.le]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2))]
        have ht : (t : ℝ) * (1 - (t : ℝ)) ≤ 1 := by nlinarith [t.2.1, t.2.2]
        exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (by simpa using hw)
      · simpa using (show (0 : ℝ) ≤ ε / 4 by positivity)
    calc
      dist (g t) (f t) ≤ dist (g t) (q t) + dist (q t) (f t) := dist_triangle _ _ _
      _ = ‖v t‖ + dist (q t) (f t) := by
        congr 1
        simp only [g, ContinuousMap.add_apply, dist_eq_norm, add_sub_cancel_left]
      _ < ε := by
        have hq := (ContinuousMap.dist_apply_le_dist t (f := q) (g := f)).trans_lt happ
        linarith

theorem rtc_open_point_avoidance (U : Set (Fin 10 → ℂ)) (hU : IsOpen U)
    {a b : U} (α : Path a b) (c : Fin 10 → ℂ)
    (ha : a.val ≠ c) (hb : b.val ≠ c) :
    ∃ β : Path a b, α.Homotopic β ∧ ∀ t, (β t).val ≠ c := by
  let f : C(unitInterval, Fin 10 → ℂ) :=
    ⟨fun t ↦ (α t).val, continuous_subtype_val.comp α.continuous⟩
  obtain ⟨ε, hε, htube⟩ := (isCompact_range f.continuous).exists_cthickening_subset_open hU
    (by rintro _ ⟨t, rfl⟩; exact (α t).property)
  obtain ⟨g, hg0, hg1, hg, hnear⟩ := rtc_polynomial_point_avoidance f c
    (by simpa only [f, ContinuousMap.coe_mk, α.source] using ha)
    (by simpa only [f, ContinuousMap.coe_mk, α.target] using hb) ε hε
  let F : unitInterval × unitInterval → Fin 10 → ℂ :=
    fun w ↦ (1 - (w.1 : ℝ)) • f w.2 + (w.1 : ℝ) • g w.2
  have hFc : Continuous F :=
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (f.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (g.continuous.comp continuous_snd)))
  have hFU (s t : unitInterval) : F (s, t) ∈ U := by
    apply htube
    apply Metric.mem_cthickening_of_dist_le _ (f t) ε (Set.range f) ⟨t, rfl⟩
    rw [dist_eq_norm]
    have he : F (s, t) - f t = (s : ℝ) • (g t - f t) := by dsimp [F]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.2.1]
    have hn : ‖g t - f t‖ < ε := by simpa only [dist_eq_norm] using hnear t
    exact (mul_le_mul_of_nonneg_right s.2.2 (norm_nonneg _)).trans (by simpa using hn.le)
  have hFg (t : unitInterval) : F (1, t) = g t := by simp [F]
  have hgU (t : unitInterval) : g t ∈ U := hFg t ▸ hFU 1 t
  let β : Path a b :=
    { toFun := fun t ↦ ⟨g t, hgU t⟩
      continuous_toFun := g.continuous.subtype_mk _
      source' := Subtype.ext (hg0.trans (congrArg Subtype.val α.source))
      target' := Subtype.ext (hg1.trans (congrArg Subtype.val α.target)) }
  refine ⟨β, ⟨?_⟩, hg⟩
  exact
    { toFun := fun w ↦ ⟨F w, hFU w.1 w.2⟩
      continuous_toFun := hFc.subtype_mk _
      map_zero_left := fun t ↦ Subtype.ext (by simp [F, f])
      map_one_left := fun t ↦ Subtype.ext (hFg t)
      prop' := fun s t ht ↦ by
        apply Subtype.ext
        rcases ht with rfl | rfl
        · change F (s, 0) = f 0
          rw [show F (s, 0) = (1 - (s : ℝ)) • f 0 + (s : ℝ) • g 0 from rfl, hg0]
          module
        · change F (s, 1) = f 1
          rw [show F (s, 1) = (1 - (s : ℝ)) • f 1 + (s : ℝ) • g 1 from rfl, hg1]
          module }

def rtc_outward (c : Fin 10 → ℂ) (R : ℝ) (s : unitInterval) (z : Fin 10 → ℂ) :
    Fin 10 → ℂ :=
  c + ((1 - (s : ℝ)) + (s : ℝ) * max 1 (R / ‖z - c‖)) • (z - c)

theorem rtc_outward_fixed (c z : Fin 10 → ℂ) (R : ℝ) (hR : 0 < R)
    (hz : R ≤ ‖z - c‖) (s : unitInterval) : rtc_outward c R s z = z := by
  have hd : 0 < ‖z - c‖ := hR.trans_le hz
  have hm : max 1 (R / ‖z - c‖) = 1 := max_eq_left ((div_le_one hd).mpr hz)
  simp only [rtc_outward, hm, mul_one, sub_add_cancel, one_smul, add_sub_cancel]

theorem rtc_outward_inside (c z : Fin 10 → ℂ) (R : ℝ) (hR : 0 < R)
    (hne : z ≠ c) (hz : ‖z - c‖ ≤ R) (s : unitInterval) :
    ‖rtc_outward c R s z - c‖ ≤ R := by
  have hd : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hm : max 1 (R / ‖z - c‖) = R / ‖z - c‖ :=
    max_eq_right ((le_div_iff₀ hd).mpr (by simpa using hz))
  have hs : 0 ≤ (1 - (s : ℝ)) + (s : ℝ) * (R / ‖z - c‖) :=
    add_nonneg (sub_nonneg.mpr s.2.2) (mul_nonneg s.2.1 (div_nonneg hR.le hd.le))
  rw [rtc_outward, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hm,
    abs_of_nonneg hs, add_mul, mul_assoc, div_mul_cancel₀ _ hd.ne']
  nlinarith [s.2.1, s.2.2]

theorem rtc_outward_end (c z : Fin 10 → ℂ) (R : ℝ) (hR : 0 < R) (hne : z ≠ c) :
    R ≤ ‖rtc_outward c R 1 z - c‖ := by
  have hd : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  by_cases hz : R ≤ ‖z - c‖
  · rwa [rtc_outward_fixed c z R hR hz]
  · have hm : max 1 (R / ‖z - c‖) = R / ‖z - c‖ :=
      max_eq_right ((le_div_iff₀ hd).mpr (by linarith))
    change R ≤ ‖c + ((1 - (1 : ℝ)) + 1 * max 1 (R / ‖z - c‖)) • (z - c) - c‖
    simp only [sub_self, zero_add, one_mul,
      add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hm,
      abs_of_pos (div_pos hR hd), div_mul_cancel₀ _ hd.ne', le_refl]

theorem rtc_outward_continuous (c : Fin 10 → ℂ) (R : ℝ)
    (f : C(unitInterval, Fin 10 → ℂ)) (hf : ∀ t, f t ≠ c) :
    Continuous fun w : unitInterval × unitInterval ↦ rtc_outward c R w.1 (f w.2) := by
  have hn (w : unitInterval × unitInterval) : ‖f w.2 - c‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hf w.2))
  unfold rtc_outward
  exact continuous_const.add
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_const.max (continuous_const.div
          (((f.continuous.comp continuous_snd).sub continuous_const).norm) hn)))).smul
            ((f.continuous.comp continuous_snd).sub continuous_const))

theorem rtc_buffered_ball_avoidance (U : Set (Fin 10 → ℂ)) (hU : IsOpen U)
    (c : Fin 10 → ℂ) (r : ℝ) (hr : 0 < r)
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (hsub : V ⊆ U)
    (hK : Metric.closedBall c r ⊆ V)
    {a b : U} (α : Path a b)
    (ha : r < ‖a.val - c‖) (hb : r < ‖b.val - c‖) :
    ∃ β : Path a b, α.Homotopic β ∧ ∀ t, r < ‖(β t).val - c‖ := by
  obtain ⟨δ, hδ, htube⟩ :=
    (isCompact_closedBall c r).exists_cthickening_subset_open hV hK
  let e := min δ (min (‖a.val - c‖ - r) (‖b.val - c‖ - r))
  have he : 0 < e := lt_min hδ (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))
  let R := r + e / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hrR : r < R := by dsimp [R]; linarith
  have hRa : R ≤ ‖a.val - c‖ := by
    have h : e ≤ ‖a.val - c‖ - r :=
      (min_le_right δ (min (‖a.val - c‖ - r) (‖b.val - c‖ - r))).trans (min_le_left _ _)
    dsimp [R]
    linarith
  have hRb : R ≤ ‖b.val - c‖ := by
    have h : e ≤ ‖b.val - c‖ - r :=
      (min_le_right δ (min (‖a.val - c‖ - r) (‖b.val - c‖ - r))).trans (min_le_right _ _)
    dsimp [R]
    linarith
  have hball : Metric.closedBall c R ⊆ U := by
    apply Set.Subset.trans _ hsub
    apply Set.Subset.trans _ htube
    rw [cthickening_closedBall hδ.le hr.le]
    apply Metric.closedBall_subset_closedBall
    have h : e ≤ δ := min_le_left _ _
    dsimp [R]
    linarith
  obtain ⟨β, hαβ, hβ⟩ := rtc_open_point_avoidance U hU α c
    (fun h ↦ by
      have he : r < 0 := by simpa only [h, sub_self, norm_zero] using ha
      exact (not_lt_of_ge hr.le) he)
    (fun h ↦ by
      have he : r < 0 := by simpa only [h, sub_self, norm_zero] using hb
      exact (not_lt_of_ge hr.le) he)
  let f : C(unitInterval, Fin 10 → ℂ) :=
    ⟨fun t ↦ (β t).val, continuous_subtype_val.comp β.continuous⟩
  have hFU (s t : unitInterval) : rtc_outward c R s (f t) ∈ U := by
    by_cases hz : R ≤ ‖f t - c‖
    · rw [rtc_outward_fixed c (f t) R hR hz]
      exact (β t).property
    · apply hball
      simpa only [Metric.mem_closedBall, dist_eq_norm] using
        rtc_outward_inside c (f t) R hR (hβ t) (by linarith) s
  have hFa (s : unitInterval) : rtc_outward c R s (f 0) = a.val := by
    change rtc_outward c R s (β 0).val = a.val
    rw [β.source]
    exact rtc_outward_fixed c a.val R hR hRa s
  have hFb (s : unitInterval) : rtc_outward c R s (f 1) = b.val := by
    change rtc_outward c R s (β 1).val = b.val
    rw [β.target]
    exact rtc_outward_fixed c b.val R hR hRb s
  let β' : Path a b :=
    { toFun := fun t ↦ ⟨rtc_outward c R 1 (f t), hFU 1 t⟩
      continuous_toFun :=
        ((rtc_outward_continuous c R f hβ).comp
          (continuous_const.prodMk continuous_id)).subtype_mk _
      source' := Subtype.ext (hFa 1)
      target' := Subtype.ext (hFb 1) }
  have hββ' : β.Homotopic β' := by
    refine ⟨{
      toFun := fun w ↦ ⟨rtc_outward c R w.1 (f w.2), hFU w.1 w.2⟩
      continuous_toFun := (rtc_outward_continuous c R f hβ).subtype_mk _
      map_zero_left := fun t ↦ Subtype.ext (by simp [rtc_outward, f])
      map_one_left := fun _ ↦ rfl
      prop' := fun s t ht ↦ ?_ }⟩
    apply Subtype.ext
    rcases ht with rfl | rfl
    · exact (hFa s).trans (congrArg Subtype.val β.source).symm
    · exact (hFb s).trans (congrArg Subtype.val β.target).symm
  exact ⟨β', hαβ.trans hββ',
    fun t ↦ hrR.trans_le (rtc_outward_end c (f t) R hR (hβ t))⟩

end HodgeLean.Foundations.Program
