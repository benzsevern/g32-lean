import HodgeLean.Foundations.Program.HalfTwistTracks
import HodgeLean.Foundations.Program.BraidBridgesThreeRelation

/-! # The elementary half-twist on based loops
The isotopy of the clockwise half-turn track and its action on the explicit loop classes.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Complex Set Topology
namespace HodgeLean.Foundations.Program

/-- Isotopy extension for twelve moving points with the base point fixed, keeping every time
slice and the transport of based families at time one. -/
theorem b66h_isotopy (Q : ℝ → Fin 12 → ℂ) (hQ : Continuous Q)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (Q t))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Q t j ≠ mr_basePoint) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ (t : unitInterval) k, H t (Q 0 k : OnePoint ℂ) = (Q t k : OnePoint ℂ)) ∧
      ∀ (K : C(unitInterval × unitInterval, OnePoint ℂ)),
        (∀ t, K (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ K (t, 1) = (mr_basePoint : OnePoint ℂ)) →
        (∀ t s, K (t, s) ≠ OnePoint.infty ∧ ∀ j, K (t, s) ≠ (Q t j : OnePoint ℂ)) →
        ∀ (Y : Set (OnePoint ℂ)),
          (∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q 1 j : OnePoint ℂ)) → w ∈ Y) →
          ∀ {y : Y} (γ γ' : Path y y), (∀ s, (γ s : OnePoint ℂ) = K (1, s)) →
            (∀ s, (γ' s : OnePoint ℂ) = H 1 (K (0, s))) → γ'.Homotopic γ := by
  have hinjA : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (b65x_adjoin Q t) :=
    fun t ht ↦ b65x_adjoin_injective Q t (hinj t ht) (hB t ht)
  obtain ⟨Φ, E, hE, hbij, h0, htr⟩ :=
    b65x_isotopy_sphere (b65x_adjoin Q) (b65x_adjoin_continuous Q hQ) hinjA
  have hcont : ∀ t : unitInterval, Continuous (OnePoint.map (Φ t)) := by
    intro t
    have h : OnePoint.map (Φ t) = fun w ↦ (E (t, w)).2 := by
      funext w; rw [hE]
    rw [h]
    exact continuous_snd.comp (E.continuous.comp (continuous_const.prodMk continuous_id))
  let H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ := fun t ↦
    (hcont t).homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (b65x_map_bijective (hbij t)))
  have hH : ∀ t w, H t w = OnePoint.map (Φ t) w := fun t w ↦ rfl
  have htrA : ∀ (t : unitInterval) (j : Fin 13), Φ t (b65x_adjoin Q 0 j) = b65x_adjoin Q t j :=
    fun t j ↦ htr t t.2 j
  refine ⟨H, ?_, ?_, fun t ↦ rfl, fun t ↦ ?_, fun t k ↦ ?_,
    fun K hKb hKa Y hY y γ γ' hγ hγ' ↦ ?_⟩
  · have h : (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) = fun q ↦ (E q).2 := by
      funext q; rw [hH, hE]
    rw [h]
    exact continuous_snd.comp E.continuous
  · ext w
    rw [hH]
    induction w using OnePoint.rec with
    | infty => rfl
    | coe z => simp [h0]
  · rw [hH, OnePoint.map_some]
    have := htrA t (Fin.last 12)
    rw [b65x_adjoin_last, b65x_adjoin_last] at this
    rw [this]
  · rw [hH, OnePoint.map_some]
    have := htrA t k.castSucc
    rw [b65x_adjoin_cast, b65x_adjoin_cast] at this
    rw [this]
  · apply b65x_family_end (b65x_adjoin Q) Φ E hE hbij h0 htr {j | j.val < 12} (Fin.last 12)
      (fun t _ ↦ by rw [b65x_adjoin_last, b65x_adjoin_last]) K
    · intro t
      rw [b65x_adjoin_last]; exact hKb t
    · intro t s
      refine ⟨(hKa t s).1, fun j hj ↦ ?_⟩
      have h := (hKa t s).2 ⟨j.val, hj⟩
      simpa [b65x_adjoin, dite_eq_left (show j.val < 12 from hj)] using h
    · intro w hw hj
      apply hY w hw
      intro j
      have h := hj j.castSucc (by simp)
      rwa [b65x_adjoin_cast] at h
    · exact hγ
    · intro s; rw [hγ']; rfl

/-! ## The clockwise half-turn -/

/-- Real coordinate of a mark. -/
abbrev b66h_x (k : Fin 12) : ℝ := (b66h_markZ k : ℝ)

theorem b66h_track_im (j : Fin 11) (t : ℝ) (k : Fin 12) :
    (b66h_track j (-1) t k).im =
      if k = j.castSucc ∨ k = j.succ then
        (b66h_x k - (b66h_x j.castSucc + b66h_x j.succ) / 2) * Real.sin (-(Real.pi * t))
      else 0 := by
  split_ifs with hk
  · rw [b66h_track_moving j (-1) t k hk, b66h_marks_eq, b66h_marks_eq, b66h_marks_eq,
      show ((-1 : ℝ) : ℂ) * Real.pi * Complex.I * (t : ℂ) = ((-(Real.pi * t) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, Complex.sub_re, Complex.div_ofNat_im, Complex.div_ofNat_re, Complex.add_re,
      Complex.I_re, Complex.I_im, Complex.mul_re]
    ring
  · rw [b66h_track_fixed j (-1) t k hk, b65x_marks_im]

theorem b66h_track_sub_norm (j : Fin 11) (t : ℝ) (k : Fin 12)
    (hk : k = j.castSucc ∨ k = j.succ) :
    ‖b66h_track j (-1) t k - (mr_marks j.castSucc + mr_marks j.succ) / 2‖ =
      ‖mr_marks k - (mr_marks j.castSucc + mr_marks j.succ) / 2‖ := by
  rw [b66h_track_moving j (-1) t k hk, add_sub_cancel_left, norm_mul, b66h_norm_exp, mul_one]

theorem b66h_markZ_facts : ∀ j : Fin 11,
    b66h_markZ j.castSucc < b66h_markZ j.succ ∧ b66h_markZ j.succ - b66h_markZ j.castSucc ≤ 3 ∧
    -12 ≤ b66h_markZ j.castSucc ∧ b66h_markZ j.succ ≤ 1 := by
  decide

theorem b66h_markZ_gap : ∀ (j : Fin 11) (m : Fin 12), m ≠ j.castSucc → m ≠ j.succ →
    b66h_markZ m + 1 ≤ b66h_markZ j.castSucc ∨ b66h_markZ j.succ + 1 ≤ b66h_markZ m := by
  decide

theorem b66h_markZ_range : ∀ m : Fin 12, -12 ≤ b66h_markZ m ∧ b66h_markZ m ≤ 1 := by
  decide

theorem b66h_sin_nonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ Real.sin (Real.pi * t) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, ht.1])
    (by nlinarith [Real.pi_pos, ht.2])

/-- Imaginary parts: the left mark runs over the top, every other point stays weakly below. -/
theorem b66h_im_left (j : Fin 11) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (b66h_track j (-1) t j.castSucc).im := by
  rw [b66h_track_im, ite_eq_left (Or.inl rfl), Real.sin_neg]
  have := (b66h_markZ_facts j).1
  have h : (b66h_x j.castSucc : ℝ) < b66h_x j.succ := by exact_mod_cast this
  nlinarith [b66h_sin_nonneg t ht]

theorem b66h_im_other (j : Fin 11) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 12)
    (hk : k ≠ j.castSucc) : (b66h_track j (-1) t k).im ≤ 0 := by
  rw [b66h_track_im]
  split_ifs with h
  · have hks : k = j.succ := h.resolve_left hk
    subst hks
    rw [Real.sin_neg]
    have := (b66h_markZ_facts j).1
    have h' : (b66h_x j.castSucc : ℝ) < b66h_x j.succ := by exact_mod_cast this
    nlinarith [b66h_sin_nonneg t ht]
  · exact le_rfl

theorem b66h_im_abs (j : Fin 11) (t : ℝ) (k : Fin 12) :
    |(b66h_track j (-1) t k).im| ≤ 3 / 2 := by
  rw [b66h_track_im]
  split_ifs with h
  · obtain ⟨h1, h2, -, -⟩ := b66h_markZ_facts j
    have h1' : (b66h_x j.castSucc : ℝ) < b66h_x j.succ := by exact_mod_cast h1
    have h2' : (b66h_x j.succ : ℝ) - b66h_x j.castSucc ≤ 3 := by exact_mod_cast h2
    rw [abs_mul]
    have hs := Real.abs_sin_le_one (-(Real.pi * t))
    have hd : |b66h_x k - (b66h_x j.castSucc + b66h_x j.succ) / 2| ≤ 3 / 2 := by
      rcases h with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
    calc _ ≤ 3 / 2 * 1 := mul_le_mul hd hs (abs_nonneg _) (by norm_num)
      _ = 3 / 2 := by ring
  · norm_num

theorem b66h_Q_continuous (j : Fin 11) : Continuous (b66h_track j (-1)) :=
  continuous_pi fun k ↦ (b66h_track_continuous_body j (-1)).comp
    (continuous_id.prodMk continuous_const)

theorem b66h_Q_ne_base (j : Fin 11) (t : ℝ) (k : Fin 12) :
    b66h_track j (-1) t k ≠ mr_basePoint := by
  intro h
  have him := congrArg Complex.im h
  have hb := b66h_im_abs j t k
  rw [him] at hb
  simp [mr_basePoint, mr_centre] at hb
  norm_num [abs_of_pos] at hb

/-- The radial segment to the left mark is never blocked. -/
theorem b66h_seg_left (j : Fin 11) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (b : Fin 12)
    (hb : b ≠ j.castSucc) (μ : ℝ) (hμ : μ ∈ Icc (0 : ℝ) 1) :
    mr_basePoint + (μ : ℂ) * (b66h_track j (-1) t j.castSucc - mr_basePoint) ≠
      b66h_track j (-1) t b := by
  intro h
  have him := congrArg Complex.im h
  have h0 := b66h_im_left j t ht
  have h1 := b66h_im_other j t ht b hb
  have hbase : mr_basePoint.im = 10 := by simp [mr_basePoint, mr_centre]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.sub_im, hbase] at him
  have hμ1 : μ = 1 := by nlinarith [hμ.1, hμ.2]
  subst hμ1
  have he : b66h_track j (-1) t j.castSucc = b66h_track j (-1) t b := by
    rw [← h]; push_cast; ring
  exact hb (b66h_track_injective_body j (-1) t he).symm

/-! ## Fixed loops -/

theorem b66h_centre_eq (j : Fin 11) : (mr_marks j.castSucc + mr_marks j.succ) / 2 =
    (((b66h_x j.castSucc + b66h_x j.succ) / 2 : ℝ) : ℂ) := by
  rw [b66h_marks_eq, b66h_marks_eq]; push_cast; ring

theorem b66h_moving_norm (j : Fin 11) (t : ℝ) (k : Fin 12) (hk : k = j.castSucc ∨ k = j.succ) :
    ‖b66h_track j (-1) t k - (mr_marks j.castSucc + mr_marks j.succ) / 2‖ =
      (b66h_x j.succ - b66h_x j.castSucc) / 2 := by
  rw [b66h_track_sub_norm j t k hk, b66h_centre_eq, b66h_marks_eq, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have h1 : (b66h_x j.castSucc : ℝ) < b66h_x j.succ := by exact_mod_cast (b66h_markZ_facts j).1
  rcases hk with rfl | rfl
  · rw [abs_of_neg (by linarith)]; ring
  · rw [abs_of_pos (by linarith)]; ring

/-- The explicit lasso of a fixed mark stays outside the circle of the two moving marks. -/
theorem b66h_lasso_far (j : Fin 11) (m : Fin 12) (hm1 : m ≠ j.castSucc) (hm2 : m ≠ j.succ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (b66h_x j.succ - b66h_x j.castSucc) / 2 <
      ‖mr_lasso (mr_marks m) s - (mr_marks j.castSucc + mr_marks j.succ) / 2‖ := by
  obtain ⟨h1, h2, -, -⟩ := b66h_markZ_facts j
  have h1' : (b66h_x j.castSucc : ℝ) < b66h_x j.succ := by exact_mod_cast h1
  have h2' : (b66h_x j.succ : ℝ) - b66h_x j.castSucc ≤ 3 := by exact_mod_cast h2
  have hg : b66h_x m + 1 ≤ b66h_x j.castSucc ∨ b66h_x j.succ + 1 ≤ b66h_x m := by
    rcases b66h_markZ_gap j m hm1 hm2 with h | h
    · left; unfold b66h_x; exact_mod_cast h
    · right; unfold b66h_x; exact_mod_cast h
  have hr : -12 ≤ b66h_x m ∧ b66h_x m ≤ 1 := by
    obtain ⟨a, b⟩ := b66h_markZ_range m
    exact ⟨by unfold b66h_x; exact_mod_cast a, by unfold b66h_x; exact_mod_cast b⟩
  set xa := b66h_x j.castSucc
  set xb := b66h_x j.succ
  set xm := b66h_x m
  rw [b66h_centre_eq, b65x_mr_lasso_shape]
  rcases b65x_shape_cases (mr_marks m) (I / 4) s hs with ⟨μ, hμ, he⟩ | he
  · rw [he]
    set z := mr_basePoint + (μ : ℂ) * (mr_marks m + I / 4 - mr_basePoint) -
      (((xa + xb) / 2 : ℝ) : ℂ)
    have hz : z = ((-11 / 2 + μ * (xm + 11 / 2) - (xa + xb) / 2 : ℝ) : ℂ) +
        ((10 - 39 / 4 * μ : ℝ) : ℂ) * I := by
      simp only [z, mr_basePoint, mr_centre, xm, b66h_marks_eq]; push_cast; ring
    have him : z.im = 10 - 39 / 4 * μ := by rw [hz]; simp
    have hre : z.re = -11 / 2 + μ * (xm + 11 / 2) - (xa + xb) / 2 := by rw [hz]; simp
    by_cases hi : 3 / 2 < 10 - 39 / 4 * μ
    · calc (xb - xa) / 2 < z.im := by rw [him]; linarith
        _ ≤ |z.im| := le_abs_self _
        _ ≤ ‖z‖ := Complex.abs_im_le_norm _
    · push Not at hi
      have hn := Complex.abs_re_le_norm z
      rw [hre] at hn
      have hμ' : 1 - μ ≤ 5 / 39 := by linarith
      have hp1 : 0 ≤ (1 - μ) * (xm + 11 / 2 + 13 / 2) := mul_nonneg (by linarith [hμ.2])
        (by linarith)
      have hp2 : 0 ≤ (1 - μ) * (13 / 2 - (xm + 11 / 2)) := mul_nonneg (by linarith [hμ.2])
        (by linarith)
      rcases hg with hg | hg
      · have hk : (xb - xa) / 2 < -(-11 / 2 + μ * (xm + 11 / 2) - (xa + xb) / 2) := by
          nlinarith
        exact lt_of_lt_of_le hk ((neg_le_abs _).trans hn)
      · have hk : (xb - xa) / 2 < -11 / 2 + μ * (xm + 11 / 2) - (xa + xb) / 2 := by
          nlinarith
        exact lt_of_lt_of_le hk ((le_abs_self _).trans hn)
  · have hI : ‖I / 4‖ = 1 / 4 := by rw [norm_div, Complex.norm_I]; norm_num
    rw [hI] at he
    have hmc : ‖mr_marks m - (((xa + xb) / 2 : ℝ) : ℂ)‖ = |xm - (xa + xb) / 2| := by
      rw [b66h_marks_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have tri := norm_sub_le_norm_sub_add_norm_sub (mr_marks m)
      (b65x_shape (mr_marks m) (I / 4) s) (((xa + xb) / 2 : ℝ) : ℂ)
    rw [hmc, norm_sub_rev, he] at tri
    rcases hg with hg | hg
    · have := neg_le_abs (xm - (xa + xb) / 2)
      linarith
    · have := le_abs_self (xm - (xa + xb) / 2)
      linarith

theorem b66h_curve_ne_moving (j : Fin 11) (m : Fin 13) (hm1 : m ≠ j.castSucc.castSucc)
    (hm2 : m ≠ j.succ.castSucc) (s : unitInterval) (t : ℝ) (k : Fin 12)
    (hk : k = j.castSucc ∨ k = j.succ) :
    mr_curve m s ≠ (b66h_track j (-1) t k : OnePoint ℂ) := by
  intro h
  unfold mr_curve at h
  split_ifs at h with hm
  · have h' := OnePoint.coe_injective h
    have hf := b66h_lasso_far j ⟨m.val, hm⟩ (fun e ↦ hm1 (Fin.ext (by simp [← e])))
      (fun e ↦ hm2 (Fin.ext (by simp [← e]))) s ⟨s.2.1, s.2.2⟩
    rw [h', b66h_moving_norm j t k hk] at hf
    exact lt_irrefl _ hf
  · have h' := OnePoint.coe_injective h
    have h1 := b65x_outer_norm s
    rw [h'] at h1
    have h2 : ‖b66h_track j (-1) t k + 11 / 2‖ ≤
        ‖(mr_marks j.castSucc + mr_marks j.succ) / 2 + 11 / 2‖ +
          ‖b66h_track j (-1) t k - (mr_marks j.castSucc + mr_marks j.succ) / 2‖ := by
      have := norm_add_le ((mr_marks j.castSucc + mr_marks j.succ) / 2 + 11 / 2)
        (b66h_track j (-1) t k - (mr_marks j.castSucc + mr_marks j.succ) / 2)
      rwa [show (mr_marks j.castSucc + mr_marks j.succ) / 2 + 11 / 2 +
        (b66h_track j (-1) t k - (mr_marks j.castSucc + mr_marks j.succ) / 2) =
        b66h_track j (-1) t k + 11 / 2 by ring] at this
    rw [b66h_moving_norm j t k hk, b66h_centre_eq,
      show (((b66h_x j.castSucc + b66h_x j.succ) / 2 : ℝ) : ℂ) + 11 / 2 =
        (((b66h_x j.castSucc + b66h_x j.succ) / 2 + 11 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at h2
    obtain ⟨h3, -, h4, h5⟩ := b66h_markZ_facts j
    have h3' : (b66h_x j.castSucc : ℝ) < b66h_x j.succ := by exact_mod_cast h3
    have h4' : (-12 : ℝ) ≤ b66h_x j.castSucc := by unfold b66h_x; exact_mod_cast h4
    have h5' : (b66h_x j.succ : ℝ) ≤ 1 := by unfold b66h_x; exact_mod_cast h5
    have := abs_le.mpr (show -(13 / 2 - (b66h_x j.succ - b66h_x j.castSucc) / 2) ≤
        (b66h_x j.castSucc + b66h_x j.succ) / 2 + 11 / 2 ∧
        (b66h_x j.castSucc + b66h_x j.succ) / 2 + 11 / 2 ≤
          13 / 2 - (b66h_x j.succ - b66h_x j.castSucc) / 2 by constructor <;> linarith)
    linarith

/-! ## Restriction to the punctured sphere -/

theorem b66h_mem_iff (w : OnePoint ℂ) :
    w ∈ b6t_punctured mr_base ↔ w ≠ OnePoint.infty ∧ ∀ k : Fin 12, w ≠ (mr_marks k : OnePoint ℂ) := by
  refine ⟨fun h ↦ ⟨fun hw ↦ h ⟨Fin.last 12, hw ▸ rfl⟩, fun k hw ↦ h ⟨k.castSucc, ?_⟩⟩,
    fun h ↦ b65x_mem_punctured h.1 h.2⟩
  rw [b65x_branch_cast, hw]

theorem b66h_restrict (e : OnePoint ℂ ≃ₜ OnePoint ℂ) (heI : e OnePoint.infty = OnePoint.infty)
    (σ : Equiv.Perm (Fin 12)) (heQ : ∀ k, e (mr_marks k : OnePoint ℂ) = (mr_marks (σ k) : OnePoint ℂ))
    (w : OnePoint ℂ) : w ∈ b6t_punctured mr_base ↔ e w ∈ b6t_punctured mr_base := by
  rw [b66h_mem_iff, b66h_mem_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h ↦ h1 (e.injective (h.trans heI.symm)), fun k h ↦ ?_⟩
    obtain ⟨k', rfl⟩ := σ.surjective k
    exact h2 k' (e.injective (h.trans (heQ k').symm))
  · rintro ⟨h1, h2⟩
    refine ⟨fun h ↦ h1 (by rw [h, heI]), fun k h ↦ h2 (σ k) (by rw [h, heQ])⟩

theorem b66h_mapOfEq_fromPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (p : Path x x) :
    FundamentalGroup.mapOfEq f h (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((p.map f.continuous).cast h.symm h.symm)) :=
  FundamentalGroup.mapOfEq_apply f h _

/-- The based loop traced by an explicit curve. -/
def b66h_curvePath (m : Fin 13) : Path b63gP_basePoint b63gP_basePoint :=
  b65x_mkPath _ b63gP_basePoint (mr_curve m ·)
    ((mr_curve_continuous _).comp continuous_subtype_val)
    (fun s ↦ (mr_curve_avoids mr_base b63gP_s₀.property m s).1)
    (mr_curve_zero _) (mr_curve_one _)

theorem b66h_curvePath_apply (m : Fin 13) (s : unitInterval) :
    (b66h_curvePath m s : OnePoint ℂ) = mr_curve m s := rfl

/-- A homeomorphism carrying the explicit curve `m` to a loop homotopic to the explicit curve
`m'` sends the class of `m` to the class of `m'`. -/
theorem b66h_class (h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base)
    (hb : h b63gP_basePoint = b63gP_basePoint) (m m' : Fin 13)
    (hhom : ∀ γ : Path b63gP_basePoint b63gP_basePoint,
      (∀ s, (γ s : OnePoint ℂ) = (h (b66h_curvePath m s) : OnePoint ℂ)) →
        γ.Homotopic (b66h_curvePath m')) :
    FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb (b63gP_loops m) = b63gP_loops m' := by
  have h1 := b65x_loops_eq m (b66h_curvePath m) (fun s ↦ rfl)
  have h2 := b65x_loops_eq m' (b66h_curvePath m') (fun s ↦ rfl)
  calc _ = FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (b66h_curvePath m))) := by rw [← h1]; rfl
    _ = _ := b66h_mapOfEq_fromPath _ hb _
    _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (b66h_curvePath m')) :=
        congrArg _ (Path.Homotopic.Quotient.eq.mpr (hhom _ fun s ↦ rfl))
    _ = _ := by rw [← h2]; rfl

/-! ## The moving mark with an unblocked radial lasso -/

/-- Along a motion starting at the marks, a point whose radial segment is never blocked carries
its explicit lasso to the explicit lasso of the mark it reaches. -/
theorem b66h_radial_class (Q : ℝ → Fin 12 → ℂ) (hQ : Continuous Q) (hQ0 : Q 0 = mr_marks)
    (e : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (heB : e (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ))
    (heI : e OnePoint.infty = OnePoint.infty)
    (heQ : ∀ j, e (Q 0 j : OnePoint ℂ) = (Q 1 j : OnePoint ℂ))
    (hfam : ∀ (K : C(unitInterval × unitInterval, OnePoint ℂ)),
        (∀ t, K (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ K (t, 1) = (mr_basePoint : OnePoint ℂ)) →
        (∀ t s, K (t, s) ≠ OnePoint.infty ∧ ∀ j, K (t, s) ≠ (Q t j : OnePoint ℂ)) →
        ∀ (Y : Set (OnePoint ℂ)),
          (∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q 1 j : OnePoint ℂ)) → w ∈ Y) →
          ∀ {y : Y} (γ γ' : Path y y), (∀ s, (γ s : OnePoint ℂ) = K (1, s)) →
            (∀ s, (γ' s : OnePoint ℂ) = e (K (0, s))) → γ'.Homotopic γ)
    (hQ1 : ∀ i, ∃ j, Q 1 j = mr_marks i) (k : Fin 12)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b, b ≠ k → ∀ μ ∈ Icc (0 : ℝ) 1,
      mr_basePoint + (μ : ℂ) * (Q t k - mr_basePoint) ≠ Q t b)
    (hBk : ∀ t ∈ Icc (0 : ℝ) 1, Q t k ≠ mr_basePoint)
    (m : Fin 12) (hm : Q 1 k = mr_marks m)
    {y : b6t_punctured mr_base} (hy : (y : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ))
    (γ γ' : Path y y) (hγ : ∀ s, (γ s : OnePoint ℂ) = e (mr_curve k.castSucc s))
    (hγ' : ∀ s, (γ' s : OnePoint ℂ) = mr_curve m.castSucc s) : γ.Homotopic γ' := by
  have hY : ∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q 1 j : OnePoint ℂ)) →
      w ∈ b6t_punctured mr_base := by
    intro w hw hj
    apply b65x_mem_punctured hw
    intro i
    obtain ⟨j, hj'⟩ := hQ1 i
    rw [← hj']; exact hj j
  obtain ⟨ρ0, hρ0, hvalid⟩ := b65x_radial_valid Q hQ k hseg hBk
  set N1 := ‖mr_basePoint - mr_marks k‖
  set N2 := ‖mr_basePoint - mr_marks m‖
  set ρ := min ρ0 (min ((1/4) / (N1 + 1)) ((1/4) / (N2 + 1)))
  have hN1 : 0 ≤ N1 := norm_nonneg _
  have hN2 : 0 ≤ N2 := norm_nonneg _
  have hρpos : 0 < ρ := by positivity
  have hρle : ρ ≤ ρ0 := min_le_left _ _
  have hρ1 : ρ * N1 ≤ 1/4 := by
    have h : ρ ≤ (1/4) / (N1 + 1) := (min_le_right _ _).trans (min_le_left _ _)
    calc ρ * N1 ≤ (1/4) / (N1 + 1) * N1 := mul_le_mul_of_nonneg_right h hN1
      _ ≤ 1/4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have hρ2 : ρ * N2 ≤ 1/4 := by
    have h : ρ ≤ (1/4) / (N2 + 1) := (min_le_right _ _).trans (min_le_right _ _)
    calc ρ * N2 ≤ (1/4) / (N2 + 1) * N2 := mul_le_mul_of_nonneg_right h hN2
      _ ≤ 1/4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have hval := hvalid ρ hρpos hρle
  let Rf : unitInterval × unitInterval → ℂ := fun q' ↦
    b65x_shape (Q q'.1 k) ((ρ : ℂ) * (mr_basePoint - Q q'.1 k)) q'.2
  have hRc : Continuous Rf := by
    have hq : Continuous fun q' : unitInterval × unitInterval ↦ Q q'.1 k :=
      ((continuous_apply k).comp hQ).comp (continuous_subtype_val.comp continuous_fst)
    exact b65x_shape_continuous.comp (hq.prodMk
      ((continuous_const.mul (continuous_const.sub hq)).prodMk
        (continuous_subtype_val.comp continuous_snd)))
  let R : C(unitInterval × unitInterval, OnePoint ℂ) :=
    ⟨fun q' ↦ (Rf q' : OnePoint ℂ), OnePoint.continuous_coe.comp hRc⟩
  have hRb : ∀ t, R (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ R (t, 1) = (mr_basePoint : OnePoint ℂ) :=
    fun t ↦ ⟨congrArg _ (b65x_shape_zero _ _), congrArg _ (b65x_shape_one _ _)⟩
  have hRa : ∀ t s, R (t, s) ≠ OnePoint.infty ∧ ∀ j, R (t, s) ≠ (Q t j : OnePoint ℂ) := by
    intro t s
    refine ⟨OnePoint.coe_ne_infty _, fun j h ↦ ?_⟩
    exact hval t t.2 s ⟨s.2.1, s.2.2⟩ j (OnePoint.coe_injective h)
  have he_mem : ∀ w : ℂ, (∀ j, w ≠ Q 0 j) → e (w : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    intro w hw
    apply hY
    · intro h; rw [← heI] at h; exact OnePoint.coe_ne_infty _ (e.injective h)
    · intro j h; rw [← heQ j] at h; exact hw j (OnePoint.coe_injective (e.injective h))
  let Pe0 : Path y y := b65x_mkPath _ y (fun s ↦ e (Rf (0, s) : OnePoint ℂ))
    (e.continuous.comp (OnePoint.continuous_coe.comp
      (hRc.comp (continuous_const.prodMk continuous_id))))
    (fun s ↦ he_mem _ fun j h ↦ hval 0 (by simp) s ⟨s.2.1, s.2.2⟩ j h)
    (by simp only [Rf, Set.Icc.coe_zero, b65x_shape_zero]; rw [heB, hy])
    (by simp only [Rf, Set.Icc.coe_one, b65x_shape_one]; rw [heB, hy])
  let P1 : Path y y := b65x_mkPath _ y (fun s ↦ (Rf (1, s) : OnePoint ℂ))
    (OnePoint.continuous_coe.comp (hRc.comp (continuous_const.prodMk continuous_id)))
    (fun s ↦ hY _ (OnePoint.coe_ne_infty _) fun j h ↦
      hval 1 (by simp) s ⟨s.2.1, s.2.2⟩ j (OnePoint.coe_injective h))
    (by simp only [Rf, Set.Icc.coe_zero, b65x_shape_zero]; rw [hy])
    (by simp only [Rf, Set.Icc.coe_one, b65x_shape_one]; rw [hy])
  have h1 : Pe0.Homotopic P1 := hfam R hRb hRa _ hY P1 Pe0 (fun s ↦ rfl) (fun s ↦ rfl)
  obtain ⟨F0, hF0c, hF00, hF01, hF0b, hF0a⟩ := b65x_static_end k ρ hρpos hρ1
  have h0 : Pe0.Homotopic γ := by
    apply b65x_transport_static (Q 0) (Q 1) e heB heI heQ F0 hF0c hF0b
      (fun t s j ↦ by rw [hQ0]; exact hF0a t s j) _ hY hy
    · intro s
      change e (Rf (0, s) : OnePoint ℂ) = e (F0 (0, s) : OnePoint ℂ)
      rw [hF00]
      simp only [Rf, Set.Icc.coe_zero, hQ0]
    · intro s; rw [hγ, hF01, b65x_mr_curve_cast]
  obtain ⟨F1, hF1c, hF10, hF11, hF1b, hF1a⟩ := b65x_static_end m ρ hρpos hρ2
  have h2 : P1.Homotopic γ' := by
    apply b65x_homotopic_of_family P1 γ' (fun q' ↦ (F1 q' : OnePoint ℂ))
      (OnePoint.continuous_coe.comp hF1c)
    · intro q'
      exact b65x_mem_punctured (OnePoint.coe_ne_infty _) fun i h ↦
        hF1a q'.1 q'.2 i (OnePoint.coe_injective h)
    · intro s
      change (F1 (0, s) : OnePoint ℂ) = (Rf (1, s) : OnePoint ℂ)
      rw [hF10]
      simp only [Rf, Set.Icc.coe_one]
      rw [hm]
    · intro s; rw [hF11, hγ', b65x_mr_curve_cast]
    · intro t; rw [(hF1b t).1, (hF1b t).2, hy]; exact ⟨rfl, rfl⟩
  exact h0.symm.trans (h1.trans h2)

/-! ## The relation -/

theorem b66h_rel_solve {G : Type*} [Group G] (j : Fin 11) (f : Fin 13 → G) (X : G)
    (hf : (List.ofFn f).reverse.prod = 1)
    (hg : (List.ofFn fun m : Fin 13 ↦ if m.val = j.val + 1 then X
      else if m.val = j.val then f j.succ.castSucc else f m).reverse.prod = 1) :
    X = f j.succ.castSucc * f j.castSucc.castSucc * (f j.succ.castSucc)⁻¹ := by
  rw [b65x_prod13_rev] at hf hg
  have h := hg.trans hf.symm
  apply eq_mul_inv_of_mul_eq
  fin_cases j <;> simp at h ⊢ <;> first
    | exact h
    | (rw [← mul_assoc, ← mul_assoc, mul_left_inj] at h; exact h)
    | (simp only [← mul_assoc, mul_left_inj] at h; exact h)

/-! ## The elementary half-twist -/

theorem b66h_index_facts (i : Fin 12) (hi : i ≠ 0) :
    let j : Fin 11 := ⟨11 - i.val, by omega⟩
    i.castSucc.rev = j.succ.castSucc ∧ i.succ.rev = j.castSucc.castSucc ∧
      ∀ k : Fin 13, k ≠ i.castSucc → k ≠ i.succ →
        k.rev ≠ j.castSucc.castSucc ∧ k.rev ≠ j.succ.castSucc := by
  have hi' : i.val ≠ 0 := fun h ↦ hi (Fin.ext h)
  refine ⟨Fin.ext ?_, Fin.ext ?_, fun k h1 h2 ↦ ⟨fun h ↦ h2 (Fin.ext ?_), fun h ↦ h1 (Fin.ext ?_)⟩⟩
  · simp [Fin.rev] <;> omega
  · simp [Fin.rev] <;> omega
  · have := congrArg Fin.val h; simp [Fin.rev] at this ⊢ <;> omega
  · have := congrArg Fin.val h; simp [Fin.rev] at this ⊢ <;> omega

theorem b66h_half_twist_body (i : Fin 12) (hi : i ≠ 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ t k, H t (mr_marks k : OnePoint ℂ) =
        (b66h_track ⟨11 - i.val, by omega⟩ ε t k : OnePoint ℂ)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ k, MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k))) =
            b4_braid i.castSucc i.succ b66h_loop k := by
  obtain ⟨hrb, hra, hro⟩ := b66h_index_facts i hi
  set j : Fin 11 := ⟨11 - i.val, by omega⟩ with hj
  set Q := b66h_track j (-1) with hQdef
  have hne : j.castSucc ≠ j.succ := Fin.castSucc_lt_succ.ne
  have hQ0 : Q 0 = mr_marks := (b66h_track_endpoints_body j (-1) (Or.inr rfl)).1
  have hQ1 : Q 1 = mr_marks ∘ Equiv.swap j.castSucc j.succ :=
    (b66h_track_endpoints_body j (-1) (Or.inr rfl)).2
  obtain ⟨H, hHc, hH0, hHI, hHB, hHQ, hfam⟩ := b66h_isotopy Q (b66h_Q_continuous j)
    (fun t _ ↦ b66h_track_injective_body j (-1) t) (fun t _ k ↦ b66h_Q_ne_base j t k)
  have hHQ' : ∀ (t : unitInterval) k, H t (mr_marks k : OnePoint ℂ) = (Q t k : OnePoint ℂ) := by
    intro t k
    rw [← hHQ t k, hQ0]
  have heQ1 : ∀ k, H 1 (mr_marks k : OnePoint ℂ) =
      (mr_marks (Equiv.swap j.castSucc j.succ k) : OnePoint ℂ) := by
    intro k
    rw [hHQ' 1 k]
    change ((Q 1 k : ℂ) : OnePoint ℂ) = _
    rw [hQ1]; rfl
  have hfam1 := hfam
  let h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base :=
    (H 1).subtype (b66h_restrict (H 1) (hHI 1) _ heQ1)
  have hb : h b63gP_basePoint = b63gP_basePoint := Subtype.ext (hHB 1)
  have hY : ∀ w, w ≠ OnePoint.infty → (∀ k, w ≠ (Q 1 k : OnePoint ℂ)) →
      w ∈ b6t_punctured mr_base := by
    intro w hw hk
    apply b65x_mem_punctured hw
    intro k
    have := hk (Equiv.swap j.castSucc j.succ k)
    rwa [hQ1, Function.comp_apply, Equiv.swap_apply_self] at this
  -- fixed loops
  have hfix : ∀ m : Fin 13, m ≠ j.castSucc.castSucc → m ≠ j.succ.castSucc →
      FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb (b63gP_loops m) = b63gP_loops m := by
    intro m hm1 hm2
    apply b66h_class h hb m m
    intro γ hγ
    let K : C(unitInterval × unitInterval, OnePoint ℂ) :=
      ⟨fun q ↦ mr_curve m q.2, (mr_curve_continuous m).comp (continuous_subtype_val.comp
        continuous_snd)⟩
    apply hfam1 K (fun t ↦ ⟨mr_curve_zero m, mr_curve_one m⟩) _ _ hY (b66h_curvePath m) γ
      (fun s ↦ rfl) (fun s ↦ hγ s)
    intro t s
    have hmem := (b66h_mem_iff _).mp (mr_curve_avoids mr_base b63gP_s₀.property m s).1
    refine ⟨hmem.1, fun k ↦ ?_⟩
    by_cases hk : k = j.castSucc ∨ k = j.succ
    · exact b66h_curve_ne_moving j m hm1 hm2 s t k hk
    · change mr_curve m s ≠ ((b66h_track j (-1) t k : ℂ) : OnePoint ℂ)
      rw [b66h_track_fixed j (-1) t k hk]
      exact hmem.2 k
  -- the left mark
  have hA : FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb (b63gP_loops j.castSucc.castSucc) =
      b63gP_loops j.succ.castSucc := by
    apply b66h_class h hb
    intro γ hγ
    refine b66h_radial_class Q (b66h_Q_continuous j) hQ0 (H 1) (hHB 1) (hHI 1)
      (fun k ↦ by simpa using hHQ 1 k) hfam1 (fun k ↦ ⟨Equiv.swap j.castSucc j.succ k, by
        rw [hQ1, Function.comp_apply, Equiv.swap_apply_self]⟩) j.castSucc
      (fun t ht b hb' μ hμ ↦ b66h_seg_left j t ht b hb' μ hμ)
      (fun t _ ↦ b66h_Q_ne_base j t _) j.succ ?_ rfl γ (b66h_curvePath j.succ.castSucc)
      (fun s ↦ hγ s) (fun s ↦ rfl)
    rw [hQ1, Function.comp_apply, Equiv.swap_apply_left]
  -- the right mark, from the relation
  have hrel : (List.ofFn b63gP_loops).reverse.prod = 1 :=
    mr_loops_product mr_base b63gP_s₀.property b63gP_basePoint b63gP_loops
      (fun i ↦ (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec)
  set φ := FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb
  have hrelφ : (List.ofFn fun m : Fin 13 ↦ if m.val = j.val + 1 then φ (b63gP_loops j.succ.castSucc)
      else if m.val = j.val then b63gP_loops j.succ.castSucc else b63gP_loops m).reverse.prod = 1 := by
    have h1 := congrArg φ hrel
    rw [map_one, map_list_prod, List.map_reverse, List.map_ofFn] at h1
    convert h1 using 3
    congr 1
    funext m
    simp only [Function.comp_apply]
    split_ifs with h2 h3
    · congr 2; exact Fin.ext (by simp [h2])
    · rw [show m = j.castSucc.castSucc from Fin.ext (by simp [h3]), hA]
    · rw [hfix m (fun e ↦ h3 (by simp [e])) (fun e ↦ h2 (by simp [e]))]
  have hB := b66h_rel_solve j b63gP_loops _ hrel hrelφ
  refine ⟨-1, Or.inr rfl, H, hHc, hH0, hHI, hHB, hHQ', h, fun z ↦ rfl, hb, fun k ↦ ?_⟩
  simp only [b66h_loop, MulOpposite.unop_op, map_inv]
  by_cases hk1 : k = i.castSucc
  · subst hk1
    rw [hrb, hB]
    simp only [b4_braid, Function.update_self, b66h_loop, hrb, hra]
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul, MulOpposite.unop_inv]
    group
  by_cases hk2 : k = i.succ
  · subst hk2
    rw [hra, hA]
    simp only [b4_braid, Function.update_of_ne (Ne.symm Fin.castSucc_lt_succ.ne),
      Function.comp_apply, Equiv.swap_apply_right, b66h_loop, hrb]
  · obtain ⟨h1, h2⟩ := hro k hk1 hk2
    rw [hfix _ h1 h2]
    simp only [b4_braid, Function.update_of_ne hk1, Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne hk1 hk2, b66h_loop]

end HodgeLean.Foundations.Program
