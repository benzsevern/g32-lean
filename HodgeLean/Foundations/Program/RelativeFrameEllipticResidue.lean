import HodgeLean.Foundations.Program.RelativeFrameEllipticForms

/-! # A genus-one witness: the residue obstruction for `δ₀` on `rfw_E`
A bounded chart form on the outer region of `rfw_E` is a lattice-periodic holomorphic function on
the preimage of the outer region (`rfw_formFun`). If `u⁻¹` on the annulus were `α − g` with `α` such
a form and `g` holomorphic on the disc `D(0, 2/5)`, then `α − u⁻¹` and `g` would glue to a
holomorphic function on the square `[-1/2, 1/2]²`; its boundary integral vanishes (Cauchy), the
periodic part cancels on opposite sides, and what is left is `-2i ∫ (t² + 1/4)⁻¹ dt ≠ 0`.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction Interval
namespace HodgeLean.Foundations.Program
local instance rfw_decidableResidue (p : Prop) : Decidable p := Classical.propDecidable p

/-- The disc of `rfw_outer`. -/
abbrev rfw_x0 : Fin rfw_outer.m := ⟨0, show 0 < rfw_outer.m from Nat.one_pos⟩

/-- The only sector index of a disc of degree one. -/
abbrev rfw_j0 (x : Fin rfw_outer.m) : Fin (rfw_outer.deg x) :=
  ⟨0, show 0 < rfw_outer.deg x from Nat.one_pos⟩

/-- The values of `δ₀` on the annulus: outer coefficient minus disc datum. -/
theorem rfw_delta_apply (k : rf4_Src rfw_outer) (x : Fin rfw_outer.m) {u : ℂ}
    (hu : u ∈ b63r_annulus 1 (1 / 5)) :
    rf4_extendBdd (rf4_delta rfw_outer (fun _ ↦ 0) k x) u =
      rf4_extendBdd (k.1.val (rfw_outer.ann x)) u - rf4_extendBdd (k.2 x (rfw_j0 x)) u := by
  have hu1 : u ∈ b63r_annulus (rfw_outer.deg x) rfw_outer.r := hu
  have hu2 : u ∈ rfw_outer.P.piece (rfw_outer.ann x) := hu
  have hs := rf4_sectorOp_apply (rfw_outer.deg x) (rfw_outer.hdeg x) rfw_outer.r rfw_outer.hr
    (rfw_outer.c x) 0 (by change ‖(0 : ℂ)‖ < 1 / 5; norm_num) (k.2 x) ⟨u, hu1⟩
  change _ = ((1 : ℕ) : ℂ) * ∑ j : Fin 1, rf4_multiplierFun 1 0 j u *
    rf4_extendBdd (k.2 x j) (0 + u ^ 1) at hs
  simp only [Fin.sum_univ_one, rf4_multiplierFun, rf4_sectorExp, zero_add, pow_one,
    Nat.cast_one, one_mul, zero_mul, sub_zero, Complex.one_cpow, Fin.val_zero, pow_zero,
    div_one] at hs
  have key : ((rf4_delta rfw_outer (fun _ ↦ 0) k x :
        b63r_bddHol (b63r_annulus (rfw_outer.deg x) rfw_outer.r)) :
        b63r_annulus (rfw_outer.deg x) rfw_outer.r →ᵇ ℂ) ⟨u, hu1⟩ =
      ((k.1.val (rfw_outer.ann x) : b63r_bddHol (rfw_outer.P.piece (rfw_outer.ann x))) :
        rfw_outer.P.piece (rfw_outer.ann x) →ᵇ ℂ) ⟨u, hu2⟩ -
      ((rf4_sectorOp (rfw_outer.deg x) (rfw_outer.hdeg x) rfw_outer.r rfw_outer.hr
        (rfw_outer.c x) 0 (k.2 x) : b63r_bddHol (b63r_annulus (rfw_outer.deg x) rfw_outer.r)) :
        b63r_annulus (rfw_outer.deg x) rfw_outer.r →ᵇ ℂ) ⟨u, hu1⟩ := rfl
  simp only [rf4_extendBdd, hu1, hu2, ↓reduceDIte]
  rw [key, hs]
  rfl

/-- A point of norm in `(1/5, 4/5)` lies over the outer region. -/
theorem rfw_mem_O_of_norm {p : ℂ} (h1 : 1 / 5 < ‖p‖) (h2 : ‖p‖ < 4 / 5) : rfw_proj p ∈ rfw_O := by
  rintro ⟨q, hq, hqp⟩
  have hq' : ‖q‖ ≤ 1 / 5 := by simpa using hq
  obtain ⟨m, n, hmn⟩ := (rfw_proj_eq_iff q p).mp hqp
  by_cases h0 : (m : ℂ) + n * Complex.I = 0
  · rw [h0, sub_eq_zero] at hmn
    subst hmn
    linarith
  · have := rfw_lattice_norm h0
    rw [← hmn] at this
    have := norm_sub_le p q
    linarith

/-! ## Bounded chart forms as periodic functions -/

/-- The function on `rfw_E` of a bounded chart form on the outer cover: at `p`, the coefficient in
a piece whose chart sends `p` into it, at that chart value; zero if there is none. -/
def rfw_formFunE (α : rf2_bddForm rfw_cover) (p : rfw_E) : ℂ :=
  if h : ∃ i, p ∈ (rfw_cover.chart i).source ∧ rfw_cover.chart i p ∈ rfw_cover.piece i then
    rf4_extendBdd (α.val (Classical.choose h)) (rfw_cover.chart (Classical.choose h) p)
  else 0

/-- The lattice-periodic function on `ℂ` of a bounded chart form. -/
def rfw_formFun (α : rf2_bddForm rfw_cover) (z : ℂ) : ℂ := rfw_formFunE α (rfw_proj z)

theorem rfw_formFun_proj (α : rf2_bddForm rfw_cover) {z z' : ℂ} (h : rfw_proj z = rfw_proj z') :
    rfw_formFun α z = rfw_formFun α z' := by
  simp only [rfw_formFun, h]

/-- The value of `rfw_formFun` through any piece. -/
theorem rfw_formFun_eq (α : rf2_bddForm rfw_cover) (z : ℂ) (i : Fin rfw_cover.n)
    (hs : rfw_proj z ∈ (rfw_cover.chart i).source)
    (hp : rfw_cover.chart i (rfw_proj z) ∈ rfw_cover.piece i) :
    rfw_formFun α z = rf4_extendBdd (α.val i) (rfw_cover.chart i (rfw_proj z)) := by
  have hex : ∃ i, rfw_proj z ∈ (rfw_cover.chart i).source ∧
      rfw_cover.chart i (rfw_proj z) ∈ rfw_cover.piece i := ⟨i, hs, hp⟩
  unfold rfw_formFun rfw_formFunE
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hspec := Classical.choose_spec hex
  generalize Classical.choose hex = j at hspec ⊢
  have hc := α.2 j i ⟨_, hspec.2⟩ ⟨_, hp⟩ (by
    simp only
    rw [(rfw_cover.chart j).left_inv hspec.1, (rfw_cover.chart i).left_inv hs])
  simp only [rf4_extendBdd, hspec.2, hp, ↓reduceDIte]
  refine hc.trans ?_
  have hd : deriv (rfw_cover.chart i ∘ (rfw_cover.chart j).symm)
      (rfw_cover.chart j (rfw_proj z)) = 1 := by
    change deriv (rfw_chart (rfw_cen i) ∘ (rfw_chart (rfw_cen j)).symm)
      (rfw_chart (rfw_cen j) (rfw_proj z)) = 1
    apply rfw_deriv_transition
    rw [← rfw_chart_symm_apply (rfw_cen j), (rfw_chart (rfw_cen j)).left_inv hspec.1]
    exact hs
  rw [hd, mul_one]

/-- `rfw_formFun` is holomorphic over the outer region. -/
theorem rfw_formFun_differentiableAt (α : rf2_bddForm rfw_cover) {z₀ : ℂ}
    (hz₀ : rfw_proj z₀ ∈ rfw_O) : DifferentiableAt ℂ (rfw_formFun α) z₀ := by
  obtain ⟨i, hs, hp⟩ := rfw_mem_piece_of_mem_O hz₀
  change rfw_proj z₀ ∈ (rfw_cover.chart i).source at hs
  change rfw_cover.chart i (rfw_proj z₀) ∈ rfw_cover.piece i at hp
  set s := rfw_cover.chart i (rfw_proj z₀) - z₀
  obtain ⟨gα, hgα, hα⟩ := (α.val i).2
  have hopen := rfw_cover.isOpen i
  have hcont : Continuous fun z : ℂ ↦ z + s := continuous_id.add continuous_const
  have hmem : (fun z : ℂ ↦ z + s) ⁻¹' rfw_cover.piece i ∈ 𝓝 z₀ :=
    hcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simpa [s] using hp))
  have hps : rfw_proj s = 0 := by
    simp only [s, map_sub]
    change (rfw_chart (rfw_cen i)).symm (rfw_chart (rfw_cen i) (rfw_proj z₀)) - rfw_proj z₀ = 0
    rw [(rfw_chart (rfw_cen i)).left_inv hs, sub_self]
  have hev : rfw_formFun α =ᶠ[𝓝 z₀] fun z ↦ gα (z + s) := by
    have ht := rfw_chart_proj_eventually (c := rfw_cen i) (z := z₀) hs
    filter_upwards [ht, hmem] with z hz hzp
    have hz' : rfw_cover.chart i (rfw_proj z) = z + s := hz
    have hsrc : rfw_proj z ∈ (rfw_cover.chart i).source := by
      have hb : z + s ∈ Metric.ball (rfw_cen i) (1 / 2) := rfw_piece_subset i hzp
      have : rfw_proj (z + s) = rfw_proj z := by rw [map_add, hps, add_zero]
      rw [← this]
      exact rfw_proj_mem_source hb
    have hzp' : z + s ∈ rfw_cover.piece i := hzp
    rw [rfw_formFun_eq α z i hsrc (by rw [hz']; exact hzp'), hz']
    simp only [rf4_extendBdd, hzp', ↓reduceDIte]
    exact hα ⟨_, hzp'⟩
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev)
  have : DifferentiableAt ℂ gα (z₀ + s) :=
    (hgα _ (by simpa [s] using hp)).differentiableAt (hopen.mem_nhds (by simpa [s] using hp))
  exact this.comp z₀ (differentiableAt_id.add_const s)

/-! ## The residue obstruction -/

theorem rfw_annulus_norm {u : ℂ} (hu : u ∈ b63r_annulus 1 (1 / 5)) : 1 / 5 < ‖u‖ ∧ ‖u‖ < 2 / 5 := by
  have h1 := hu.1
  have h2 := hu.2
  simp only [pow_one] at h1 h2
  constructor <;> linarith

theorem rfw_mem_annulus {u : ℂ} (h1 : 1 / 5 < ‖u‖) (h2 : ‖u‖ < 2 / 5) :
    u ∈ b63r_annulus 1 (1 / 5) := by
  constructor <;> simp only [pow_one] <;> linarith

/-- `u⁻¹` as a bounded holomorphic function on the annulus.
Source: `rf4_bddOn`; `u⁻¹` is continuous on `{1/5 ≤ |u| ≤ 2/5}`, which avoids `0`. -/
def rfw_invA : b63r_bddHol (b63r_annulus 1 (1 / 5)) :=
  rf4_bddOn (rf4_closedAnnulus_isCompact le_rfl _) (rf4_annulus_subset_closed 1 _) (fun u ↦ u⁻¹)
    (fun _ hu ↦ (continuousAt_inv₀
      (rf4_closedAnnulus_ne_zero le_rfl (by norm_num) hu)).continuousWithinAt)
    (fun _ hu ↦ (differentiableAt_inv (rf4_closedAnnulus_ne_zero le_rfl (by norm_num)
      (rf4_annulus_subset_closed 1 _ hu))).differentiableWithinAt)

/-- `du/u` on the annulus, as an element of the target of `δ₀`. -/
def rfw_invT : rf4_Tgt rfw_outer := fun _ ↦ rfw_invA

theorem rfw_invT_apply (x : Fin rfw_outer.m) {u : ℂ} (hu : u ∈ b63r_annulus 1 (1 / 5)) :
    rf4_extendBdd (rfw_invT x) u = u⁻¹ := by
  have hu1 : u ∈ b63r_annulus (rfw_outer.deg x) rfw_outer.r := hu
  simp only [rf4_extendBdd, hu1, ↓reduceDIte]
  rfl

/-- The coefficient of a bounded chart form on the annulus piece is `rfw_formFun`. -/
theorem rfw_formFun_annulus (α : rf2_bddForm rfw_cover) (x : Fin rfw_outer.m) {u : ℂ}
    (hu : u ∈ b63r_annulus 1 (1 / 5)) :
    rf4_extendBdd (α.val (rfw_outer.ann x)) u = rfw_formFun α u := by
  have hb : u ∈ Metric.ball (0 : ℂ) (1 / 2) :=
    rfw_closedAnnulus_subset (rf4_annulus_subset_closed 1 _ hu)
  have h := rfw_formFun_eq α u (0 : Fin (rfw_centres.card + 1)) (rfw_proj_mem_source hb) (by
    change rfw_chart 0 (rfw_proj u) ∈ rfw_piece 0
    rw [rfw_chart_proj hb]
    exact hu)
  rw [h]
  change _ = rf4_extendBdd (α.val (0 : Fin (rfw_centres.card + 1))) (rfw_chart 0 (rfw_proj u))
  rw [rfw_chart_proj hb]
  rfl

theorem rfw_rect_pos : 0 < ∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2), (x ^ 2 + 1 / 4)⁻¹ := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (Continuous.continuousOn (by fun_prop) (s := uIcc _ _) |>.inv₀
      (fun x _ ↦ by positivity)).intervalIntegrable
  · intro x _
    positivity
  · norm_num

theorem rfw_rect_norm {p : ℂ} (hp : p ∈ [[(-1 / 2 : ℝ), 1 / 2]] ×ℂ [[(-1 / 2 : ℝ), 1 / 2]]) :
    ‖p‖ < 4 / 5 := by
  simp only [Complex.mem_reProdIm, uIcc_of_le (show (-1 / 2 : ℝ) ≤ 1 / 2 by norm_num),
    mem_Icc] at hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have hsq : ‖p‖ ^ 2 = p.re ^ 2 + p.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [norm_nonneg p]

/-- **The residue obstruction**: `du/u` is not in the range of `δ₀`. -/
theorem rfw_invT_not_mem_range :
    rfw_invT ∉ (rf4_delta rfw_outer (fun _ ↦ 0)).range := by
  rintro ⟨k, hk⟩
  simp only [ContinuousLinearMap.coe_coe] at hk
  set F := rfw_formFun k.1
  obtain ⟨gg, hgg, hgk⟩ := (k.2 rfw_x0 (rfw_j0 rfw_x0)).2
  have hball : Metric.ball (rfw_outer.c rfw_x0) (2 * rfw_outer.r) =
      Metric.ball (0 : ℂ) (2 / 5) := by
    change Metric.ball (0 : ℂ) (2 * (1 / 5)) = _
    norm_num
  have hgg' : DifferentiableOn ℂ gg (Metric.ball (0 : ℂ) (2 / 5)) := hball ▸ hgg
  have heq : ∀ u ∈ b63r_annulus 1 (1 / 5), u⁻¹ = F u - gg u := by
    intro u hu
    have h := congrArg (fun t : rf4_Tgt rfw_outer ↦ rf4_extendBdd (t rfw_x0) u) hk
    rw [rfw_delta_apply k _ hu, rfw_invT_apply _ hu] at h
    rw [← h]
    congr 1
    · exact rfw_formFun_annulus k.1 rfw_x0 hu
    have hub : u ∈ Metric.ball (rfw_outer.c rfw_x0) (2 * rfw_outer.r) := by
      rw [hball, mem_ball_zero_iff]; exact (rfw_annulus_norm hu).2
    simp only [rf4_extendBdd, hub, ↓reduceDIte]
    rw [hgk ⟨u, hub⟩]
  let K : ℂ → ℂ := fun z ↦ if ‖z‖ < 2 / 5 then gg z else F z - z⁻¹
  have hKout : ∀ q : ℂ, 1 / 5 < ‖q‖ → K q = F q - q⁻¹ := by
    intro q hq
    simp only [K]
    split_ifs with h
    · rw [heq q (rfw_mem_annulus hq h)]; ring
    · rfl
  have hK : DifferentiableOn ℂ K ([[(-1 / 2 : ℝ), 1 / 2]] ×ℂ [[(-1 / 2 : ℝ), 1 / 2]]) := by
    intro p hp
    have hp8 := rfw_rect_norm hp
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases h : ‖p‖ < 2 / 5
    · have hm : Metric.ball (0 : ℂ) (2 / 5) ∈ 𝓝 p :=
        Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr h)
      refine ((hgg' p (mem_ball_zero_iff.mpr h)).differentiableAt hm).congr_of_eventuallyEq ?_
      filter_upwards [hm] with q hq
      simp only [K, mem_ball_zero_iff.mp hq, ↓reduceIte]
    · push Not at h
      have hm : {q : ℂ | 1 / 5 < ‖q‖} ∈ 𝓝 p :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds (by
          change 1 / 5 < ‖p‖; linarith)
      have hp0 : p ≠ 0 := by
        rintro rfl; norm_num at h
      refine ((rfw_formFun_differentiableAt k.1 (rfw_mem_O_of_norm (by linarith) hp8)).sub
        (differentiableAt_inv hp0)).congr_of_eventuallyEq ?_
      filter_upwards [hm] with q hq
      exact hKout q hq
  have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn K
    ⟨-1 / 2, -1 / 2⟩ ⟨1 / 2, 1 / 2⟩ hK
  simp only at hR
  have hKc : ContinuousOn K ([[(-1 / 2 : ℝ), 1 / 2]] ×ℂ [[(-1 / 2 : ℝ), 1 / 2]]) := hK.continuousOn
  have hI : ∀ (a : ℝ), a ∈ [[(-1 / 2 : ℝ), 1 / 2]] →
      IntervalIntegrable (fun x : ℝ ↦ K (x + a * Complex.I)) MeasureTheory.volume (-1 / 2) (1 / 2) ∧
      IntervalIntegrable (fun y : ℝ ↦ K (a + y * Complex.I)) MeasureTheory.volume
        (-1 / 2) (1 / 2) := by
    intro a ha
    constructor
    · refine (hKc.comp (by fun_prop) (fun x hx ↦ ?_)).intervalIntegrable
      refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
      · simpa using hx
      · simpa using ha
    · refine (hKc.comp (by fun_prop) (fun y hy ↦ ?_)).intervalIntegrable
      refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
      · simpa using ha
      · simpa using hy
  have hm1 : (-1 / 2 : ℝ) ∈ [[(-1 / 2 : ℝ), 1 / 2]] := left_mem_uIcc
  have hm2 : (1 / 2 : ℝ) ∈ [[(-1 / 2 : ℝ), 1 / 2]] := right_mem_uIcc
  have hper1 : ∀ x : ℝ, F (x + (-1 / 2 : ℝ) * Complex.I) = F (x + (1 / 2 : ℝ) * Complex.I) := by
    intro x
    refine rfw_formFun_proj k.1 ((rfw_proj_eq_iff _ _).mpr ⟨0, 1, ?_⟩)
    push_cast; ring
  have hper2 : ∀ y : ℝ, F ((1 / 2 : ℝ) + y * Complex.I) = F ((-1 / 2 : ℝ) + y * Complex.I) := by
    intro y
    refine rfw_formFun_proj k.1 ((rfw_proj_eq_iff _ _).mpr ⟨-1, 0, ?_⟩)
    push_cast; ring
  have hnb : ∀ (x a : ℝ), |a| = 1 / 2 → 1 / 5 < ‖(x : ℂ) + a * Complex.I‖ := by
    intro x a ha
    have := Complex.abs_im_le_norm ((x : ℂ) + a * Complex.I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero] at this
    linarith
  have hnr : ∀ (y a : ℝ), |a| = 1 / 2 → 1 / 5 < ‖(a : ℂ) + y * Complex.I‖ := by
    intro y a ha
    have := Complex.abs_re_le_norm ((a : ℂ) + y * Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, sub_zero, add_zero] at this
    linarith
  have ha1 : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num [abs_of_neg]
  have ha2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  have hbt : (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2), K (x + (-1 / 2 : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2), K (x + (1 / 2 : ℝ) * Complex.I)) =
      -Complex.I * ∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2), (((x ^ 2 + 1 / 4 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_sub (hI _ hm1).1 (hI _ hm2).1,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    rw [hKout _ (hnb x _ ha1), hKout _ (hnb x _ ha2), hper1 x]
    have h1 : (x : ℂ) + ((-1 / 2 : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro h0; have := congrArg Complex.im h0; simp at this
    have h2 : (x : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro h0; have := congrArg Complex.im h0; simp at this
    have hd : ((x : ℂ) + ((-1 / 2 : ℝ) : ℂ) * Complex.I) - ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)
        = -Complex.I := by push_cast; ring
    have hp : ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) * ((x : ℂ) + ((-1 / 2 : ℝ) : ℂ) * Complex.I)
        = ((x ^ 2 + 1 / 4 : ℝ) : ℂ) := by
      push_cast; linear_combination (-1 / 4 : ℂ) * Complex.I_sq
    rw [Complex.ofReal_inv, ← hp, ← hd, sub_sub_sub_cancel_left, inv_sub_inv h2 h1]
    ring
  have hrl : (∫ y : ℝ in (-1 / 2 : ℝ)..(1 / 2), K ((1 / 2 : ℝ) + y * Complex.I)) -
      (∫ y : ℝ in (-1 / 2 : ℝ)..(1 / 2), K ((-1 / 2 : ℝ) + y * Complex.I)) =
      -∫ y : ℝ in (-1 / 2 : ℝ)..(1 / 2), (((y ^ 2 + 1 / 4 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_sub (hI _ hm2).2 (hI _ hm1).2,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    rw [hKout _ (hnr y _ ha2), hKout _ (hnr y _ ha1), hper2 y]
    have h1 : ((1 / 2 : ℝ) : ℂ) + y * Complex.I ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
    have h2 : ((-1 / 2 : ℝ) : ℂ) + y * Complex.I ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
    have hd : (((1 / 2 : ℝ) : ℂ) + y * Complex.I) - (((-1 / 2 : ℝ) : ℂ) + y * Complex.I) = 1 := by
      push_cast; ring
    have hp : (((-1 / 2 : ℝ) : ℂ) + y * Complex.I) * (((1 / 2 : ℝ) : ℂ) + y * Complex.I)
        = -((y ^ 2 + 1 / 4 : ℝ) : ℂ) := by
      push_cast; linear_combination ((y : ℂ) ^ 2) * Complex.I_sq
    rw [Complex.ofReal_inv, sub_sub_sub_cancel_left, inv_sub_inv h2 h1, hd, hp]
    ring
  have hJ := rfw_rect_pos
  rw [intervalIntegral.integral_ofReal] at hbt hrl
  have hsum : (-Complex.I * ((∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2), (x ^ 2 + 1 / 4)⁻¹ : ℝ) : ℂ)) +
      Complex.I * (-((∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2), (x ^ 2 + 1 / 4)⁻¹ : ℝ) : ℂ)) = 0 := by
    rw [← hbt, ← hrl, ← hR]
    simp only [smul_eq_mul]
    ring
  have : ((∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2), (x ^ 2 + 1 / 4)⁻¹ : ℝ) : ℂ) = 0 := by
    have h2 : (-2 * Complex.I) * ((∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2), (x ^ 2 + 1 / 4)⁻¹ : ℝ) : ℂ)
        = 0 := by rw [← hsum]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · exfalso; simp at h
    · exact h
  exact absurd (Complex.ofReal_eq_zero.mp this) hJ.ne'

end HodgeLean.Foundations.Program
