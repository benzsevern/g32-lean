import HodgeLean.Foundations.Program.MarkedRootCoverLoops

/-! # Open obligations for the marked root cover -/

noncomputable section
open scoped Manifold ContDiff
open Complex
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold


theorem mr_branch_eq (j : Fin 13) :
    b6_branch mr_base j =
      if j.val < 12 then (((mr_int j : ℤ) : ℂ) : OnePoint ℂ) else OnePoint.infty := by
  fin_cases j <;> simp [b6_branch, mr_base, mr_int, Fin.append, Fin.addCases] <;> norm_num

theorem mr_base_mem_chart_aux :
    mr_base ∈ b6_chart := by
  intro i j h
  rw [mr_branch_eq, mr_branch_eq] at h
  have key : ∀ i j : Fin 13, i.val < 12 → j.val < 12 → mr_int i = mr_int j → i = j := by
    decide
  split_ifs at h with hi hj hj
  · exact key i j hi hj (by exact_mod_cast OnePoint.coe_injective h)
  · exact absurd h (OnePoint.coe_ne_infty _)
  · exact absurd h.symm (OnePoint.coe_ne_infty _)
  · ext; omega




/-- Points of a segment from the base point down to the line `Im = 1/4` stay away from the
real axis. -/
theorem mr_segment_far (p m : ℂ) (hp : p.im = 0) (hm : m.im = 0) (u : ℝ) (hu1 : u ≤ 1) : 1 / 4 ≤ ‖mr_basePoint + (u : ℂ) * (p + I / 4 - mr_basePoint) - m‖ := by
  refine le_trans ?_ (Complex.abs_im_le_norm _)
  simp [mr_basePoint, mr_centre, hp, hm]
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith

theorem mr_circle_far (p m : ℂ) (x : ℝ) (h : m = p ∨ 1 ≤ ‖p - m‖) :
    1 / 4 ≤ ‖p + I / 4 * exp (2 * Real.pi * I * (x : ℂ)) - m‖ := by
  have he : ‖I / 4 * exp (2 * Real.pi * I * (x : ℂ))‖ = 1 / 4 := by
    have : 2 * Real.pi * I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * I := by push_cast; ring
    rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I]
    simp
  rcases h with rfl | h
  · rw [add_sub_cancel_left, he]
  · have := norm_sub_norm_le (p - m) (-(I / 4 * exp (2 * Real.pi * I * (x : ℂ))))
    rw [norm_neg, he] at this
    have e : p - m - -(I / 4 * exp (2 * Real.pi * I * (x : ℂ))) =
      p + I / 4 * exp (2 * Real.pi * I * (x : ℂ)) - m := by ring
    rw [e] at this
    linarith

theorem mr_outer_far (m : ℂ) (hm : m.im = 0) (hm1 : -12 ≤ m.re) (hm2 : m.re ≤ 1) (x : ℝ) :
    1 / 4 ≤ ‖mr_outer x - m‖ := by
  have he : ‖10 * I * exp (-(2 * Real.pi * I * (x : ℂ)))‖ = 10 := by
    have : -(2 * Real.pi * I * (x : ℂ)) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * I := by push_cast; ring
    rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I]
    simp
  have hc : ‖mr_centre - m‖ ≤ 13 / 2 := by
    have : mr_centre - m = ((-11 / 2 - m.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [mr_centre, hm]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have := norm_sub_norm_le (10 * I * exp (-(2 * Real.pi * I * (x : ℂ)))) (-(mr_centre - m))
  rw [norm_neg, he] at this
  have e : 10 * I * exp (-(2 * Real.pi * I * (x : ℂ))) - -(mr_centre - m) = mr_outer x - m := by
    simp only [mr_outer]; ring
  rw [e] at this
  linarith

theorem mr_lasso_far (p m : ℂ) (hp : p.im = 0) (hm : m.im = 0) (h : m = p ∨ 1 ≤ ‖p - m‖)
    (s : ℝ) : 1 / 4 ≤ ‖mr_lasso p s - m‖ := by
  unfold mr_lasso
  split_ifs with h1 h2
  · exact mr_segment_far p m hp hm _ (by linarith)
  · exact mr_circle_far p m _ h
  · exact mr_segment_far p m hp hm _ (by linarith)

/-- Every explicit curve point is a finite point at distance at least `1/4` from every finite
mark of the base configuration. -/
theorem mr_curve_far (i : Fin 13) (s : ℝ) :
    ∃ z : ℂ, mr_curve i s = (z : OnePoint ℂ) ∧
      ∀ j : Fin 13, j.val < 12 → 1 / 4 ≤ ‖z - ((mr_int j : ℤ) : ℂ)‖ := by
  unfold mr_curve
  split_ifs with hi
  · refine ⟨_, rfl, fun j hj ↦ ?_⟩
    rw [mr_marks_eq]
    apply mr_lasso_far _ _ (by simp) (by simp) _ s
    by_cases hij : j = (⟨i.val, hi⟩ : Fin 12).castSucc
    · left; rw [hij]
    · right
      have hne := mr_int_sep _ _ (by simpa using hi) hj (Ne.symm hij)
      rw [← Int.cast_sub, Complex.norm_intCast]
      have : (1 : ℤ) ≤ |mr_int (⟨i.val, hi⟩ : Fin 12).castSucc - mr_int j| :=
        Int.one_le_abs (sub_ne_zero.2 hne)
      exact_mod_cast this
  · refine ⟨_, rfl, fun j hj ↦ ?_⟩
    obtain ⟨h1, h2⟩ := mr_int_range j hj
    exact mr_outer_far _ (by simp) (by simp; exact_mod_cast h1) (by simp; exact_mod_cast h2) s






theorem mr_branch_cases (t : Fin 10 → ℂ) (j : Fin 13) :
    (∃ k : Fin 10, b6_branch t j = (t k : OnePoint ℂ)) ∨ b6_branch t j = ((0 : ℂ) : OnePoint ℂ) ∨
      b6_branch t j = ((1 : ℂ) : OnePoint ℂ) ∨ b6_branch t j = OnePoint.infty := by
  fin_cases j <;> simp [b6_branch, Fin.append, Fin.addCases]

/-- A finite point at distance at least `1/4` from every finite base mark avoids every
branch disc of `mr_base` and every mark of each configuration of its polydisc. -/
theorem mr_far_avoids (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (z : ℂ)
    (hz : ∀ j : Fin 13, j.val < 12 → 1 / 4 ≤ ‖z - ((mr_int j : ℤ) : ℂ)‖) :
    (z : OnePoint ℂ) ∉ Set.range (b6_branch t) ∧
      (z : OnePoint ℂ) ∉ ⋃ k : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
        Metric.closedBall (mr_base k) (b6t_radius mr_base) := by
  have hr := mr_radius_lt
  have hball : ∀ k : Fin 10, b6t_radius mr_base < dist z (mr_base k) := by
    intro k
    rw [dist_eq_norm, mr_base_eq]
    exact lt_of_lt_of_le hr (hz _ (show k.val < 12 by omega))
  refine ⟨?_, ?_⟩
  · rintro ⟨j, hj⟩
    rcases mr_branch_cases t j with ⟨k, hk⟩ | h0 | h1 | hi
    · rw [hk] at hj
      have hzk : z = t k := (OnePoint.coe_injective hj).symm
      have h1 := hball k
      have h2 : dist (t k) (mr_base k) < b6t_radius mr_base := ht k
      rw [hzk] at h1
      linarith
    · rw [h0] at hj
      have hzk : z = 0 := (OnePoint.coe_injective hj).symm
      have := hz 10 (by decide)
      simp [mr_int, hzk] at this
      norm_num at this
    · rw [h1] at hj
      have hzk : z = 1 := (OnePoint.coe_injective hj).symm
      have := hz 11 (by decide)
      simp [mr_int, hzk] at this
      norm_num at this
    · rw [hi] at hj
      exact OnePoint.infty_ne_coe _ hj
  · simp only [Set.mem_iUnion, Set.mem_image, not_exists, not_and]
    intro k w hw hwz
    have hwz' : w = z := OnePoint.coe_injective hwz
    rw [hwz', Metric.mem_closedBall] at hw
    linarith [hball k]

theorem mr_curve_avoids_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∀ (i : Fin 13) (s : unitInterval), mr_curve i s ∉ Set.range (b6_branch t) ∧
      mr_curve i s ∉ ⋃ k : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
        Metric.closedBall (mr_base k) (b6t_radius mr_base) := by
  intro i s
  obtain ⟨z, hz, hfar⟩ := mr_curve_far i s
  rw [hz]
  exact mr_far_avoids t ht z hfar



theorem mr_lasso_continuous (p : ℂ) : Continuous (mr_lasso p) := by
  unfold mr_lasso
  refine Continuous.if_le (by fun_prop) (Continuous.if_le (by fun_prop) (by fun_prop)
    continuous_id continuous_const ?_) continuous_id continuous_const ?_
  · intro s hs
    rw [hs]
    have : 2 * (Real.pi : ℂ) * I * ((3 * (2 / 3 : ℝ) - 1 : ℝ) : ℂ) = 2 * Real.pi * I := by
      push_cast; ring
    rw [this, Complex.exp_two_pi_mul_I]
    push_cast; ring
  · intro s hs
    rw [hs]
    simp only [show (1 / 3 : ℝ) ≤ 2 / 3 by norm_num, ↓reduceIte]
    have : 2 * (Real.pi : ℂ) * I * ((3 * (1 / 3 : ℝ) - 1 : ℝ) : ℂ) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero]
    push_cast; ring

theorem mr_outer_continuous : Continuous mr_outer := by
  unfold mr_outer; fun_prop

theorem mr_curve_continuous (i : Fin 13) : Continuous (mr_curve i) := by
  unfold mr_curve
  split_ifs
  · exact OnePoint.continuous_coe.comp (mr_lasso_continuous _)
  · exact OnePoint.continuous_coe.comp mr_outer_continuous

theorem mr_curve_zero (i : Fin 13) : mr_curve i 0 = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
  unfold mr_curve
  split_ifs
  · simp [mr_lasso]
  · simp [mr_outer, mr_basePoint]

theorem mr_curve_one (i : Fin 13) : mr_curve i 1 = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
  unfold mr_curve
  split_ifs
  · simp [mr_lasso]; norm_num
  · have : -(2 * (Real.pi : ℂ) * I * ((1 : ℝ) : ℂ)) = -(2 * Real.pi * I) := by push_cast; ring
    simp only [mr_outer, this, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one,
      mr_basePoint]

/-- The explicit based path tracing `mr_curve i` in the punctured sphere at `t`. -/
def mr_path (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ)) (i : Fin 13) : Path y₀ y₀ where
  toFun s := ⟨mr_curve i s, (mr_curve_avoids_aux t ht i s).1⟩
  continuous_toFun := ((mr_curve_continuous i).comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (by simp [mr_curve_zero, hy₀])
  target' := Subtype.ext (by simp [mr_curve_one, hy₀])

theorem mr_loop_existsUnique_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ)) (i : Fin 13) :
    ∃! c : FundamentalGroup (b6t_punctured t) y₀, mr_IsLoop t y₀ i c := by
  refine ⟨_, ⟨mr_path t ht y₀ hy₀ i, fun s ↦ rfl, rfl⟩, ?_⟩
  rintro c ⟨q, hq, rfl⟩
  have : q = mr_path t ht y₀ hy₀ i := Path.ext (funext fun s ↦ Subtype.ext (hq s))
  rw [this]



theorem mr_loops_product_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    (List.ofFn γ).reverse.prod = 1 := by
  choose P hP hPc using hγ
  have hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    have := hP 0 0
    rw [(P 0).source] at this
    rw [this]; exact mr_curve_zero 0
  obtain ⟨Ψ, hΨ⟩ := mr_plane_exists t
  obtain ⟨e, he⟩ := RiemannRochTop_homeomorph_pi1_map Ψ y₀
  have h := mr_plane_outer t ht Ψ hΨ y₀ hy₀ (fun j ↦ P j.castSucc) (fun j ↦ hP j.castSucc)
    (P (Fin.last 12)) (hP (Fin.last 12))
  apply e.injective
  rw [map_one, mr_reverse_prod_last, map_mul, map_list_prod, List.map_reverse, List.map_ofFn,
    ← hPc, he]
  convert h using 4
  congr 1
  funext j
  simp only [Function.comp_apply, ← hPc, he]

theorem mr_loops_universal_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    ∀ (H : Type) [Group H] (k : Fin 13 → H), (List.ofFn k).reverse.prod = 1 →
      ∃! ψ : FundamentalGroup (b6t_punctured t) y₀ →* H, ∀ i, ψ (γ i) = k i := by
  intro H _ k hk
  have hrel := mr_loops_product_aux t ht y₀ γ hγ
  choose P hP hPc using hγ
  have hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    have := hP 0 0
    rw [(P 0).source] at this
    rw [this]; exact mr_curve_zero 0
  obtain ⟨Ψ, hΨ⟩ := mr_plane_exists t
  obtain ⟨e, he⟩ := RiemannRochTop_homeomorph_pi1_map Ψ y₀
  obtain ⟨φ, hφ, huniq⟩ := mr_plane_free t ht Ψ hΨ y₀ hy₀ (fun j ↦ P j.castSucc)
    (fun j ↦ hP j.castSucc) H (fun j ↦ k j.castSucc)
  have hφ' : ∀ j : Fin 12, φ (e (γ j.castSucc)) = k j.castSucc := by
    intro j; rw [← hPc, he]; exact hφ j
  rw [mr_reverse_prod_last] at hk hrel
  have hlast : φ (e (γ (Fin.last 12))) = k (Fin.last 12) := by
    have h1 : γ (Fin.last 12) =
        ((List.ofFn fun j : Fin 12 ↦ γ j.castSucc).reverse.prod)⁻¹ :=
      eq_inv_of_mul_eq_one_left hrel
    have h2 : k (Fin.last 12) =
        ((List.ofFn fun j : Fin 12 ↦ k j.castSucc).reverse.prod)⁻¹ :=
      eq_inv_of_mul_eq_one_left hk
    rw [h1, h2, map_inv, map_inv, map_list_prod, map_list_prod, List.map_reverse,
      List.map_reverse, List.map_ofFn, List.map_ofFn]
    congr 3
    congr 1
    funext j
    exact hφ' j
  refine ⟨φ.comp e.toMonoidHom, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => exact hlast
    | cast j => exact hφ' j
  · intro ψ hψ
    have : ψ.comp e.symm.toMonoidHom = φ := by
      apply huniq
      intro j
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← he, hPc, MulEquiv.symm_apply_apply, hψ]
    ext x
    rw [← this]
    simp

theorem mr_loops_positive_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    ∀ (D : Type) [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ, ℂ) ω D]
      [T2Space D] [CompactSpace D] [ConnectedSpace D] (G : Type) [Group G] [Finite G]
      [MulAction G D] [FaithfulSMul G D],
      (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x)) →
      ∀ f : D → OnePoint ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover G f →
      (∀ x, f x ∉ Set.range (b6_branch t) → MulAction.stabilizer G x = ⊥) →
      ∀ (j : Fin 13) (c : Path y₀ y₀), FundamentalGroup.fromPath ⟦c⟧ = γ j →
      ∀ (Γ : C(unitInterval, D)) (k : G), (∀ s, f (Γ s) = (c s : OnePoint ℂ)) →
        Γ 1 = k • Γ 0 → ∃ x, f x = b6_branch t j ∧ b4_IsRotGen ℂ x k := by
  intro D _ _ _ _ _ _ G _ _ _ _ hG f hf hgal hfree j c hc Γ k hΓ hend
  choose P hP hPc using hγ
  have hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    have := hP 0 0
    rw [(P 0).source] at this
    rw [this]; exact mr_curve_zero 0
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  have hB : (Set.range (b6_branch t)).Finite := Set.finite_range _
  induction j using Fin.lastCases with
  | last =>
    rw [mr_branch_last]
    have hd : ∀ s : unitInterval, ((P (Fin.last 12)).symm s : OnePoint ℂ) =
        ((mr_centre + Complex.exp ((((s : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) * (10 * I) : ℂ) :
          OnePoint ℂ) := by
      intro s
      change ((P (Fin.last 12)) (unitInterval.symm s) : OnePoint ℂ) = _
      rw [hP, mr_curve_last, unitInterval.coe_symm_eq, mr_outer_symm]
    have hbound : ∀ b : ℂ, (b : OnePoint ℂ) ∈ Set.range (b6_branch t) →
        ‖b - mr_centre‖ < 7 := by
      intro b hb
      rcases (mr_mem_branch t b).1 hb with h | ⟨i, hi⟩
      · exact absurd h (OnePoint.coe_ne_infty b)
      · rw [OnePoint.coe_injective hi]; exact mr_fin_center_bound t ht i
    have havoid := RiemannRochTop_infinity_disk_avoids _ mr_centre 7 (by norm_num) hbound
    have hc2 : FundamentalGroup.fromPath ⟦c⟧ = FundamentalGroup.fromPath
        ⟦((Path.refl y₀).trans (P (Fin.last 12)).symm.symm).trans (Path.refl y₀).symm⟧ := by
      rw [hc, ← hPc, Path.symm_symm, Path.refl_symm]
      apply congrArg FundamentalGroup.fromPath
      apply Quotient.sound
      exact (((Path.Homotopic.refl_trans _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.trans_refl _)).symm
    refine RiemannRochTop_rotGen_infinity_circle hE hG f hf hgal _ hB hfree mr_centre 7⁻¹
      havoid (10 * I) ?_ (by simp) (Path.refl y₀) (P (Fin.last 12)).symm hd c ?_ Γ k hΓ hend
    · rw [norm_inv, norm_mul]; simp; norm_num
    · exact hc2
  | cast j =>
    rw [mr_branch_castSucc]
    obtain ⟨Ψ, hΨ⟩ := mr_plane_exists t
    obtain ⟨q₁, q₂, α, δ, β, hα, hδ, hβ, hq1, hq2, hH⟩ :=
      mr_lasso_cut t ht Ψ hΨ y₀ j (P j.castSucc) (hP _)
    obtain ⟨y', k', c', -, hc', hhom⟩ := RiemannRochTop_cut_loop_inverse_circle (mr_planeSet t)
      (mr_planeSet_finite t) _ ⟨j, rfl⟩ (1 / 2) (by norm_num) (mr_plane_iso t ht j)
      α δ β hα hδ hβ hq1 hq2
    obtain ⟨K, Dp, hDp, hPK⟩ := mr_transport_conj Ψ (P j.castSucc) k' c'.symm (hH.symm.trans hhom)
    have hd : ∀ s : unitInterval, (Dp s : OnePoint ℂ) =
        ((mr_fin t j + Complex.exp ((((s : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) *
          (Complex.exp (((-(Real.pi / 4)) : ℝ) * I) * ((1 / 4 : ℝ) : ℂ)) : ℂ) :
            OnePoint ℂ) := by
      intro s
      rw [hDp, mr_plane_symm t Ψ hΨ]
      change (((starRingEnd ℂ) (c' (unitInterval.symm s)) : ℂ) : OnePoint ℂ) = _
      rw [hc', unitInterval.coe_symm_eq, mr_circle_conj]
    have havoid : ∀ z : ℂ, ‖z‖ < 1 / 2 → z ≠ 0 →
        ((mr_fin t j + z : ℂ) : OnePoint ℂ) ∉ Set.range (b6_branch t) := by
      intro z hz hz0 hmem
      rcases (mr_mem_branch t _).1 hmem with h | ⟨i, hi⟩
      · exact OnePoint.coe_ne_infty _ h
      · have hi' := OnePoint.coe_injective hi
        by_cases hij : i = j
        · subst hij; apply hz0; linear_combination hi'
        · have h1 := mr_fin_re_sep t ht i j hij
          have h2 : (mr_fin t i).re - (mr_fin t j).re = z.re := by
            rw [← hi']; simp
          rw [h2] at h1
          linarith [Complex.abs_re_le_norm z]
    have hw : ‖Complex.exp (((-(Real.pi / 4)) : ℝ) * I) * ((1 / 4 : ℝ) : ℂ)‖ < 1 / 2 := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I]; simp; norm_num
    have hw0 : Complex.exp (((-(Real.pi / 4)) : ℝ) * I) * ((1 / 4 : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (by norm_num)
    have hc2 : FundamentalGroup.fromPath ⟦c⟧ =
        FundamentalGroup.fromPath ⟦(K.trans Dp).trans K.symm⟧ :=
      hc.trans ((hPc _).symm.trans (congrArg FundamentalGroup.fromPath (Quotient.sound hPK)))
    exact RiemannRochTop_rotGen_affine_circle hE hG f hf hgal _ hB hfree (mr_fin t j) (1 / 2)
      havoid _ hw hw0 K Dp hd c hc2 Γ k hΓ hend

theorem mr_root_surjective_aux {M : Type} [Group M] (φ : M →* b4b_Groupᵐᵒᵖ) (γ : Fin 13 → M)
    (hroot : ∀ i, φ (γ i) = MulOpposite.op (b4b_root i)) :
    Function.Surjective φ := by
  intro g
  have hK : Subgroup.closure (Set.range b4b_root) ≤ φ.range.unop := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨γ i, hroot i⟩
  rw [b63d_root_subgroup] at hK
  exact hK (Subgroup.mem_top g.unop)

theorem mr_loop_transport_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (e : b6t_punctured mr_base ≃ₜ b6t_punctured t)
    (he : ∀ x, (e x : OnePoint ℂ) = b6t_sphere mr_base t x)
    (y₀ : b6t_punctured mr_base) (i : Fin 13)
    (c : FundamentalGroup (b6t_punctured mr_base) y₀) (hc : mr_IsLoop mr_base y₀ i c) :
    mr_IsLoop t (e y₀) i (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ c) := by
  have hbase : mr_base ∈ b6t_polydisc mr_base :=
    (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart_aux).1
  obtain ⟨p, hp, rfl⟩ := hc
  refine ⟨p.map e.continuous, fun s ↦ ?_, rfl⟩
  have hout := (mr_curve_avoids_aux mr_base hbase i s).2
  rw [← hp s] at hout
  change ((e (p s) : b6t_punctured t) : OnePoint ℂ) = _
  rw [he, (b6t_fixed mr_base mr_base_mem_chart_aux t ht).2.2.2 _ hout, hp s]

theorem mr_rootCover_aux (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction b4b_Group U)
      (_ : ConnectedSpace U) (π : U → b6t_punctured mr_base)
      (hπ : IsQuotientCoveringMap π b4b_Group) (u₀ : π ⁻¹' {y₀}),
      (∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
      ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
        (_ : ConnectedSpace C) (_ : MulAction b4b_Group C) (_ : FaithfulSMul b4b_Group C)
        (f : C → OnePoint ℂ) (ι : U → C),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover b4b_Group f ∧
        Function.Surjective f ∧
        (∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
        Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ ∧
        (∀ u, f (ι u) = π u) ∧ (∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u) ∧
        (∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥) ∧
        ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j) := by
  have hbase : mr_base ∈ b6t_polydisc mr_base :=
    (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart_aux).1
  obtain ⟨φ, hφ, -⟩ := mr_loops_universal_aux mr_base hbase y₀ γ hγ b4b_Groupᵐᵒᵖ
    (fun i ↦ MulOpposite.op (b4b_root i)) mr_root_op_reverse_prod
  have hφs := mr_root_surjective_aux φ γ hφ
  obtain ⟨U, _, _, _, π, hπ, u₀, hφeq, C, _, _, _, _, _, _, _, f, ι, hf, hgal, hsurj, hG, hι,
    hιr, hfι, hιeq⟩ := b6m_marked_rex mr_base mr_base_mem_chart_aux b4b_Group y₀ φ hφs
  have hfree : ∀ (k : b4b_Group) (u : U), k • u = u → k = 1 := by
    intro k u hku
    obtain ⟨V, hV, hV'⟩ := hπ.disjoint u
    exact hV' k ⟨u, ⟨u, mem_of_mem_nhds hV, hku⟩, mem_of_mem_nhds hV⟩
  have hstab : ∀ x, f x ∉ Set.range (b6_branch mr_base) →
      MulAction.stabilizer b4b_Group x = ⊥ := by
    intro x hx
    have : x ∈ Set.range ι := by rw [hιr]; exact hx
    obtain ⟨u, rfl⟩ := this
    rw [eq_bot_iff]
    intro k hk
    rw [MulAction.mem_stabilizer_iff, ← hιeq] at hk
    exact hfree k u (hι.injective hk)
  have hfaith : FaithfulSMul b4b_Group C := by
    refine ⟨fun {k₁ k₂} h ↦ ?_⟩
    have h1 : (k₂⁻¹ * k₁) • ι u₀.1 = ι u₀.1 := by rw [mul_smul, h, inv_smul_smul]
    rw [← hιeq] at h1
    have := hfree _ u₀.1 (hι.injective h1)
    rwa [inv_mul_eq_one, eq_comm] at this
  have hmon : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) =
      MulOpposite.op (b4b_root i) := fun i ↦ by rw [hφeq, hφ]
  refine ⟨U, inferInstance, inferInstance, inferInstance, π, hπ, u₀, hmon, C, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hfaith, f, ι, hf, hgal, hsurj, hG, hι, hιr, hfι, hιeq, hstab, fun j ↦ ?_⟩
  obtain ⟨c, -, hc⟩ := hγ j
  have hcov := hπ.isCoveringMap
  let L := hcov.liftPath c.toContinuousMap u₀.1 (c.source.trans u₀.2.symm)
  have hL1 : L 1 = b4b_root j • u₀.1 := by
    have h1 := hcov.monodromy_eq_apply_one (γ := c) (e := u₀) (Γ := L)
      (hcov.liftPath_lifts _ _ _) (hcov.liftPath_zero _ _ _)
    have h2 := hπ.unop_fundamentalGroupToMulOpposite_smul (e := u₀) (γ := γ j)
    rw [hmon, MulOpposite.unop_op] at h2
    change L 1 = _
    rw [← h1, h2, ← hc]
    rfl
  exact mr_loops_positive_aux mr_base hbase y₀ γ hγ C b4b_Group hG f hf hgal hstab j c hc
    ⟨ι ∘ L, hι.continuous.comp L.continuous⟩ (b4b_root j) (fun t ↦ by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hfι]
      exact congrArg Subtype.val (congrFun (hcov.liftPath_lifts _ _ _) t))
    (by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hL1, hιeq]
      exact congrArg (b4b_root j • ·) (congrArg ι (hcov.liftPath_zero _ _ _).symm))

theorem mr_rootCover_family_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) :
    ∃ e : b6t_punctured mr_base ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere mr_base t x) ∧
      (e y₀ : OnePoint ℂ) = y₀ ∧
      ∀ i, mr_IsLoop t (e y₀) i (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ (γ i)) ∧
        (hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
          ⟨u₀.val, congrArg e u₀.property⟩
          (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ (γ i)) =
            MulOpposite.op (b4b_root i) := by
  have hbase : mr_base ∈ b6t_polydisc mr_base :=
    (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart_aux).1
  have hx₀ : (y₀ : OnePoint ℂ) ∉ ⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
      Metric.closedBall (mr_base i) (b6t_radius mr_base) := by
    obtain ⟨p, hp, -⟩ := hγ 0
    have h := (mr_curve_avoids_aux mr_base hbase 0 0).2
    rw [← hp 0, p.source] at h
    exact h
  obtain ⟨e, hes, hex, hm⟩ :=
    b6t_monodromy mr_base mr_base_mem_chart_aux t ht b4b_Group U π hπ y₀ u₀ hx₀
  refine ⟨e, hes, hex, fun i ↦ ⟨mr_loop_transport_aux t ht e hes y₀ i _ (hγ i), ?_⟩⟩
  rw [← hroot i, ← hm]
  rfl

end HodgeLean.Foundations.Program
