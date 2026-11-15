import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cFlatPaths

noncomputable section

namespace HodgeLean.Foundations.Program

open Filter
open scoped Topology

theorem b6m_cubic_flat_param (a : ℝ) :
    ∃ q : ℝ → ℝ, StrictMono q ∧ Function.Surjective q ∧ ContDiff ℝ 1 q ∧
      q 0 = a ∧ HasDerivAt q 0 0 ∧ (∀ x, q x ≠ a → 0 < deriv q x) := by
  have hm : StrictMono (fun x : ℝ ↦ x ^ 3) := (by decide : Odd 3).strictMono_pow
  have ht : Tendsto (fun x : ℝ ↦ x ^ 3) atTop atTop := tendsto_pow_atTop (by decide)
  have hb : Tendsto (fun x : ℝ ↦ x ^ 3) atBot atBot := by
    have H := tendsto_neg_atTop_atBot.comp (ht.comp tendsto_neg_atBot_atTop)
    have he : (Neg.neg ∘ (fun x : ℝ ↦ x ^ 3) ∘ Neg.neg) = (fun x : ℝ ↦ x ^ 3) := by
      funext x
      simp only [Function.comp_apply]
      ring
    rw [he] at H
    exact H
  have hs := (continuous_id.pow 3).surjective ht hb
  refine ⟨fun x ↦ x ^ 3 + a, fun _ _ h ↦ by simpa [add_comm] using add_lt_add_right (hm h) a, ?_,
    (contDiff_id.pow 3).add contDiff_const, by simp, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hs (y - a)
    change x ^ 3 = y - a at hx
    exact ⟨x, by simp [hx]⟩
  · simpa using (((hasDerivAt_id (0 : ℝ)).pow 3).add_const a)
  · intro x hx
    have hx0 : x ≠ 0 := by intro h; apply hx; simp [h]
    have hd : HasDerivAt (fun y : ℝ ↦ y ^ 3 + a) (3 * x ^ 2) x := by
      simpa using (((hasDerivAt_id x).pow 3).add_const a)
    rw [hd.deriv]
    positivity

theorem b6m_finite_flat_param (S : Set ℝ) (hS : S.Finite) :
    ∃ q : ℝ → ℝ, StrictMono q ∧ Function.Surjective q ∧ ContDiff ℝ 1 q ∧
      (∀ x, q x ∈ S → HasDerivAt q 0 x) ∧
      (∀ x, q x ∉ S → 0 < deriv q x) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨id, strictMono_id, Function.surjective_id, contDiff_id,
      by simp, by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨f, hfm, hfs, hfd, hflat, hfpos⟩ := ih
    obtain ⟨u, hu⟩ := hfs a
    obtain ⟨q, hqm, hqs, hqd, hq0, hqflat, hqpos⟩ := b6m_cubic_flat_param u
    refine ⟨f ∘ q, hfm.comp hqm, hfs.comp hqs, hfd.comp hqd, ?_, ?_⟩
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · have hx0 : x = 0 := hqm.injective (hfm.injective (by
          rw [hq0, hu]
          exact hx))
        subst x
        simpa using ((hfd.differentiable one_ne_zero (q 0)).hasDerivAt.comp 0 hqflat)
      · simpa using ((hflat (q x) hx).comp x (hqd.differentiable one_ne_zero x).hasDerivAt)
    · intro x hx
      have hf : f (q x) ∉ S := fun h ↦ hx (Set.mem_insert_of_mem a h)
      have hq : q x ≠ u := by
        intro h
        apply hx
        exact Set.mem_insert_iff.mpr (Or.inl (by simpa [h] using hu))
      rw [deriv_comp x (hfd.differentiable one_ne_zero (q x))
        (hqd.differentiable one_ne_zero x)]
      exact mul_pos (hfpos (q x) hf) (hqpos x hq)

theorem b6m_finite_flat_interval_param (S : Set ℝ) (hS : S.Finite) :
    ∃ q : ℝ → ℝ, StrictMono q ∧ ContDiff ℝ 1 q ∧ q 0 = 0 ∧ q 1 = 1 ∧
      (∀ x, q x ∈ S → HasDerivAt q 0 x) ∧
      (∀ x, q x ∉ S → 0 < deriv q x) := by
  obtain ⟨f, hm, hs, hd, hflat, hpos⟩ := b6m_finite_flat_param S hS
  obtain ⟨u, hu⟩ := hs 0
  obtain ⟨v, hv⟩ := hs 1
  have huv : u < v := hm.lt_iff_lt.mp (by rw [hu, hv]; norm_num)
  let L : ℝ → ℝ := fun x ↦ u + (v - u) * x
  have hLm : StrictMono L := by
    intro x y hxy
    dsimp [L]
    linarith [mul_lt_mul_of_pos_left hxy (sub_pos.mpr huv)]
  have hLd : ContDiff ℝ 1 L := contDiff_const.add (contDiff_const.mul contDiff_id)
  refine ⟨f ∘ L, hm.comp hLm, hd.comp hLd, ?_, ?_, ?_, ?_⟩
  · simpa [L] using hu
  · simpa [L] using hv
  · intro x hx
    simpa using (hflat (L x) hx).comp x (hLd.differentiable one_ne_zero x).hasDerivAt
  · intro x hx
    have hL : HasDerivAt L (v - u) x := by
      simpa [L] using ((hasDerivAt_id x).const_mul (v - u)).const_add u
    rw [deriv_comp x (hd.differentiable one_ne_zero (L x)) hL.differentiableAt,
      hL.deriv]
    exact mul_pos (hpos (L x) hx) (sub_pos.mpr huv)

theorem b6m_step_deriv_pos {x : ℝ} (hx : b3A_step x ∈ Set.Ioo 0 1) :
    0 < deriv b3A_step x := by
  have harg : 3 * x - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · by_contra h
      have hz : b3A_step x = 0 := Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)
      exact (ne_of_gt hx.1) hz
    · by_contra h
      have ho : b3A_step x = 1 := Real.smoothTransition.one_of_one_le (le_of_not_gt h)
      exact (ne_of_lt hx.2) ho
  obtain ⟨d, hd, hderiv⟩ := b3Rest_smoothTransition_hasDerivAt_pos harg
  have hinner : HasDerivAt (fun y : ℝ ↦ 3 * y - 1) 3 x := by
    simpa using ((hasDerivAt_id x).const_mul 3).sub_const 1
  have H : HasDerivAt b3A_step (d * 3) x := hderiv.comp x hinner
  rw [H.deriv]
  positivity

theorem b6m_finite_flat_step (S : Set ℝ) (hS : S.Finite) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ 1 σ ∧ (∀ x, σ x ∈ Set.Icc 0 1) ∧
      (∀ᶠ x in 𝓝 0, σ x = 0) ∧ (∀ᶠ x in 𝓝 1, σ x = 1) ∧
      (∀ x, σ x ∈ S → HasDerivAt σ 0 x) ∧
      (∀ x, σ x ∈ Set.Ioo 0 1 → σ x ∉ S → 0 < deriv σ x) := by
  obtain ⟨q, hm, hd, hq0, hq1, hflat, hpos⟩ := b6m_finite_flat_interval_param S hS
  refine ⟨q ∘ b3A_step, hd.comp b3A_step_contDiff, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change 0 ≤ q (b3A_step x) ∧ q (b3A_step x) ≤ 1
    rw [← hq0, ← hq1]
    exact ⟨hm.monotone (Real.smoothTransition.nonneg _),
      hm.monotone (Real.smoothTransition.le_one _)⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with x hx
    have hx' : b3A_step x = 0 := Real.smoothTransition.zero_of_nonpos (by
      have hx : x < 1 / 3 := hx
      linarith)
    simp [hx', hq0]
  · filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with x hx
    have hx' : b3A_step x = 1 := Real.smoothTransition.one_of_one_le (by
      have hx : 2 / 3 < x := hx
      linarith)
    simp [hx', hq1]
  · intro x hx
    simpa using (hflat (b3A_step x) hx).comp x
      (b3A_step_contDiff.differentiable one_ne_zero x).hasDerivAt
  · intro x hx hSx
    have hstep : b3A_step x ∈ Set.Ioo 0 1 := by
      constructor
      · apply hm.lt_iff_lt.mp
        simpa [hq0] using hx.1
      · apply hm.lt_iff_lt.mp
        simpa [hq1] using hx.2
    rw [deriv_comp x (hd.differentiable one_ne_zero (b3A_step x))
      (b3A_step_contDiff.differentiable one_ne_zero x)]
    exact mul_pos (hpos (b3A_step x) hSx) (b6m_step_deriv_pos hstep)

theorem b6m_path_finite_flat_reparam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ → E) (hp : ContDiff ℝ 1 p) (S : Set ℝ) (hS : S.Finite) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ 1 σ ∧ (∀ x, σ x ∈ Set.Icc 0 1) ∧
      (∀ᶠ x in 𝓝 0, σ x = 0) ∧ (∀ᶠ x in 𝓝 1, σ x = 1) ∧
      (∀ x, σ x ∈ S → deriv (p ∘ σ) x = 0) ∧
      (∀ x, σ x ∈ Set.Ioo 0 1 → σ x ∉ S → 0 < deriv σ x) := by
  obtain ⟨σ, hd, hr, h0, h1, hflat, hpos⟩ := b6m_finite_flat_step S hS
  refine ⟨σ, hd, hr, h0, h1, ?_, hpos⟩
  intro x hx
  have H := (hp.differentiable one_ne_zero (σ x)).hasFDerivAt.comp_hasDerivAt x (hflat x hx)
  simpa using H.deriv

theorem b6m_plane_finite_reparam (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (p : ℝ → ℂ) (hp : ContDiff ℝ 1 p)
    (hbad : {s : ℝ | s ∈ Set.Icc 0 1 ∧
      ∃ i, p s = b i ∨ dist (p s) (b i) = b6t_radius b}.Finite) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ 1 σ ∧ (∀ x, σ x ∈ Set.Icc 0 1) ∧
      (∀ᶠ x in 𝓝 0, σ x = 0) ∧ (∀ᶠ x in 𝓝 1, σ x = 1) ∧
      ContDiff ℝ 1 (b6t_plane b t ∘ (p ∘ σ)) ∧
      (∀ s, σ s ∈ Set.Ioo 0 1 →
        (∀ i, p (σ s) ≠ b i ∧ dist (p (σ s)) (b i) ≠ b6t_radius b) →
        0 < deriv σ s) := by
  obtain ⟨σ, hd, hr, h0, h1, hflat, hpos⟩ := b6m_path_finite_flat_reparam p hp _ hbad
  refine ⟨σ, hd, hr, h0, h1, b6m_plane_contDiff_comp_flat b t hb (hp.comp hd) ?_, ?_⟩
  · intro s i hi
    exact hflat s ⟨hr s, i, hi⟩
  · intro s hs hreg
    apply hpos s hs
    rintro ⟨_, i, hi | hi⟩
    · exact (hreg i).1 hi
    · exact (hreg i).2 hi

end HodgeLean.Foundations.Program
