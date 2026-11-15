import HodgeLean.Foundations.Program.CurveJacobianAPaths
import HodgeLean.Adapters.DegreeOneLatticeLoops

/-! # Track B3, lane Rest: approximation of continuous loops by `C¹` loops

A continuous loop `p` on a manifold is cut, by a Lebesgue number of a cover by chart balls, into
`N` arcs each inside one chart ball; replacing each arc by the chart segment between its endpoints
(reparametrized by a smooth step, so the pieces join with zero velocity) gives a `C¹` loop, and the
straight-line homotopy inside each chart ball deforms `p` into it. Homotopic loops have the same
singular periods (`loopPeriod_eq_of_homotopy`), so every continuous loop has a `C¹` loop with the
same `loopPeriod`.

The pieces are glued through `⌊u⌋` and `Int.fract u`: `b3Rest_continuous_floor` (continuity of a
family of maps on `[0, 1]` glued end to end) and `b3Rest_floorPath_contMDiff` (good paths glued end
to end form a `C¹` path).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Manifold Filter Topology Set Metric
open scoped ContDiff unitInterval

namespace HodgeLean.Foundations.Program

/-! ## Gluing maps along the integers -/

section Floor

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

theorem b3Rest_continuousOn_shift (G : ℤ → Y → ℝ → X)
    (hG : ∀ k, ContinuousOn (fun p : Y × ℝ ↦ G k p.1 p.2) (univ ×ˢ Icc 0 1)) (k : ℤ) (a : ℝ) :
    ContinuousOn (fun p : Y × ℝ ↦ G k p.1 (p.2 - a)) (univ ×ˢ Icc a (a + 1)) := by
  refine (hG k).comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn ?_
  rintro ⟨y, u⟩ ⟨-, hu1, hu2⟩
  dsimp only at hu1 hu2
  refine ⟨trivial, ?_, ?_⟩ <;> simp only [Pi.sub_apply] <;> linarith

/-- **Maps on `[0, 1]` glued end to end along the integers are continuous.** -/
theorem b3Rest_continuous_floor (G : ℤ → Y → ℝ → X)
    (hG : ∀ k, ContinuousOn (fun p : Y × ℝ ↦ G k p.1 p.2) (univ ×ˢ Icc 0 1))
    (hm : ∀ k y, G k y 1 = G (k + 1) y 0) :
    Continuous (fun p : Y × ℝ ↦ G ⌊p.2⌋ p.1 (Int.fract p.2)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨y, u⟩
  rcases em (∃ n : ℤ, u = n) with ⟨n, rfl⟩ | hu
  · have hS : ({p : Y × ℝ | p.2 ≤ n} ∪ {p | (n : ℝ) ≤ p.2}) = univ := by
      ext p
      simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      exact le_total _ _
    rw [ContinuousAt, ← nhdsWithin_univ, ← hS]
    refine ContinuousWithinAt.union ?_ ?_
    · -- from the left, the piece `n - 1`
      have h1 := b3Rest_continuousOn_shift G hG (n - 1) ((n : ℝ) - 1)
      have hopen : {p : Y × ℝ | (n : ℝ) - 1 < p.2} ∈ 𝓝 (y, (n : ℝ)) :=
        (isOpen_lt continuous_const continuous_snd).mem_nhds (by simp)
      have hmem : (univ ×ˢ Icc ((n : ℝ) - 1) (n - 1 + 1)) ∈
          𝓝[{p : Y × ℝ | p.2 ≤ n}] (y, (n : ℝ)) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hopen, self_mem_nhdsWithin] with p hp1 hp2
        have hp2' : p.2 ≤ n := hp2
        exact ⟨trivial, le_of_lt hp1, by linarith⟩
      have hc := (h1 (y, (n : ℝ)) ⟨trivial, by simp, by simp⟩).mono_of_mem_nhdsWithin hmem
      refine hc.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [mem_nhdsWithin_of_mem_nhds hopen, self_mem_nhdsWithin] with p hp1 hp2
        have hp1' : (n : ℝ) - 1 < p.2 := hp1
        have hp2' : p.2 ≤ n := hp2
        rcases hp2'.lt_or_eq with hlt | heq
        · have hfl : ⌊p.2⌋ = n - 1 := by
            rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
          rw [hfl, Int.fract, hfl]
          push_cast
          rfl
        · rw [heq, Int.floor_intCast, Int.fract_intCast]
          have := hm (n - 1) p.1
          rw [sub_add_cancel] at this
          rw [← this]
          congr 1
          ring
      · simp only [Int.floor_intCast, Int.fract_intCast]
        have := hm (n - 1) y
        rw [sub_add_cancel] at this
        rw [← this]
        congr 1
        ring
    · -- from the right, the piece `n`
      have h1 := b3Rest_continuousOn_shift G hG n (n : ℝ)
      have hopen : {p : Y × ℝ | p.2 < (n : ℝ) + 1} ∈ 𝓝 (y, (n : ℝ)) :=
        (isOpen_lt continuous_snd continuous_const).mem_nhds (by simp)
      have hmem : (univ ×ˢ Icc (n : ℝ) (n + 1)) ∈ 𝓝[{p : Y × ℝ | (n : ℝ) ≤ p.2}] (y, (n : ℝ)) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hopen, self_mem_nhdsWithin] with p hp1 hp2
        exact ⟨trivial, hp2, hp1.le⟩
      have hc := (h1 (y, (n : ℝ)) ⟨trivial, by simp, by simp⟩).mono_of_mem_nhdsWithin hmem
      refine hc.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [mem_nhdsWithin_of_mem_nhds hopen, self_mem_nhdsWithin] with p hp1 hp2
        have hfl : ⌊p.2⌋ = n := by
          rw [Int.floor_eq_iff]; exact ⟨hp2, hp1⟩
        rw [hfl, Int.fract, hfl]
      · simp
  · have hu' : (u : ℝ) ≠ ⌊u⌋ := fun h ↦ hu ⟨_, h⟩
    have hlt : (⌊u⌋ : ℝ) < u := lt_of_le_of_ne (Int.floor_le u) (Ne.symm hu')
    have hlt' : u < ⌊u⌋ + 1 := Int.lt_floor_add_one u
    have h1 := b3Rest_continuousOn_shift G hG ⌊u⌋ (⌊u⌋ : ℝ)
    have hopen : {p : Y × ℝ | (⌊u⌋ : ℝ) < p.2 ∧ p.2 < ⌊u⌋ + 1} ∈ 𝓝 (y, u) :=
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)).mem_nhds ⟨hlt, hlt'⟩
    have hc := h1.continuousAt (x := (y, u)) (Filter.mem_of_superset hopen
      (fun p hp ↦ ⟨trivial, hp.1.le, hp.2.le⟩))
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [hopen] with p hp
    have hfl : ⌊p.2⌋ = ⌊u⌋ := by
      rw [Int.floor_eq_iff]; exact ⟨hp.1.le, hp.2⟩
    show G ⌊p.2⌋ p.1 (Int.fract p.2) = G ⌊u⌋ p.1 (p.2 - ⌊u⌋)
    rw [hfl, Int.fract, hfl]

end Floor

/-! ## Good paths glued along the integers -/

section Glue

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C]

/-- **Good paths glued end to end along the integers form a `C¹` path.** Near an integer `n` the
glued path is constant (equal to `z n`), and between integers it is a translate of one path. -/
theorem b3Rest_floorPath_contMDiff (γ : ℤ → ℝ → C) (z : ℤ → C)
    (hγ : ∀ k, b3A_IsGoodPath (E := E) (γ k) (z k) (z (k + 1))) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun u ↦ γ ⌊u⌋ (Int.fract u)) := by
  intro u
  rcases em (∃ n : ℤ, u = n) with ⟨n, rfl⟩ | hu
  · refine contMDiffAt_const (c := z n).congr_of_eventuallyEq ?_
    have h0 : ∀ᶠ v in 𝓝 (n : ℝ), γ n (v - n) = z n := by
      have ht : Tendsto (fun v : ℝ ↦ v - n) (𝓝 (n : ℝ)) (𝓝 0) :=
        (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
      exact ht.eventually (hγ n).2.1
    have h1 : ∀ᶠ v in 𝓝 (n : ℝ), γ (n - 1) (v - (n - 1)) = z n := by
      have ht : Tendsto (fun v : ℝ ↦ v - (n - 1)) (𝓝 (n : ℝ)) (𝓝 1) :=
        (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
      have := ht.eventually (hγ (n - 1)).2.2
      simpa only [sub_add_cancel] using this
    have h2 : Ioo ((n : ℝ) - 1) (n + 1) ∈ 𝓝 (n : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [h0, h1, h2] with v hv0 hv1 hv2
    rcases le_or_gt (n : ℝ) v with hle | hlt
    · have hfl : ⌊v⌋ = n := by rw [Int.floor_eq_iff]; exact ⟨hle, hv2.2⟩
      show γ ⌊v⌋ (Int.fract v) = z n
      rw [Int.fract, hfl, hv0]
    · have hfl : ⌊v⌋ = n - 1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hv2.1]
      show γ ⌊v⌋ (Int.fract v) = z n
      rw [Int.fract, hfl]
      push_cast
      exact hv1
  · have hu' : (u : ℝ) ≠ ⌊u⌋ := fun h ↦ hu ⟨_, h⟩
    have hlt : (⌊u⌋ : ℝ) < u := lt_of_le_of_ne (Int.floor_le u) (Ne.symm hu')
    have hlt' : u < ⌊u⌋ + 1 := Int.lt_floor_add_one u
    have hd : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun v ↦ γ ⌊u⌋ (v - ⌊u⌋)) u :=
      ((hγ ⌊u⌋).1 (u - ⌊u⌋)).comp u
        ((contDiff_id.sub contDiff_const).contMDiff u)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hlt hlt'] with v hv
    have hfl : ⌊v⌋ = ⌊u⌋ := by rw [Int.floor_eq_iff]; exact ⟨hv.1.le, hv.2⟩
    show γ ⌊v⌋ (Int.fract v) = γ ⌊u⌋ (v - ⌊u⌋)
    rw [Int.fract, hfl]

end Glue

/-! ## A cover of a loop by chart balls -/

section Cover

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C]

omit [NormedSpace ℂ E] in
/-- **Cutting a loop into arcs inside chart balls**: for a continuous `1`-periodic `P`, some
`N > 0` and `N`-periodic choices of charts `x k` and radii `r k` put `P [k/N, (k+1)/N]` inside the
ball of radius `r k` of the chart at `x k`. -/
theorem b3Rest_exists_chartCover (P : ℝ → C) (hP : Continuous P) (hper : Function.Periodic P 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ x : ℤ → C, ∃ r : ℤ → ℝ, (∀ k, x (k + N) = x k) ∧
      (∀ k, r (k + N) = r k) ∧
      (∀ k, ball (chartAt E (x k) (x k)) (r k) ⊆ (chartAt E (x k)).target) ∧
      ∀ k : ℤ, ∀ τ ∈ Icc (0 : ℝ) 1, P ((k + τ) / N) ∈ (chartAt E (x k)).source ∧
        chartAt E (x k) (P ((k + τ) / N)) ∈ ball (chartAt E (x k) (x k)) (r k) := by
  have hρ : ∀ y : C, ∃ ρ > 0, ball (chartAt E y y) ρ ⊆ (chartAt E y).target := fun y ↦
    Metric.isOpen_iff.1 (chartAt E y).open_target _ ((chartAt E y).map_source (mem_chart_source E y))
  choose ρ hρ0 hρ using hρ
  let U : C → Set C := fun y ↦
    (chartAt E y).source ∩ (chartAt E y) ⁻¹' ball (chartAt E y y) (ρ y)
  have hUo : ∀ y, IsOpen (P ⁻¹' U y) := fun y ↦
    ((chartAt E y).continuousOn.isOpen_inter_preimage (chartAt E y).open_source
      isOpen_ball).preimage hP
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ y, P ⁻¹' U y := fun t _ ↦
    mem_iUnion.2 ⟨P t, mem_chart_source E _, by simp [hρ0]⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hUo hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℝ) < N := by positivity
  have hNz : (0 : ℤ) < N := by positivity
  have hsel : ∀ m : ℤ, ∃ y : C, ball ((m % (N : ℤ) : ℤ) / (N : ℝ)) δ ⊆ P ⁻¹' U y := by
    intro m
    apply hball
    have h0 : (0 : ℝ) ≤ ((m % (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg m hNz.ne'
    have h1 : ((m % (N : ℤ) : ℤ) : ℝ) < N := by exact_mod_cast Int.emod_lt_of_pos m hNz
    exact ⟨div_nonneg h0 hNpos.le, (div_le_one hNpos).2 h1.le⟩
  choose y hy using hsel
  refine ⟨N, Nat.succ_pos n, fun k ↦ y (k % (N : ℤ)), fun k ↦ ρ (y (k % (N : ℤ))), ?_, ?_,
    fun k ↦ hρ _, ?_⟩
  · intro k; simp only [Int.add_emod_right]
  · intro k; simp only [Int.add_emod_right]
  · intro k τ hτ
    set m := k % (N : ℤ)
    set q := k / (N : ℤ)
    have hk : (k : ℝ) = N * q + m := by exact_mod_cast (Int.mul_ediv_add_emod k N).symm
    have hPe : P ((k + τ) / N) = P ((m + τ) / N) := by
      have : (k + τ) / N = (m + τ) / N + (q : ℝ) * 1 := by
        rw [hk]; field_simp; ring
      rw [this]
      exact (hper.int_mul q) _
    have hmem : (m + τ) / (N : ℝ) ∈ ball ((m : ℝ) / N) δ := by
      rw [mem_ball, Real.dist_eq, add_div, add_sub_cancel_left, abs_of_nonneg
        (div_nonneg hτ.1 hNpos.le)]
      calc τ / N ≤ 1 / N := div_le_div_of_nonneg_right hτ.2 hNpos.le
        _ = 1 / ((n : ℝ) + 1) := by rw [hNdef]; push_cast; ring
        _ < δ := hn
    have hc : m % (N : ℤ) = m := Int.emod_emod _ _
    have := hy m (by rw [hc]; exact hmem)
    rw [hPe]
    exact this

end Cover

/-! ## The polygonal loop of a cover and the homotopy to it -/

section Approx

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- A cover of a `1`-periodic path by `N` arcs inside chart balls, as given by
`b3Rest_exists_chartCover`. -/
structure b3Rest_Cover (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] {C : Type}
    [TopologicalSpace C] [ChartedSpace E C] (P : ℝ → C) where
  N : ℕ
  pos : 0 < N
  x : ℤ → C
  r : ℤ → ℝ
  x_add : ∀ k, x (k + N) = x k
  r_add : ∀ k, r (k + N) = r k
  ball_sub : ∀ k, ball (chartAt E (x k) (x k)) (r k) ⊆ (chartAt E (x k)).target
  mem : ∀ k : ℤ, ∀ τ ∈ Icc (0 : ℝ) 1, P ((k + τ) / N) ∈ (chartAt E (x k)).source ∧
    chartAt E (x k) (P ((k + τ) / N)) ∈ ball (chartAt E (x k) (x k)) (r k)

namespace b3Rest_Cover

variable {P : ℝ → C} (K : b3Rest_Cover E P)

/-- The initial vertex of the `k`-th arc, in the chart of the arc. -/
def a (k : ℤ) : E := chartAt E (K.x k) (P (k / K.N))

/-- The final vertex of the `k`-th arc, in the chart of the arc. -/
def b (k : ℤ) : E := chartAt E (K.x k) (P ((k + 1) / K.N))

theorem mem_zero (k : ℤ) : P (k / K.N) ∈ (chartAt E (K.x k)).source ∧
    K.a k ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
  have := K.mem k 0 ⟨le_rfl, zero_le_one⟩
  rw [add_zero] at this
  exact this

theorem mem_one (k : ℤ) : P ((k + 1) / K.N) ∈ (chartAt E (K.x k)).source ∧
    K.b k ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) :=
  K.mem k 1 ⟨zero_le_one, le_rfl⟩

/-- The `k`-th chart segment, from `P (k / N)` to `P ((k + 1) / N)`. -/
def seg (k : ℤ) (τ : ℝ) : C :=
  (chartAt E (K.x k)).symm (K.a k + Real.smoothTransition (3 * τ - 1) • (K.b k - K.a k))

theorem seg_isGoodPath (k : ℤ) :
    b3A_IsGoodPath (E := E) (K.seg k) (P (k / K.N)) (P (((k + 1 : ℤ) : ℝ) / K.N)) := by
  have h := b3A_isGoodPath_segment (K.x k) (K.a k) (K.b k)
    (((convex_ball _ _).segment_subset (K.mem_zero k).2 (K.mem_one k).2).trans (K.ball_sub k))
  have e1 : (chartAt E (K.x k)).symm (K.a k) = P (k / K.N) :=
    (chartAt E (K.x k)).left_inv (K.mem_zero k).1
  have e2 : (chartAt E (K.x k)).symm (K.b k) = P (((k + 1 : ℤ) : ℝ) / K.N) := by
    push_cast
    exact (chartAt E (K.x k)).left_inv (K.mem_one k).1
  rw [e1, e2] at h
  exact h

/-- The straight-line homotopy in the chart of the `k`-th arc, from the arc to its segment. -/
def piece (k : ℤ) (s : unitInterval) (τ : ℝ) : C :=
  (chartAt E (K.x k)).symm ((1 - (s : ℝ)) • chartAt E (K.x k) (P ((k + τ) / K.N)) +
    (s : ℝ) • (K.a k + Real.smoothTransition (3 * τ - 1) • (K.b k - K.a k)))

theorem piece_zero (k : ℤ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    K.piece k 0 τ = P ((k + τ) / K.N) := by
  simp only [piece, Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
  exact (chartAt E (K.x k)).left_inv (K.mem k τ hτ).1

theorem piece_one (k : ℤ) (τ : ℝ) : K.piece k 1 τ = K.seg k τ := by
  simp only [piece, seg, Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]

theorem piece_one_eq (k : ℤ) (s : unitInterval) :
    K.piece k s 1 = P ((k + 1) / K.N) := by
  have h1 : Real.smoothTransition (3 * 1 - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by norm_num)
  simp only [piece, h1, one_smul, add_sub_cancel]
  rw [show chartAt E (K.x k) (P ((k + 1) / K.N)) = K.b k from rfl, ← add_smul, sub_add_cancel,
    one_smul]
  exact (chartAt E (K.x k)).left_inv (K.mem_one k).1

theorem piece_zero_eq (k : ℤ) (s : unitInterval) :
    K.piece k s 0 = P (k / K.N) := by
  have h0 : Real.smoothTransition (3 * 0 - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by norm_num)
  simp only [piece, h0, zero_smul, add_zero]
  rw [show chartAt E (K.x k) (P (k / K.N)) = K.a k from rfl, ← add_smul, sub_add_cancel,
    one_smul]
  exact (chartAt E (K.x k)).left_inv (K.mem_zero k).1

theorem piece_match (k : ℤ) (s : unitInterval) : K.piece k s 1 = K.piece (k + 1) s 0 := by
  rw [piece_one_eq, piece_zero_eq]
  push_cast
  rfl

theorem continuousOn_piece (hPc : Continuous P) (k : ℤ) :
    ContinuousOn (fun p : unitInterval × ℝ ↦ K.piece k p.1 p.2) (univ ×ˢ Icc 0 1) := by
  have hσ : Continuous fun τ : ℝ ↦ Real.smoothTransition (3 * τ - 1) :=
    Real.smoothTransition.continuous.comp ((continuous_const.mul continuous_id).sub continuous_const)
  have hP : ContinuousOn (fun p : unitInterval × ℝ ↦ chartAt E (K.x k) (P ((k + p.2) / K.N)))
      (univ ×ˢ Icc 0 1) := by
    refine (chartAt E (K.x k)).continuousOn.comp
      (hPc.comp ((continuous_const.add continuous_snd).div_const _)).continuousOn ?_
    rintro ⟨s, τ⟩ ⟨-, hτ⟩
    exact (K.mem k τ hτ).1
  have hs : Continuous fun p : unitInterval × ℝ ↦ (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hg : ContinuousOn (fun p : unitInterval × ℝ ↦
      (1 - (p.1 : ℝ)) • chartAt E (K.x k) (P ((k + p.2) / K.N)) +
        (p.1 : ℝ) • (K.a k + Real.smoothTransition (3 * p.2 - 1) • (K.b k - K.a k)))
      (univ ×ˢ Icc 0 1) :=
    ((continuous_const.sub hs).continuousOn.smul hP).add
      (hs.smul (continuous_const.add ((hσ.comp continuous_snd).smul continuous_const))).continuousOn
  refine (chartAt E (K.x k)).continuousOn_symm.comp hg ?_
  rintro ⟨s, τ⟩ ⟨-, hτ⟩
  apply K.ball_sub k
  exact convex_ball _ _ (K.mem k τ hτ).2
    (Convex.add_smul_sub_mem (convex_ball _ _) (K.mem_zero k).2 (K.mem_one k).2
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
    (sub_nonneg.2 s.2.2) s.2.1 (by ring)

theorem P_add (hper : Function.Periodic P 1) (k : ℤ) (τ : ℝ) :
    P ((((k + K.N : ℤ) : ℝ) + τ) / K.N) = P ((k + τ) / K.N) := by
  have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
  have : (((k + K.N : ℤ) : ℝ) + τ) / K.N = (k + τ) / K.N + 1 := by
    push_cast; field_simp; ring
  rw [this, hper]

theorem a_add (hper : Function.Periodic P 1) (k : ℤ) : K.a (k + K.N) = K.a k := by
  have := K.P_add hper k 0
  simp only [add_zero] at this
  simp only [a, K.x_add, this]

theorem b_add (hper : Function.Periodic P 1) (k : ℤ) : K.b (k + K.N) = K.b k := by
  have := K.P_add hper k 1
  simp only [b, K.x_add]
  push_cast at this ⊢
  rw [this]

theorem seg_add (hper : Function.Periodic P 1) (k : ℤ) : K.seg (k + K.N) = K.seg k := by
  funext τ
  simp only [seg, K.x_add, K.a_add hper, K.b_add hper]

theorem piece_add (hper : Function.Periodic P 1) (k : ℤ) : K.piece (k + K.N) = K.piece k := by
  funext s τ
  simp only [piece, K.x_add, K.a_add hper, K.b_add hper, K.P_add hper]

/-- The polygonal loop of the cover, `t ↦ seg ⌊N t⌋ (fract (N t))`. -/
def loop (t : ℝ) : C := K.seg ⌊(K.N : ℝ) * t⌋ (Int.fract ((K.N : ℝ) * t))

/-- The homotopy from `P` to the polygonal loop. -/
def hom (p : unitInterval × ℝ) : C := K.piece ⌊(K.N : ℝ) * p.2⌋ p.1 (Int.fract ((K.N : ℝ) * p.2))

theorem loop_periodic (hper : Function.Periodic P 1) : Function.Periodic K.loop 1 := by
  intro t
  simp only [loop, mul_add, mul_one]
  rw [Int.floor_add_natCast, Int.fract_add_natCast]
  rw [K.seg_add hper]

theorem hom_periodic (hper : Function.Periodic P 1) (s : unitInterval) :
    Function.Periodic (fun t ↦ K.hom (s, t)) 1 := by
  intro t
  simp only [hom, mul_add, mul_one]
  rw [Int.floor_add_natCast, Int.fract_add_natCast]
  rw [K.piece_add hper]

theorem loop_contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 K.loop := by
  have h := b3Rest_floorPath_contMDiff K.seg (fun k ↦ P (k / K.N)) K.seg_isGoodPath
  exact h.comp ((contDiff_const.mul contDiff_id).contMDiff)

theorem continuous_hom (hPc : Continuous P) : Continuous K.hom := by
  have h := b3Rest_continuous_floor K.piece (K.continuousOn_piece hPc) K.piece_match
  exact h.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))

theorem hom_zero (t : ℝ) : K.hom (0, t) = P t := by
  have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
  simp only [hom]
  rw [K.piece_zero _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, Int.floor_add_fract]
  congr 1
  field_simp

theorem hom_one (t : ℝ) : K.hom (1, t) = K.loop t := by
  simp only [hom, loop, piece_one]

end b3Rest_Cover

/-- **Every continuous loop is homotopic to a `C¹` loop.** -/
theorem b3Rest_exists_homotopic_smoothLoop (p : C(UnitAddCircle, C)) :
    ∃ (γ : b3_SmoothLoop E C) (q : C(UnitAddCircle, C)),
      (∀ t : ℝ, γ.1 t = q t) ∧ Nonempty (ContinuousMap.Homotopy p q) := by
  let P : ℝ → C := fun t ↦ p t
  have hPc : Continuous P := p.continuous.comp (AddCircle.continuous_mk' 1)
  have hper : Function.Periodic P 1 := fun t ↦ by
    simp only [P, AddCircle.coe_add_period]
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ := b3Rest_exists_chartCover (E := E) P hPc hper
  let K : b3Rest_Cover E P := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  have hq : Continuous (K.loop_periodic hper).lift := by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact (K.loop_contMDiff.continuous)
  let q : C(UnitAddCircle, C) := ⟨(K.loop_periodic hper).lift, hq⟩
  let Hc : unitInterval × UnitAddCircle → C := fun z ↦ (K.hom_periodic hper z.1).lift z.2
  have hHc : Continuous Hc := by
    rw [← (IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff]
    exact K.continuous_hom hPc
  refine ⟨⟨K.loop, K.loop_periodic hper, K.loop_contMDiff⟩, q, fun t ↦ rfl,
    ⟨{ toFun := Hc
       continuous_toFun := hHc
       map_zero_left := fun z ↦ ?_
       map_one_left := fun z ↦ ?_ }⟩⟩
  · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact K.hom_zero t
  · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact K.hom_one t

/-- **Every continuous loop has a `C¹` loop with the same singular periods.** -/
theorem b3Rest_exists_smoothLoop (p : C(UnitAddCircle, C)) :
    ∃ (γ : b3_SmoothLoop E C) (q : C(UnitAddCircle, C)),
      (∀ t : ℝ, γ.1 t = q t) ∧ HodgeLean.Adapters.loopPeriod q = HodgeLean.Adapters.loopPeriod p := by
  obtain ⟨γ, q, hγq, ⟨H⟩⟩ := b3Rest_exists_homotopic_smoothLoop (E := E) p
  exact ⟨γ, q, hγq, (HodgeLean.Adapters.loopPeriod_eq_of_homotopy H).symm⟩

end Approx

end HodgeLean.Foundations.Program
