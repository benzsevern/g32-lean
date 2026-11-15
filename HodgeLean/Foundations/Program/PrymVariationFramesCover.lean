import HodgeLean.Foundations.Program.PrymVariationFramesSlice
import HodgeLean.Foundations.Program.PrymVariationFramesLoops

noncomputable section
open Set Filter Topology Metric
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem b63e_exists_chartCover {X M : Type*} [TopologicalSpace X] [PseudoMetricSpace M]
    (ch : X → OpenPartialHomeomorph X M) (hch : ∀ y, y ∈ (ch y).source)
    (P : ℝ → X) (hP : Continuous P) (hper : Function.Periodic P 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ x : ℤ → X, ∃ r : ℤ → ℝ, (∀ k, x (k + N) = x k) ∧
      (∀ k, r (k + N) = r k) ∧
      (∀ k, ball (ch (x k) (x k)) (r k) ⊆ (ch (x k)).target) ∧
      ∀ k : ℤ, ∀ τ ∈ Icc (0 : ℝ) 1, P ((k + τ) / N) ∈ (ch (x k)).source ∧
        ch (x k) (P ((k + τ) / N)) ∈ ball (ch (x k) (x k)) (r k) := by
  have hρ : ∀ y : X, ∃ ρ > 0, ball (ch y y) ρ ⊆ (ch y).target := fun y ↦
    Metric.isOpen_iff.1 (ch y).open_target _ ((ch y).map_source (hch y))
  choose ρ hρ0 hρ using hρ
  let U : X → Set X := fun y ↦ (ch y).source ∩ (ch y) ⁻¹' ball (ch y y) (ρ y)
  have hUo : ∀ y, IsOpen (P ⁻¹' U y) := fun y ↦
    ((ch y).continuousOn.isOpen_inter_preimage (ch y).open_source isOpen_ball).preimage hP
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ y, P ⁻¹' U y := fun t _ ↦
    mem_iUnion.2 ⟨P t, hch _, by simp [hρ0]⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hUo hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℝ) < N := by positivity
  have hNz : (0 : ℤ) < N := by positivity
  have hsel : ∀ m : ℤ, ∃ y : X, ball ((m % (N : ℤ) : ℤ) / (N : ℝ)) δ ⊆ P ⁻¹' U y := by
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

/-- A cover of a loop in the parameter fibre over `u₀` of the total space by arcs inside balls of
parameter charts. -/
structure b63e_Cover (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)] (u₀ : Fin 10 → ℂ)
    (Γ : ℝ → b6t_polydisc b × C) where
  N : ℕ
  pos : 0 < N
  φ : ℤ → OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)
  mem_atlas : ∀ k, φ k ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)
  fp : ∀ k, ∀ y ∈ (φ k).source, (φ k y).1 = y.1.val
  ctr : ℤ → (Fin 10 → ℂ) × ℂ
  r : ℤ → ℝ
  φ_add : ∀ k, φ (k + N) = φ k
  ctr_add : ∀ k, ctr (k + N) = ctr k
  r_add : ∀ k, r (k + N) = r k
  ball_sub : ∀ k, ball (ctr k) (r k) ⊆ (φ k).target
  mem : ∀ k : ℤ, ∀ τ ∈ Icc (0 : ℝ) 1, Γ ((k + τ) / N) ∈ (φ k).source ∧
    φ k (Γ ((k + τ) / N)) ∈ ball (ctr k) (r k)
  fib : ∀ τ, (Γ τ).1.val = u₀
  per : Function.Periodic Γ 1
  cont : Continuous Γ

theorem b63e_exists_cover (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (hA : ∀ q : b6t_polydisc b × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (u₀ : b6t_polydisc b) {c : ℝ → C} (hc : Continuous c) (hcp : Function.Periodic c 1) :
    Nonempty (b63e_Cover b C u₀.val (fun τ ↦ (u₀, c τ))) := by
  choose ch hch hsrc hfp using hA
  have hΓ : Continuous (fun τ ↦ ((u₀, c τ) : b6t_polydisc b × C)) :=
    continuous_const.prodMk hc
  have hΓp : Function.Periodic (fun τ ↦ ((u₀, c τ) : b6t_polydisc b × C)) 1 := fun τ ↦ by
    simp only [hcp τ]
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ := b63e_exists_chartCover ch hsrc _ hΓ hΓp
  exact ⟨{
    N := N
    pos := hN
    φ := fun k ↦ ch (x k)
    mem_atlas := fun k ↦ hch _
    fp := fun k ↦ hfp _
    ctr := fun k ↦ ch (x k) (x k)
    r := r
    φ_add := fun k ↦ by simp only [hx]
    ctr_add := fun k ↦ by simp only [hx]
    r_add := hr
    ball_sub := hball
    mem := hmem
    fib := fun _ ↦ rfl
    per := hΓp
    cont := hΓ }⟩

theorem b63e_int_periodic_emod {α : Type*} (f : ℤ → α) (N : ℕ) (h : ∀ k, f (k + N) = f k)
    (k : ℤ) : f k = f (k % (N : ℤ)) := by
  have hp : Function.Periodic f (N : ℤ) := h
  rw [Int.emod_def, mul_comm]
  exact (hp.sub_int_mul_eq (k / N)).symm

namespace b63e_Cover

variable {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
  [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)] {u₀ : Fin 10 → ℂ}
  {Γ : ℝ → b6t_polydisc b × C} (K : b63e_Cover b C u₀ Γ)

/-- The vertical coordinate of the `k`-th vertex in the `k`-th chart. -/
def a (k : ℤ) : ℂ := (K.φ k (Γ (k / K.N))).2

/-- The `k`-th vertex over the parameter `u`. -/
def v (k : ℤ) (u : Fin 10 → ℂ) : b6t_polydisc b × C := (K.φ k).symm (u, K.a k)

/-- The vertical coordinate of the `(k + 1)`-st vertex in the `k`-th chart. -/
def bb (k : ℤ) (u : Fin 10 → ℂ) : ℂ := (K.φ k (K.v (k + 1) u)).2

/-- The `k`-th chart segment in vertical coordinates. -/
def w (k : ℤ) (u : Fin 10 → ℂ) (τ : ℝ) : ℂ :=
  K.a k + (b3A_step τ : ℂ) * (K.bb k u - K.a k)

/-- The `k`-th chart segment in the total space. -/
def seg (k : ℤ) (u : Fin 10 → ℂ) (τ : ℝ) : b6t_polydisc b × C := (K.φ k).symm (u, K.w k u τ)

/-- The parameters over which the vertices and segments stay in the chart balls. -/
def cond (u : Fin 10 → ℂ) (k : ℤ) : Prop :=
  (u, K.a k) ∈ ball (K.ctr k) (K.r k) ∧ K.v (k + 1) u ∈ (K.φ k).source ∧
    (u, K.bb k u) ∈ ball (K.ctr k) (K.r k)

theorem Γ_add (k : ℤ) (τ : ℝ) : Γ ((((k + K.N : ℤ) : ℝ) + τ) / K.N) = Γ ((k + τ) / K.N) := by
  have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
  have : (((k + K.N : ℤ) : ℝ) + τ) / K.N = (k + τ) / K.N + 1 := by
    push_cast; field_simp; ring
  rw [this, K.per]

theorem a_add (k : ℤ) : K.a (k + K.N) = K.a k := by
  have := K.Γ_add k 0
  simp only [add_zero] at this
  simp only [a, K.φ_add, this]

theorem v_add (k : ℤ) (u : Fin 10 → ℂ) : K.v (k + K.N) u = K.v k u := by
  simp only [v, K.φ_add, K.a_add]

theorem bb_add (k : ℤ) (u : Fin 10 → ℂ) : K.bb (k + K.N) u = K.bb k u := by
  simp only [bb, K.φ_add, add_right_comm k (K.N : ℤ) 1, K.v_add]

theorem w_add (k : ℤ) (u : Fin 10 → ℂ) : K.w (k + K.N) u = K.w k u := by
  funext τ
  simp only [w, K.a_add, K.bb_add]

theorem seg_add (k : ℤ) (u : Fin 10 → ℂ) : K.seg (k + K.N) u = K.seg k u := by
  funext τ
  simp only [seg, K.φ_add, K.w_add]

theorem cond_add (u : Fin 10 → ℂ) (k : ℤ) : K.cond u (k + K.N) = K.cond u k := by
  simp only [cond, K.a_add, K.ctr_add, K.r_add, K.φ_add, K.bb_add, add_right_comm k (K.N : ℤ) 1,
    K.v_add]

theorem cond_iff (u : Fin 10 → ℂ) :
    (∀ k, K.cond u k) ↔ ∀ k ∈ Finset.range K.N, K.cond u k := by
  refine ⟨fun h k _ ↦ h k, fun h k ↦ ?_⟩
  rw [b63e_int_periodic_emod (K.cond u) K.N (K.cond_add u) k]
  have h0 : 0 ≤ k % (K.N : ℤ) := Int.emod_nonneg k (by exact_mod_cast K.pos.ne')
  have h1 : k % (K.N : ℤ) < K.N := Int.emod_lt_of_pos k (by exact_mod_cast K.pos)
  have := h (k % (K.N : ℤ)).toNat (Finset.mem_range.2 (by omega))
  rwa [Int.toNat_of_nonneg h0] at this

theorem mem_zero (k : ℤ) : Γ (k / K.N) ∈ (K.φ k).source ∧
    K.φ k (Γ (k / K.N)) ∈ ball (K.ctr k) (K.r k) := by
  have := K.mem k 0 ⟨le_rfl, zero_le_one⟩
  rw [add_zero] at this
  exact this

theorem mem_one (k : ℤ) : Γ ((k + 1) / K.N) ∈ (K.φ k).source ∧
    K.φ k (Γ ((k + 1) / K.N)) ∈ ball (K.ctr k) (K.r k) :=
  K.mem k 1 ⟨zero_le_one, le_rfl⟩

theorem φ_Γ (k : ℤ) : K.φ k (Γ (k / K.N)) = (u₀, K.a k) := by
  refine Prod.ext ?_ rfl
  rw [K.fp k _ (K.mem_zero k).1, K.fib]

theorem v_u₀ (k : ℤ) : K.v k u₀ = Γ (k / K.N) := by
  rw [v, ← K.φ_Γ k]
  exact (K.φ k).left_inv (K.mem_zero k).1

theorem φ_Γ_one (k : ℤ) : K.φ k (Γ ((k + 1) / K.N)) = (u₀, K.bb k u₀) := by
  have hv : K.v (k + 1) u₀ = Γ ((k + 1) / K.N) := by
    rw [K.v_u₀]; push_cast; rfl
  refine Prod.ext ?_ ?_
  · rw [K.fp k _ (K.mem_one k).1, K.fib]
  · rw [bb, hv]

theorem cond_u₀ (k : ℤ) : K.cond u₀ k := by
  have hv : K.v (k + 1) u₀ = Γ ((k + 1) / K.N) := by
    rw [K.v_u₀]; push_cast; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← K.φ_Γ k]; exact (K.mem_zero k).2
  · rw [hv]; exact (K.mem_one k).1
  · rw [← K.φ_Γ_one k]; exact (K.mem_one k).2

theorem continuousAt_v (k : ℤ) {u : Fin 10 → ℂ} (hu : (u, K.a k) ∈ ball (K.ctr k) (K.r k)) :
    ContinuousAt (K.v k) u :=
  ContinuousAt.comp (g := (K.φ k).symm) (f := fun u' : Fin 10 → ℂ ↦ (u', K.a k))
    ((K.φ k).continuousAt_symm (K.ball_sub k hu))
    (continuous_id.prodMk continuous_const).continuousAt

theorem continuousAt_bb (k : ℤ) {u : Fin 10 → ℂ} (hu : K.cond u (k + 1))
    (hu' : K.cond u k) : ContinuousAt (K.bb k) u :=
  continuous_snd.continuousAt.comp
    (((K.φ k).continuousAt hu'.2.1).comp (K.continuousAt_v (k + 1) hu.1))

theorem cond_nhds : ∀ᶠ u in 𝓝 u₀, ∀ k, K.cond u k := by
  have hk : ∀ k, ∀ᶠ u in 𝓝 u₀, K.cond u k := by
    intro k
    have h0 := K.cond_u₀ k
    have h1 := K.cond_u₀ (k + 1)
    have hc1 : ∀ᶠ u in 𝓝 u₀, (u, K.a k) ∈ ball (K.ctr k) (K.r k) :=
      ((continuous_id.prodMk continuous_const).tendsto u₀).eventually (isOpen_ball.mem_nhds h0.1)
    have hc2 : ∀ᶠ u in 𝓝 u₀, K.v (k + 1) u ∈ (K.φ k).source :=
      (K.continuousAt_v (k + 1) h1.1) ((K.φ k).open_source.mem_nhds h0.2.1)
    have hc3 : ∀ᶠ u in 𝓝 u₀, (u, K.bb k u) ∈ ball (K.ctr k) (K.r k) :=
      (continuous_id.continuousAt.prodMk (K.continuousAt_bb k h1 h0))
        (isOpen_ball.mem_nhds h0.2.2)
    filter_upwards [hc1, hc2, hc3] with u h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have := (Finset.eventually_all (Finset.range K.N)).2 (fun k _ ↦ hk k)
  filter_upwards [this] with u hu
  exact (K.cond_iff u).2 hu

section Good

variable {u : Fin 10 → ℂ} (hu : ∀ k, K.cond u k)
include hu

theorem segment_mem (k : ℤ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (u, K.a k + (s : ℂ) * (K.bb k u - K.a k)) ∈ ball (K.ctr k) (K.r k) := by
  have h := Convex.add_smul_sub_mem (convex_ball (K.ctr k) (K.r k)) (hu k).1 (hu k).2.2 hs
  convert h using 1
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, Complex.real_smul]

theorem w_mem (k : ℤ) (τ : ℝ) : (u, K.w k u τ) ∈ ball (K.ctr k) (K.r k) :=
  K.segment_mem hu k ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem v_fib (k : ℤ) : (K.v k u).1.val = u := by
  have hmem := K.ball_sub k (hu k).1
  show ((K.φ k).symm (u, K.a k)).1.val = u
  rw [← K.fp k _ ((K.φ k).map_target hmem), (K.φ k).right_inv hmem]

theorem φ_v (k : ℤ) : K.φ k (K.v (k + 1) u) = (u, K.bb k u) := by
  refine Prod.ext ?_ rfl
  rw [K.fp k _ (hu k).2.1, K.v_fib hu]

theorem seg_fib (k : ℤ) (τ : ℝ) : (K.seg k u τ).1.val = u := by
  have hmem := K.ball_sub k (K.w_mem hu k τ)
  show ((K.φ k).symm (u, K.w k u τ)).1.val = u
  rw [← K.fp k _ ((K.φ k).map_target hmem), (K.φ k).right_inv hmem]

omit hu in
theorem w_zero (k : ℤ) {τ : ℝ} (hτ : τ ≤ 1 / 3) : K.w k u τ = K.a k := by
  have : b3A_step τ = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [w, this]

omit hu in
theorem w_one (k : ℤ) {τ : ℝ} (hτ : 2 / 3 ≤ τ) : K.w k u τ = K.bb k u := by
  have : b3A_step τ = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  simp [w, this]

omit hu in
theorem seg_zero (k : ℤ) {τ : ℝ} (hτ : τ ≤ 1 / 3) : K.seg k u τ = K.v k u := by
  rw [seg, K.w_zero k hτ, v]

theorem seg_one (k : ℤ) {τ : ℝ} (hτ : 2 / 3 ≤ τ) : K.seg k u τ = K.v (k + 1) u := by
  rw [seg, K.w_one k hτ, ← K.φ_v hu k]
  exact (K.φ k).left_inv (hu k).2.1

end Good

theorem continuous_w_param (k : ℤ) {u : Fin 10 → ℂ} (hu : ∀ k, K.cond u k) (τ : ℝ) :
    ContinuousAt (fun p : (Fin 10 → ℂ) × ℝ ↦ (p.1, K.w k p.1 p.2)) (u, τ) := by
  have hbb : ContinuousAt (fun p : (Fin 10 → ℂ) × ℝ ↦ K.bb k p.1) (u, τ) :=
    ContinuousAt.comp (g := K.bb k) (f := Prod.fst)
      (K.continuousAt_bb k (hu (k + 1)) (hu k)) continuous_fst.continuousAt
  have hst : Continuous fun p : (Fin 10 → ℂ) × ℝ ↦ ((b3A_step p.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (b3A_step_contDiff.continuous.comp continuous_snd)
  exact continuous_fst.continuousAt.prodMk
    (continuousAt_const.add (hst.continuousAt.mul (hbb.sub continuousAt_const)))

theorem continuousAt_seg (k : ℤ) {u : Fin 10 → ℂ} (hu : ∀ k, K.cond u k) (τ : ℝ) :
    ContinuousAt (fun p : (Fin 10 → ℂ) × ℝ ↦ K.seg k p.1 p.2) (u, τ) :=
  ContinuousAt.comp (g := (K.φ k).symm) (f := fun p : (Fin 10 → ℂ) × ℝ ↦ (p.1, K.w k p.1 p.2))
    ((K.φ k).continuousAt_symm (K.ball_sub k (K.w_mem hu k τ))) (K.continuous_w_param k hu τ)

theorem seg_match {u : Fin 10 → ℂ} (hu : ∀ k, K.cond u k) (k : ℤ) :
    K.seg k u 1 = K.seg (k + 1) u 0 := by
  rw [K.seg_one hu k (by norm_num), K.seg_zero (k + 1) (by norm_num)]

/-- The moving polygonal loop over `u`, with arcs indexed by the integers. -/
def floorLoop (u : Fin 10 → ℂ) (t : ℝ) : b6t_polydisc b × C := K.seg ⌊t⌋ u (Int.fract t)

theorem floorLoop_periodic (u : Fin 10 → ℂ) :
    Function.Periodic (fun t ↦ K.floorLoop u ((K.N : ℝ) * t)) 1 := by
  intro t
  simp only [floorLoop, mul_add, mul_one]
  rw [Int.floor_add_natCast, Int.fract_add_natCast, K.seg_add]

theorem continuous_param {u : Fin 10 → ℂ}
    (hS : ∀ l : unitInterval, ∀ k, K.cond (u₀ + (l : ℝ) • (u - u₀)) k) :
    Continuous (fun p : unitInterval × ℝ ↦
      K.floorLoop (u₀ + (p.1 : ℝ) • (u - u₀)) ((K.N : ℝ) * p.2)) := by
  have hG : ∀ k, ContinuousOn (fun p : unitInterval × ℝ ↦
      K.seg k (u₀ + (p.1 : ℝ) • (u - u₀)) p.2) (univ ×ˢ Icc 0 1) := by
    intro k
    refine Continuous.continuousOn (continuous_iff_continuousAt.2 fun p ↦ ?_)
    have hl : Continuous fun p : unitInterval × ℝ ↦ (u₀ + (p.1 : ℝ) • (u - u₀), p.2) :=
      (continuous_const.add ((continuous_subtype_val.comp continuous_fst).smul
        continuous_const)).prodMk continuous_snd
    exact ContinuousAt.comp (g := fun q : (Fin 10 → ℂ) × ℝ ↦ K.seg k q.1 q.2)
      (f := fun p : unitInterval × ℝ ↦ (u₀ + (p.1 : ℝ) • (u - u₀), p.2))
      (K.continuousAt_seg k (hS p.1) p.2) hl.continuousAt
  have h := b3Rest_continuous_floor (fun k (l : unitInterval) τ ↦
    K.seg k (u₀ + (l : ℝ) • (u - u₀)) τ) hG (fun k l ↦ K.seg_match (hS l) k)
  exact h.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))

/-- The straight-line homotopy, in the `k`-th chart, from the `k`-th arc of the loop to the `k`-th
segment over `u₀`. -/
def piece (k : ℤ) (l : unitInterval) (τ : ℝ) : b6t_polydisc b × C :=
  (K.φ k).symm ((1 - (l : ℝ)) • K.φ k (Γ ((k + τ) / K.N)) + (l : ℝ) • (u₀, K.w k u₀ τ))

theorem piece_zero (k : ℤ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    K.piece k 0 τ = Γ ((k + τ) / K.N) := by
  simp only [piece, Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
  exact (K.φ k).left_inv (K.mem k τ hτ).1

theorem piece_one (k : ℤ) (τ : ℝ) : K.piece k 1 τ = K.seg k u₀ τ := by
  simp only [piece, seg, Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]

theorem piece_match (k : ℤ) (l : unitInterval) : K.piece k l 1 = K.piece (k + 1) l 0 := by
  have hu := K.cond_u₀
  have h1 : K.piece k l 1 = Γ ((k + 1) / K.N) := by
    simp only [piece]
    rw [K.φ_Γ_one k, K.w_one k (by norm_num : (2 : ℝ) / 3 ≤ 1), ← add_smul, sub_add_cancel,
      one_smul, ← K.φ_Γ_one k]
    exact (K.φ k).left_inv (K.mem_one k).1
  have h2 : K.piece (k + 1) l 0 = Γ ((k + 1) / K.N) := by
    simp only [piece, add_zero]
    have hΓ := K.φ_Γ (k + 1)
    push_cast at hΓ ⊢
    rw [hΓ, K.w_zero (k + 1) (by norm_num : (0 : ℝ) ≤ 1 / 3), ← add_smul, sub_add_cancel,
      one_smul, ← hΓ]
    exact (K.φ (k + 1)).left_inv (by have := (K.mem_zero (k + 1)).1; push_cast at this; exact this)
  rw [h1, h2]

theorem piece_add (k : ℤ) : K.piece (k + K.N) = K.piece k := by
  funext l τ
  simp only [piece, K.φ_add, K.Γ_add, K.w_add]

theorem continuousOn_piece (k : ℤ) :
    ContinuousOn (fun p : unitInterval × ℝ ↦ K.piece k p.1 p.2) (univ ×ˢ Icc 0 1) := by
  have hu := K.cond_u₀
  have hP : ContinuousOn (fun p : unitInterval × ℝ ↦ K.φ k (Γ ((k + p.2) / K.N)))
      (univ ×ˢ Icc 0 1) := by
    refine (K.φ k).continuousOn.comp
      (K.cont.comp ((continuous_const.add continuous_snd).div_const _)).continuousOn ?_
    rintro ⟨l, τ⟩ ⟨-, hτ⟩
    exact (K.mem k τ hτ).1
  have hs : Continuous fun p : unitInterval × ℝ ↦ (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hw : Continuous fun p : unitInterval × ℝ ↦ ((u₀, K.w k u₀ p.2) : (Fin 10 → ℂ) × ℂ) := by
    refine continuous_const.prodMk (continuous_const.add ?_)
    exact (Complex.continuous_ofReal.comp (b3A_step_contDiff.continuous.comp continuous_snd)).mul
      continuous_const
  have hg : ContinuousOn (fun p : unitInterval × ℝ ↦
      (1 - (p.1 : ℝ)) • K.φ k (Γ ((k + p.2) / K.N)) + (p.1 : ℝ) • (u₀, K.w k u₀ p.2))
      (univ ×ˢ Icc 0 1) :=
    ((continuous_const.sub hs).continuousOn.smul hP).add (hs.smul hw).continuousOn
  refine (K.φ k).continuousOn_symm.comp hg ?_
  rintro ⟨l, τ⟩ ⟨-, hτ⟩
  apply K.ball_sub k
  exact convex_ball _ _ (K.mem k τ hτ).2 (K.w_mem hu k τ) (sub_nonneg.2 l.2.2) l.2.1 (by ring)

/-- The homotopy from the loop over `u₀` to the polygonal loop over `u₀`. -/
def hom (p : unitInterval × ℝ) : b6t_polydisc b × C :=
  K.piece ⌊(K.N : ℝ) * p.2⌋ p.1 (Int.fract ((K.N : ℝ) * p.2))

theorem continuous_hom : Continuous K.hom := by
  have h := b3Rest_continuous_floor K.piece K.continuousOn_piece K.piece_match
  exact h.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))

theorem hom_periodic (l : unitInterval) : Function.Periodic (fun t ↦ K.hom (l, t)) 1 := by
  intro t
  simp only [hom, mul_add, mul_one]
  rw [Int.floor_add_natCast, Int.fract_add_natCast, K.piece_add]

theorem hom_zero (t : ℝ) : K.hom (0, t) = Γ t := by
  have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
  simp only [hom]
  rw [K.piece_zero _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, Int.floor_add_fract]
  congr 1
  field_simp

theorem hom_one (t : ℝ) : K.hom (1, t) = K.floorLoop u₀ ((K.N : ℝ) * t) := by
  simp only [hom, floorLoop, piece_one]

end b63e_Cover

end HodgeLean.Foundations.Program
