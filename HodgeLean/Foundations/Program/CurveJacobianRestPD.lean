import HodgeLean.Foundations.Program.CurveJacobianRestJunction

/-! # Track B3, lane Rest: dual forms of chart polygons

For a chart polygon `K` there is a smooth `1`-form `η_K` with `∫_C ω ∧ η_K = ∫_K ω` for every
smooth closed `1`-form `ω` (`b3Rest_Poly.exists_dual`): the sum of the smeared segments of `K`
and of the junction corrections at its vertices, divided by the mass of the bump. On each segment
the pairing is the difference of the bump averages of a primitive at the two ends; the junction
corrections replace the average at the start of each segment by the average at the end of the
previous one, up to the difference of the two primitives at the vertex, and the averages
telescope around the polygon.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

theorem b3Rest_periodic_emod_add {α : Type*} {N : ℕ} {f : ℤ → α} (hf : ∀ k, f (k + N) = f k)
    (k m : ℤ) : f (k % N + m) = f (k + m) := by
  have hP : Function.Periodic f (N : ℤ) := hf
  have : k % (N : ℤ) + m = (k + m) - (k / (N : ℤ)) • (N : ℤ) := by
    rw [Int.emod_def, smul_eq_mul]
    ring
  rw [this, hP.sub_zsmul_eq]

theorem b3Rest_periodic_emod {α : Type*} {N : ℕ} {f : ℤ → α} (hf : ∀ k, f (k + N) = f k)
    (k : ℤ) : f (k % N) = f k := by
  simpa using b3Rest_periodic_emod_add hf k 0

/-- Shifting the index of a periodic sequence does not change its sum over a period. -/
theorem b3Rest_sum_shift {N : ℕ} (hN : 0 < N) {g : ℤ → ℝ} (hg : ∀ k, g (k + N) = g k) :
    ∑ i ∈ Finset.range N, g ((i : ℤ) - 1) = ∑ i ∈ Finset.range N, g i := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have h1 : g ((0 : ℕ) - 1 : ℤ) = g n := by
    have := hg (-1)
    push_cast at this ⊢
    rw [← this]
    ring_nf
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  ring_nf

theorem b3Rest_exists_pos_lt {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 < f i) :
    ∃ ε > 0, ∀ i ∈ S, ε < f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨ε, hε, hεS⟩ := ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a S)
    refine ⟨min ε (f a / 2), lt_min hε (half_pos hfa), fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (min_le_right _ _).trans_lt (half_lt_self hfa)
    · exact (min_le_left _ _).trans_lt (hεS i hi)

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest_wedgeForm_sum {ι : Type*} (S : Finset ι) (α : C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (β : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedgeForm α (∑ i ∈ S, β i) = ∑ i ∈ S, b3Forms_wedgeForm α (β i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    funext z
    simp only [b3Forms_wedgeForm, Finset.sum_empty, Pi.zero_apply]
    have := b3Forms_wedge_smul_right 0 (α z) 0
    rwa [zero_smul, zero_smul] at this
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    funext z
    simp only [b3Forms_wedgeForm, Pi.add_apply, b3Forms_wedge_add_right]

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest_wedgeForm_smul (c : ℝ) (α β : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedgeForm α (c • β) = c • b3Forms_wedgeForm α β := by
  funext z
  simp only [b3Forms_wedgeForm, Pi.smul_apply, b3Forms_wedge_smul_right]

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest_wedgeForm_add (α β β' : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedgeForm α (β + β') = b3Forms_wedgeForm α β + b3Forms_wedgeForm α β' := by
  funext z
  simp only [b3Forms_wedgeForm, Pi.add_apply, b3Forms_wedge_add_right]

namespace b3Rest_Poly

variable (K : b3Rest_Poly E C)

/-- The same polygon with the chart radii made periodic. -/
def perR : b3Rest_Poly E C where
  N := K.N
  pos := K.pos
  x := K.x
  r k := K.r (k % K.N)
  w := K.w
  x_add := K.x_add
  w_add := K.w_add
  ball_sub k := by
    have := K.ball_sub (k % K.N)
    rwa [b3Rest_periodic_emod K.x_add] at this
  mem_w k := by
    have := K.mem_w (k % K.N)
    rwa [b3Rest_periodic_emod K.x_add, b3Rest_periodic_emod K.w_add] at this
  mem_w' k := by
    have := K.mem_w' (k % K.N)
    rwa [b3Rest_periodic_emod K.x_add, b3Rest_periodic_emod_add K.w_add] at this

theorem perR_loop : K.perR.loop = K.loop := rfl

theorem perR_r_add (k : ℤ) : K.perR.r (k + K.perR.N) = K.perR.r k := by
  show K.r ((k + K.N) % K.N) = K.r (k % K.N)
  rw [Int.add_emod_right]

/-- **The integral along a polygon** is the sum of the differences of primitives along its
segments. -/
theorem lineIntegral_eq_sum {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (h : ℤ → E → ℝ) (hh : ∀ k, ∀ u ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k),
      HasFDerivAt (h k) (b3Forms_toCLM (b3Forms_loc α (K.x k) u)) u) :
    b3Forms_lineIntegral α K.loop 0 1 =
      ∑ i ∈ Finset.range K.N, (h i (K.B i) - h i (K.A i)) := by
  have hN : (0 : ℝ) < K.N := Nat.cast_pos.2 K.pos
  have hLi : ∀ k : ℤ, b3Forms_lineIntegral α K.loop ((k : ℝ) / K.N) ((k + 1) / K.N) =
      h k (K.B k) - h k (K.A k) := by
    intro k
    have hle : (k : ℝ) / K.N ≤ (k + 1) / K.N := by gcongr; linarith
    have e := b3Forms_lineIntegral_eq_of_primitive hα (hh k) K.loop_contMDiff
      (fun t ht ↦ K.loop_mem k (by rwa [uIcc_of_le hle] at ht))
    rw [e, K.loop_at k]
    have := K.loop_at (k + 1)
    push_cast at this
    rw [this]
    rfl
  have := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ ↦ (i : ℝ) / K.N)
    (n := K.N) (f := fun t ↦ α (K.loop t) (fun _ ↦ b3Forms_velocity K.loop t))
    (μ := MeasureTheory.volume)
    (fun i _ ↦ b3Forms_intervalIntegrable_lineIntegrand hα K.loop_contMDiff _ _)
  simp only [Nat.cast_zero, zero_div, div_self hN.ne', Nat.cast_add, Nat.cast_one] at this
  show (∫ t in (0 : ℝ)..1, α (K.loop t) (fun _ ↦ b3Forms_velocity K.loop t)) = _
  rw [← this]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := hLi i
  push_cast at this
  exact this

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

/-- The segment between two complex coordinates of points of a chart ball maps into the ball. -/
theorem segment_mem (hE : Module.finrank ℂ E = 1) (k : ℤ) {z : ℂ}
    (hz : z ∈ segment ℝ (b3Rest_pt hE (K.x k) (K.w k)) (b3Rest_pt hE (K.x k) (K.w (k + 1)))) :
    b3Rest_ζ hE (K.x k) z ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
  set a := b3Rest_pt hE (K.x k) (K.w k)
  set b := b3Rest_pt hE (K.x k) (K.w (k + 1))
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have he : b3Rest_ζ hE (K.x k) (a + t • (b - a)) =
      b3Rest_ζ hE (K.x k) a + t • (b3Rest_ζ hE (K.x k) b - b3Rest_ζ hE (K.x k) a) := by
    simp only [b3Rest_ζ, add_smul, sub_smul, smul_assoc]
    abel
  rw [he, b3Rest_ζ_pt, b3Rest_ζ_pt]
  exact Convex.add_smul_sub_mem (convex_ball _ _) (K.mem_w k).2 (K.mem_w' k).2 ht

set_option maxHeartbeats 400000 in
theorem exists_dual_aux (hE : Module.finrank ℂ E = 1) (hr : ∀ k, K.r (k + K.N) = K.r k) :
    ∃ η : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth η ∧
      ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α η) =
          b3Forms_lineIntegral α K.loop 0 1 := by
  have hw1 : ∀ k : ℤ, K.w k ∈ (chartAt E (K.x (k - 1))).source ∧
      chartAt E (K.x (k - 1)) (K.w k) ∈ ball (chartAt E (K.x (k - 1)) (K.x (k - 1))) (K.r (k - 1)) := by
    intro k
    have := K.mem_w' (k - 1)
    rwa [sub_add_cancel] at this
  choose ε₀ hε₀ hJ using fun k : ℤ ↦ b3Rest_junction hE (x := K.x (k - 1)) (y := K.x k)
    (w := K.w k) (hw1 k).1 (K.mem_w k).1 isOpen_ball isOpen_ball (K.ball_sub (k - 1))
    (K.ball_sub k) (hw1 k).2 (K.mem_w k).2
  have hS : ∀ k : ℤ, ∃ δ > 0, ∀ z ∈ cthickening δ (segment ℝ (b3Rest_pt hE (K.x k) (K.w k))
      (b3Rest_pt hE (K.x k) (K.w (k + 1)))),
      b3Rest_ζ hE (K.x k) z ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
    intro k
    have hc : IsCompact (segment ℝ (b3Rest_pt hE (K.x k) (K.w k))
        (b3Rest_pt hE (K.x k) (K.w (k + 1)))) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    obtain ⟨δ, hδ, hsub⟩ := hc.exists_cthickening_subset_open
      (isOpen_ball.preimage (b3Rest_continuous_ζ hE (K.x k))) fun z hz ↦ K.segment_mem hE k hz
    exact ⟨δ, hδ, fun z hz ↦ hsub hz⟩
  choose δs hδs hδseg using hS
  obtain ⟨ε, hε, hεlt⟩ := b3Rest_exists_pos_lt (Finset.range K.N)
    (fun i : ℕ ↦ min (ε₀ i) (δs i)) fun i _ ↦ lt_min (hε₀ i) (hδs i)
  have hεJ : ∀ i : Fin K.N, ε < ε₀ i := fun i ↦
    (hεlt i (Finset.mem_range.2 i.2)).trans_le (min_le_left _ _)
  have hεS : ∀ i : ℤ, i ∈ (Finset.range K.N).image (fun j : ℕ ↦ (j : ℤ)) →
      ∀ z ∈ cthickening ε (segment ℝ (b3Rest_pt hE (K.x i) (K.w i))
        (b3Rest_pt hE (K.x i) (K.w (i + 1)))),
        b3Rest_ζ hE (K.x i) z ∈ ball (chartAt E (K.x i) (K.x i)) (K.r i) := by
    intro i hi z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    exact hδseg j z (cthickening_mono ((hεlt j hj).le.trans (min_le_right _ _)) _ hz)
  choose κ hκs _ hκ using fun i : Fin K.N ↦ hJ i ε hε (hεJ i)
  set m := ∫ z, b3Rest_rho ε z
  have hm : 0 < m := b3Rest_integral_rho_pos hε
  set σ : Fin K.N → C → E [⋀^Fin 1]→L[ℝ] ℝ := fun i ↦
    b3Rest_segForm hE (K.x i) ε (b3Rest_pt hE (K.x i) (K.w i)) (b3Rest_pt hE (K.x i) (K.w (i + 1)))
  have hσ : ∀ i : Fin K.N, b3Forms_IsSmooth (σ i) := fun i ↦
    b3Rest_isSmooth_segForm hE (K.x i) hε fun z hz ↦ K.ball_sub i
      (hεS i (Finset.mem_image.2 ⟨i, Finset.mem_range.2 i.2, rfl⟩) z hz)
  set η := ∑ i : Fin K.N, (σ i + κ i)
  have hη : b3Forms_IsSmooth η :=
    (b3Forms_Ω E C 1).sum_mem fun i _ ↦ (hσ i).add (hκs i)
  refine ⟨m⁻¹ • η, hη.smul _, fun α hα hdα ↦ ?_⟩
  -- periodic primitives on the chart balls
  choose h' hh' using fun k : ℤ ↦ b3Forms_exists_local_primitive hα hdα (K.x k) (convex_ball _ _)
    isOpen_ball (K.ball_sub k)
  set h : ℤ → E → ℝ := fun k ↦ h' (k % K.N)
  have hh : ∀ k, ∀ u ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k),
      HasFDerivAt (h k) (b3Forms_toCLM (b3Forms_loc α (K.x k) u)) u := by
    intro k
    have := hh' (k % K.N)
    rwa [b3Rest_periodic_emod K.x_add, b3Rest_periodic_emod hr] at this
  have hhN : ∀ k, h (k + K.N) = h k := fun k ↦ by
    show h' ((k + K.N) % K.N) = h' (k % K.N)
    rw [Int.add_emod_right]
  -- the averages at the ends of the segments
  set T : ℤ → ℝ := fun j ↦
    ∫ z, b3Rest_rho ε z * h j (b3Rest_ζ hE (K.x j) (z + b3Rest_pt hE (K.x j) (K.w (j + 1))))
  have hTN : ∀ j, T (j + K.N) = T j := fun j ↦ by
    simp only [T, hhN, K.x_add, show j + K.N + 1 = (j + 1) + K.N by ring, K.w_add]
  set g : ℤ → ℝ := fun j ↦ h j (K.B j)
  have hgN : ∀ j, g (j + K.N) = g j := fun j ↦ by
    simp only [g, B, hhN, K.x_add, show j + K.N + 1 = (j + 1) + K.N by ring, K.w_add]
  have hpair : ∀ i : Fin K.N, b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α (σ i + κ i)) =
      (T i - T ((i : ℤ) - 1)) + m * (g ((i : ℤ) - 1) - h i (K.A i)) := by
    intro i
    rw [b3Rest_wedgeForm_add, b3Forms_integral_add _ (hα.wedgeForm (hσ i)) (hα.wedgeForm (hκs i)),
      b3Rest_integral_wedge_segForm hE hα (K.x i) isOpen_ball (K.ball_sub i) (hh i) hε
        (hεS i (Finset.mem_image.2 ⟨i, Finset.mem_range.2 i.2, rfl⟩)),
      hκ i α hα (h ((i : ℤ) - 1)) (h i) (hh ((i : ℤ) - 1)) (hh i)]
    have e1 : T ((i : ℤ) - 1) = ∫ z, b3Rest_rho ε z * h ((i : ℤ) - 1)
        (b3Rest_ζ hE (K.x ((i : ℤ) - 1)) (z + b3Rest_pt hE (K.x ((i : ℤ) - 1)) (K.w i))) := by
      simp only [T, sub_add_cancel]
    have e2 : g ((i : ℤ) - 1) = h ((i : ℤ) - 1) (chartAt E (K.x ((i : ℤ) - 1)) (K.w i)) := by
      simp only [g, B, sub_add_cancel]
    rw [e1, e2]
    simp only [T, A]
    ring
  rw [b3Rest_wedgeForm_smul, b3Forms_integral_smul, b3Rest_wedgeForm_sum,
    b3Forms_integral_finsetSum _ _ fun i _ ↦ hα.wedgeForm ((hσ i).add (hκs i))]
  simp only [hpair]
  rw [K.lineIntegral_eq_sum hα h hh, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hF : ∀ F : ℤ → ℝ, ∑ i : Fin K.N, F i = ∑ i ∈ Finset.range K.N, F i := fun F ↦
    Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ F i) K.N
  have hF' : ∀ F : ℤ → ℝ, ∑ i : Fin K.N, F ((i : ℤ) - 1) =
      ∑ i ∈ Finset.range K.N, F ((i : ℤ) - 1) := fun F ↦
    Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ F ((i : ℤ) - 1)) K.N
  rw [hF T, hF' T, hF' g, hF (fun j ↦ h j (K.A j)), b3Rest_sum_shift K.pos hTN,
    b3Rest_sum_shift K.pos hgN, sub_self, zero_add, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul,
    ← Finset.sum_sub_distrib]

/-- **The dual form of a chart polygon**: a smooth `1`-form `η` with `∫ ω ∧ η = ∫_K ω` for every
smooth closed `1`-form `ω`. -/
theorem exists_dual (hE : Module.finrank ℂ E = 1) :
    ∃ η : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth η ∧
      ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α η) =
          b3Forms_lineIntegral α K.loop 0 1 := by
  rw [← K.perR_loop]
  exact K.perR.exists_dual_aux hE K.perR_r_add

end b3Rest_Poly

end HodgeLean.Foundations.Program
