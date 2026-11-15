import HodgeLean.Foundations.Program.HolomorphicODEPicardContraction

noncomputable section
open Set Metric Filter Topology
namespace HodgeLean.Foundations.Program

theorem b65_picardIter_geometric {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × (ℂ × E) → E} {c : ℂ} {y : E} {r S M K : ℝ} {U : Set P}
    (hU : IsOpen U) (hr : 0 < r) (hS : 0 < S) (hM : 0 ≤ M) (hd : r * M < S / 4)
    (hK : 0 ≤ K) (hKL : r * (4 * M / S) ≤ K)
    (hA : AnalyticOnNhd ℂ A (U ×ˢ (ball c r ×ˢ ball y S)))
    (hb : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y S), ‖A q‖ ≤ M) :
    ∀ n q, q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)) →
      ‖b65_picardIter A c (n + 1) q - b65_picardIter A c n q‖ ≤ r * M * K ^ n := by
  have hi := b65_picardIter_bounds hU hr hS hM hd hA hb
  have hm (n : ℕ) (q : P × (ℂ × E)) (hq : q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2))) :
      b65_picardIter A c n q ∈ ball y (3 * S / 4) :=
    b65_displacement_inner_ball hd hq.2.2 ((hi n).2 q hq)
  intro n
  induction n with
  | zero =>
    intro q hq
    simpa [b65_picardIter] using (hi 1).2 q hq
  | succ n ih =>
    intro q hq
    have hh := b65_picardStep_dist_le hS hM (by positivity : 0 ≤ r * M * K ^ n)
      hA hb (hi (n + 1)).1 (hi n).1 (hm (n + 1)) (hm n) ih hq
    have hle := hh.trans (mul_le_mul_of_nonneg_right hKL (by positivity : 0 ≤ r * M * K ^ n))
    calc
      ‖b65_picardIter A c (n + 1 + 1) q - b65_picardIter A c (n + 1) q‖ ≤
          K * (r * M * K ^ n) := hle
      _ = r * M * K ^ (n + 1) := by rw [pow_succ]; ring

theorem b65_picard_fixed_point {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × (ℂ × E) → E} {c : ℂ} {y : E} {r S M K : ℝ} {U : Set P}
    (hU : IsOpen U) (hr : 0 < r) (hS : 0 < S) (hM : 0 ≤ M) (hd : r * M < S / 4)
    (hK₀ : 0 ≤ K) (hK : K < 1) (hKL : r * (4 * M / S) ≤ K)
    (hA : AnalyticOnNhd ℂ A (U ×ˢ (ball c r ×ˢ ball y S)))
    (hb : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y S), ‖A q‖ ≤ M) :
    ∃ F : P × (ℂ × E) → E,
      AnalyticOnNhd ℂ F (U ×ˢ (ball c r ×ˢ ball y (S / 2))) ∧
      ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)),
        ‖F q - q.2.2‖ ≤ r * M ∧ F q = b65_picardStep A c F q := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let D := U ×ˢ (ball c r ×ˢ ball y (S / 2))
  have hi := b65_picardIter_bounds hU hr hS hM hd hA hb
  have he := b65_picardIter_geometric hU hr hS hM hd hK₀ hKL hA hb
  obtain ⟨F, hlim⟩ := b65_geometric_uniform_limit hK₀ hK he
  have hF : AnalyticOnNhd ℂ F D :=
    b65_uniform_limit_analytic (hU.prod (isOpen_ball.prod isOpen_ball)) (fun n ↦ (hi n).1) hlim
  have hdisp (q : P × (ℂ × E)) (hq : q ∈ D) : ‖F q - q.2.2‖ ≤ r * M :=
    le_of_tendsto ((hlim.tendsto_at hq).sub_const q.2.2 |>.norm)
      (Eventually.of_forall fun n ↦ (hi n).2 q hq)
  have hFm (q : P × (ℂ × E)) (hq : q ∈ D) : F q ∈ ball y (3 * S / 4) :=
    b65_displacement_inner_ball hd hq.2.2 (hdisp q hq)
  have him (n : ℕ) (q : P × (ℂ × E)) (hq : q ∈ D) :
      b65_picardIter A c n q ∈ ball y (3 * S / 4) :=
    b65_displacement_inner_ball hd hq.2.2 ((hi n).2 q hq)
  have herr (n : ℕ) (q : P × (ℂ × E)) (hq : q ∈ D) :
      ‖b65_picardIter A c n q - F q‖ ≤ r * M * K ^ n / (1 - K) := by
    simpa [dist_eq_norm] using dist_le_of_le_geometric_of_tendsto K (r * M) hK
      (fun n ↦ by simpa [dist_eq_norm, norm_sub_rev] using he n q hq)
      (hlim.tendsto_at hq) n
  have hzero : Tendsto (fun n : ℕ ↦ (r * (4 * M / S)) * (r * M * K ^ n / (1 - K)))
      atTop (𝓝 0) := by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one hK₀ hK).const_mul (r * M)).div_const
      (1 - K)).const_mul (r * (4 * M / S))
  refine ⟨F, hF, fun q hq ↦ ⟨hdisp q hq, ?_⟩⟩
  have hstep : ∀ n, ‖b65_picardStep A c (b65_picardIter A c n) q - b65_picardStep A c F q‖ ≤
      (r * (4 * M / S)) * (r * M * K ^ n / (1 - K)) := by
    intro n
    exact b65_picardStep_dist_le hS hM (by positivity) hA hb (hi n).1 hF
      (him n) hFm (herr n) hq
  have ht : Tendsto (fun n ↦ b65_picardStep A c (b65_picardIter A c n) q)
      atTop (𝓝 (b65_picardStep A c F q)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n ↦ norm_nonneg _) hstep hzero)
  exact tendsto_nhds_unique ((hlim.tendsto_at hq).comp (tendsto_add_atTop_nat 1)) ht

theorem b65_local_parameter_solution {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × (ℂ × E) → E} {c : ℂ} {y : E} {r S M K : ℝ} {U : Set P}
    (hU : IsOpen U) (hr : 0 < r) (hS : 0 < S) (hM : 0 ≤ M) (hd : r * M < S / 4)
    (hK₀ : 0 ≤ K) (hK : K < 1) (hKL : r * (4 * M / S) ≤ K)
    (hA : AnalyticOnNhd ℂ A (U ×ˢ (ball c r ×ˢ ball y S)))
    (hb : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y S), ‖A q‖ ≤ M) :
    ∃ F : P × (ℂ × E) → E, AnalyticOnNhd ℂ F (U ×ˢ (ball c r ×ˢ ball y (S / 2))) ∧
      ∀ p ∈ U, ∀ v ∈ ball y (S / 2), F (p, (c, v)) = v ∧
        MapsTo (fun x ↦ F (p, (x, v))) (ball c r) (ball y S) ∧
        ∀ x ∈ ball c r, HasDerivAt (fun t ↦ F (p, (t, v))) (A (p, (x, F (p, (x, v))))) x := by
  obtain ⟨F, hF, hs⟩ := b65_picard_fixed_point hU hr hS hM hd hK₀ hK hKL hA hb
  have hmap : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)), F q ∈ ball y S := by
    intro q hq
    exact ball_subset_ball (by linarith : 3 * S / 4 ≤ S)
      (b65_displacement_inner_ball hd hq.2.2 (hs q hq).1)
  refine ⟨F, hF, fun p hp v hv ↦ ⟨?_, ?_, ?_⟩⟩
  · have hh := (hs (p, (c, v)) ⟨hp, mem_ball_self hr, hv⟩).2
    simpa [b65_picardStep, b65_segmentPrimitive] using hh
  · intro x hx
    exact hmap _ ⟨hp, hx, hv⟩
  · intro x hx
    apply (b65_picardStep_hasDerivAt hA hF hmap hp hv hx).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hx] with t ht
    exact (hs (p, (t, v)) ⟨hp, ht, hv⟩).2

end HodgeLean.Foundations.Program
