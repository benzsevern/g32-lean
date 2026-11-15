import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathMotion

/-! # Moving affine maps on the sphere -/
noncomputable section
open Set Topology Filter Metric
namespace HodgeLean.Foundations.Program

/-- A uniformly proper continuous plane family extends jointly to infinity.
Source: Mathlib `OnePoint.le_nhds_infty`; compact subsets of a normed space are bounded. -/
theorem rtc_uniform_proper_lift {T : Type*} [TopologicalSpace T]
    (f : T → ℂ → ℂ) (hf : Continuous fun q : T × ℂ ↦ f q.1 q.2)
    (hproper : ∀ R : ℝ, ∃ S : ℝ, ∀ t z, S ≤ ‖z‖ → R < ‖f t z‖) :
    Continuous fun q : T × OnePoint ℂ ↦ OnePoint.map (f q.1) q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, w⟩
  induction w using OnePoint.rec with
  | infty =>
    change Tendsto _ (𝓝 (t, OnePoint.infty)) (𝓝 OnePoint.infty)
    apply OnePoint.le_nhds_infty.mpr
    intro s hs hsc
    obtain ⟨R, hR⟩ := hsc.isBounded.exists_norm_le
    obtain ⟨S, hS⟩ := hproper R
    have hV : IsOpen (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall 0 S)ᶜ :=
      OnePoint.isOpen_compl_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall 0 S⟩
    have hmem : (OnePoint.infty : OnePoint ℂ) ∈
        (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall 0 S)ᶜ :=
      fun ⟨z, _, h⟩ ↦ OnePoint.coe_ne_infty z h
    change {q : T × OnePoint ℂ | OnePoint.map (f q.1) q.2 ∈ (↑) '' sᶜ ∪ {OnePoint.infty}} ∈ (𝓝 (t, (OnePoint.infty : OnePoint ℂ)))
    filter_upwards [(isOpen_univ.prod hV).mem_nhds ⟨mem_univ t, hmem⟩] with q hq
    induction h : q.2 using OnePoint.rec with
    | infty => simp
    | coe z =>
      have hz : S ≤ ‖z‖ := by
        by_contra hlt
        exact hq.2 ⟨z, by simpa using (not_le.mp hlt).le, h.symm⟩
      apply Or.inl
      refine ⟨f q.1 z, ?_, ?_⟩
      · intro hzs
        exact (not_lt_of_ge (hR _ hzs)) (hS q.1 z hz)
      · rfl
  | coe z =>
    have he : Topology.IsOpenEmbedding (Prod.map id ((↑) : ℂ → OnePoint ℂ) : T × ℂ → _) :=
      Topology.IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
    change ContinuousAt _ (Prod.map id ((↑) : ℂ → OnePoint ℂ) (t, z))
    rw [← he.continuousAt_iff]
    exact (OnePoint.continuous_coe.comp hf).continuousAt

/-- Nonvanishing continuous affine coefficients on a compact parameter space give a
jointly continuous sphere family.
Source: `rtc_uniform_proper_lift`; the estimate obtained by solving for the input. -/
theorem rtc_affine_family_continuous {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [Nonempty T] (A B : C(T, ℂ)) (hA : ∀ t, A t ≠ 0) :
    Continuous fun q : T × OnePoint ℂ ↦
      OnePoint.map (fun z ↦ A q.1 * z + B q.1) q.2 := by
  apply rtc_uniform_proper_lift (fun t z ↦ A t * z + B t)
  · exact ((A.continuous.comp continuous_fst).mul continuous_snd).add
      (B.continuous.comp continuous_fst)
  intro R
  have hc : Continuous (fun t ↦ (A t)⁻¹) := A.continuous.inv₀ hA
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn B.continuous.continuousOn
  refine ⟨(|C| + 1) * (|R| + |D| + 1), fun t z hz ↦ ?_⟩
  by_contra hlt
  have hle : ‖A t * z + B t‖ ≤ R := not_lt.mp hlt
  have hsolve : z = (A t)⁻¹ * ((A t * z + B t) - B t) := by
    rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (hA t), one_mul]
  have hnorm : ‖z‖ ≤ |C| * (R + |D|) := by
    calc
      ‖z‖ = ‖(A t)⁻¹‖ * ‖(A t * z + B t) - B t‖ := by rw [← norm_mul, ← hsolve]
      _ ≤ |C| * (‖A t * z + B t‖ + ‖B t‖) :=
        mul_le_mul ((hC t (mem_univ t)).trans (le_abs_self C)) (norm_sub_le _ _)
          (norm_nonneg _) (abs_nonneg C)
      _ ≤ |C| * (R + |D|) := mul_le_mul_of_nonneg_left
        (add_le_add hle ((hD t (mem_univ t)).trans (le_abs_self D))) (abs_nonneg C)
  have hpos : 0 ≤ R + |D| := by linarith [norm_nonneg (A t * z + B t), abs_nonneg D]
  have hR := le_abs_self R
  have hC0 := abs_nonneg C
  have hD0 := abs_nonneg D
  nlinarith

/-- The inverse affine sphere family is jointly continuous as well.
Source: `rtc_affine_family_continuous`, applied to inverse coefficients. -/
theorem rtc_affine_inverse_family_continuous {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [Nonempty T] (A B : C(T, ℂ)) (hA : ∀ t, A t ≠ 0) :
    Continuous fun q : T × OnePoint ℂ ↦
      OnePoint.map (fun z ↦ (z - B q.1) / A q.1) q.2 := by
  have hc : Continuous (fun t ↦ (A t)⁻¹) := A.continuous.inv₀ hA
  let C : C(T, ℂ) := ⟨fun t ↦ (A t)⁻¹, hc⟩
  let D : C(T, ℂ) := ⟨fun t ↦ -(A t)⁻¹ * B t, hc.neg.mul B.continuous⟩
  have heq : (fun q : T × OnePoint ℂ ↦ OnePoint.map (fun z ↦ (z - B q.1) / A q.1) q.2) =
      (fun q : T × OnePoint ℂ ↦ OnePoint.map (fun z ↦ C q.1 * z + D q.1) q.2) := by
    funext q
    congr 1
    funext z
    simp only [C, D, ContinuousMap.coe_mk, div_eq_mul_inv]
    ring
  rw [heq]
  exact rtc_affine_family_continuous C D (fun t ↦ inv_ne_zero (hA t))

end HodgeLean.Foundations.Program
