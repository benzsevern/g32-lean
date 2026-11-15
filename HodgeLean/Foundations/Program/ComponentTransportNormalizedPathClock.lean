import HodgeLean.Foundations.Program.ComponentTransportNormalized

/-! # Short initial intervals for concatenated configuration paths -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- Piecewise affine clock sending a chosen junction to one half.
Source: linear reparametrization of the two intervals. -/
def rtc_escape_clock (a : ℝ) : unitInterval → unitInterval := fun t ↦
  Set.projIcc 0 1 zero_le_one
    (if (t : ℝ) ≤ a then (t : ℝ) / (2 * a)
      else 1 / 2 + ((t : ℝ) - a) / (2 * (1 - a)))

theorem rtc_escape_clock_continuous (a : ℝ) (ha : 0 < a) (_ha' : a < 1) :
    Continuous (rtc_escape_clock a) := by
  apply continuous_projIcc.comp
  apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_subtype_val continuous_const
  intro t ht
  simp only [ht, sub_self, zero_div, add_zero]
  field_simp

@[simp] theorem rtc_escape_clock_zero (a : ℝ) (ha : 0 < a) : rtc_escape_clock a 0 = 0 := by
  simp [rtc_escape_clock, ha.le]

@[simp] theorem rtc_escape_clock_one (a : ℝ) (ha : a < 1) : rtc_escape_clock a 1 = 1 := by
  have hne : 1 - a ≠ 0 := by linarith
  have hh : (1 / 2 : ℝ) + (1 - a) / (2 * (1 - a)) = 1 := by field_simp <;> ring
  change Set.projIcc 0 1 zero_le_one
    (if (1 : ℝ) ≤ a then 1 / (2 * a) else 1 / 2 + (1 - a) / (2 * (1 - a))) = 1
  rw [ite_eq_right (not_le.mpr ha), hh]
  simp

/-- The first interval of the clock follows the first path at constant speed.
Source: Mathlib `Path.trans_apply`; the formula for `rtc_escape_clock`. -/
theorem rtc_escape_clock_first {X : Type*} [TopologicalSpace X]
    {x y z : X} (E : Path x y) (σ : Path y z)
    (a : ℝ) (ha : 0 < a) (ha' : a < 1) (t : unitInterval) (ht : (t : ℝ) ≤ a) :
    (E.trans σ) (rtc_escape_clock a t) =
      E (Set.projIcc 0 1 zero_le_one ((t : ℝ) / a)) := by
  have hhalf : (t : ℝ) / (2 * a) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hmem : (t : ℝ) / (2 * a) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg t.2.1 (by positivity), hhalf.trans (by norm_num)⟩
  have hc : (rtc_escape_clock a t : ℝ) = (t : ℝ) / (2 * a) := by
    simp only [rtc_escape_clock, ite_eq_left ht, Set.projIcc_of_mem _ hmem]
  rw [Path.trans_apply, dite_eq_left (by rw [hc]; exact hhalf)]
  apply congrArg E
  apply Subtype.ext
  have hmem' : (t : ℝ) / a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg t.2.1 ha.le, (div_le_one ha).mpr ht⟩
  change 2 * (rtc_escape_clock a t : ℝ) = (Set.projIcc 0 1 zero_le_one ((t : ℝ) / a) : ℝ)
  rw [Set.projIcc_of_mem _ hmem', hc]
  field_simp

/-- The second interval of the clock follows the suffix at constant speed.
Source: Mathlib `Path.trans_apply`; the formula for `rtc_escape_clock`. -/
theorem rtc_escape_clock_last {X : Type*} [TopologicalSpace X]
    {x y z : X} (E : Path x y) (σ : Path y z)
    (a : ℝ) (ha : 0 < a) (ha' : a < 1) (t : unitInterval) (ht : a ≤ (t : ℝ)) :
    (E.trans σ) (rtc_escape_clock a t) =
      σ (Set.projIcc 0 1 zero_le_one (((t : ℝ) - a) / (1 - a))) := by
  by_cases he : (t : ℝ) = a
  · rw [rtc_escape_clock_first E σ a ha ha' t he.le]
    simp [he, ha.ne']
  have hlt : a < (t : ℝ) := lt_of_le_of_ne ht (Ne.symm he)
  have hden : 0 < 1 - a := sub_pos.mpr ha'
  have hparam : ((t : ℝ) - a) / (1 - a) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr ht) hden.le,
      (div_le_one hden).mpr (by linarith [t.2.2])⟩
  have hhalf : 1 / 2 < (1 / 2 : ℝ) + ((t : ℝ) - a) / (2 * (1 - a)) := by
    have : 0 < ((t : ℝ) - a) / (2 * (1 - a)) := by positivity
    linarith
  have hmem : (1 / 2 : ℝ) + ((t : ℝ) - a) / (2 * (1 - a)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · have hh := hparam.2
      have heq : 2 * (1 / 2 + ((t : ℝ) - a) / (2 * (1 - a))) =
          1 + ((t : ℝ) - a) / (1 - a) := by field_simp
      linarith
  have hc : (rtc_escape_clock a t : ℝ) =
      1 / 2 + ((t : ℝ) - a) / (2 * (1 - a)) := by
    simp only [rtc_escape_clock, ite_eq_right (not_le.mpr hlt), Set.projIcc_of_mem _ hmem]
  rw [Path.trans_apply, dite_eq_right (by rw [hc]; exact not_le.mpr hhalf)]
  apply congrArg σ
  apply Subtype.ext
  change 2 * (rtc_escape_clock a t : ℝ) - 1 =
    (Set.projIcc 0 1 zero_le_one (((t : ℝ) - a) / (1 - a)) : ℝ)
  rw [Set.projIcc_of_mem _ hparam, hc]
  field_simp
  <;> ring

/-- A sufficiently short escape interval makes the rescaled suffix uniformly small on cells.
Source: uniform continuity on the compact unit interval; affine rescaling. -/
theorem rtc_suffix_modulus {X : Type*} [PseudoMetricSpace X]
    (f : C(unitInterval, X)) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      ∀ s t : unitInterval, a ≤ (s : ℝ) → a ≤ (t : ℝ) → |(s : ℝ) - t| < a →
        dist (f (Set.projIcc 0 1 zero_le_one (((s : ℝ) - a) / (1 - a))))
          (f (Set.projIcc 0 1 zero_le_one (((t : ℝ) - a) / (1 - a)))) < ε := by
  obtain ⟨δ, hδ, hf⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  let a : ℝ := min (1 / 4) (δ / 4)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha4 : a ≤ 1 / 4 := min_le_left _ _
  have haδ : a ≤ δ / 4 := min_le_right _ _
  have ha1 : a < 1 := by linarith
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  refine ⟨a, ha, by linarith, fun s t hs ht hst ↦ hf ?_⟩
  have hmem (v : unitInterval) (hv : a ≤ (v : ℝ)) :
      ((v : ℝ) - a) / (1 - a) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hv) hden.le,
      (div_le_one hden).mpr (by linarith [v.2.2])⟩
  rw [Set.projIcc_of_mem _ (hmem s hs), Set.projIcc_of_mem _ (hmem t ht), Subtype.dist_eq]
  change |((s : ℝ) - a) / (1 - a) - ((t : ℝ) - a) / (1 - a)| < δ
  rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hden]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

end HodgeLean.Foundations.Program
