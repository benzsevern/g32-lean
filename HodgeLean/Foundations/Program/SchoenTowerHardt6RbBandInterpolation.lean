import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Interpolation on bands whose boundary sections may meet. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_band_interpolation_mem {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * a + t * b ∈ Set.Icc a b := by
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]

theorem s2v_hardt6rb_band_interpolation_surjective {a b : ℝ} (hab : a ≤ b)
    {y : ℝ} (hy : y ∈ Set.Icc a b) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) * a + t * b = y := by
  by_cases heq : a = b
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    have hy' : y = a := le_antisymm (heq ▸ hy.2) hy.1
    simp only [sub_zero, one_mul, zero_mul, add_zero, hy']
  · have hpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
    refine ⟨(y - a) / (b - a), ⟨div_nonneg (sub_nonneg.mpr hy.1) hpos.le,
      (div_le_one hpos).mpr (sub_le_sub_right hy.2 a)⟩, ?_⟩
    field_simp
    <;> nlinarith

theorem s2v_hardt6rb_band_interpolation_eq_iff (a b t u : ℝ) :
    (1 - t) * a + t * b = (1 - u) * a + u * b ↔ t = u ∨ a = b := by
  constructor
  · intro h
    have hz : (t - u) * (b - a) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hz with ht | hab
    · exact Or.inl (sub_eq_zero.mp ht)
    · exact Or.inr (sub_eq_zero.mp hab).symm
  · rintro (rfl | rfl)
    · rfl
    · ring

theorem s2v_hardt6rb_band_interpolation_cross_iff {a b c d y v : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hzero : a = b ↔ c = d)
    (hy : y ∈ Set.Icc a b) (hv : v ∈ Set.Icc c d) :
    (y - a) * (d - c) = (v - c) * (b - a) ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1,
        (1 - t) * a + t * b = y ∧ (1 - t) * c + t * d = v := by
  constructor
  · intro hcross
    obtain ⟨t, ht, hty⟩ := s2v_hardt6rb_band_interpolation_surjective hab hy
    refine ⟨t, ht, hty, ?_⟩
    by_cases heq : a = b
    · have hcd' := hzero.mp heq
      have hv' : v = c := le_antisymm (hcd' ▸ hv.2) hv.1
      rw [← hcd', hv']
      ring
    · have hident :
          ((1 - t) * a + t * b - a) * (d - c) =
          ((1 - t) * c + t * d - c) * (b - a) := by ring
      rw [hty] at hident
      have hmul : ((1 - t) * c + t * d - v) * (b - a) = 0 := by
        nlinarith [hcross, hident]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right
        (fun h => heq (sub_eq_zero.mp h).symm))
  · rintro ⟨t, ht, hty, htv⟩
    rw [← hty, ← htv]
    ring

end HodgeLean.Foundations.Program
