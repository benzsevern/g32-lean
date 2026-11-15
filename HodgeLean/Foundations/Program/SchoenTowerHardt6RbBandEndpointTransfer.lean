import Mathlib.Tactic

/-! Endpoint incidence under collapsed-fiber band interpolation. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_band_endpoint_transfer (a b c d y v : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hy : a ≤ y ∧ y ≤ b) (hv : c ≤ v ∧ v ≤ d)
    (hz : a = b ↔ c = d)
    (he : (y - a) * (d - c) = (v - c) * (b - a)) :
    (y = a ↔ v = c) ∧ (y = b ↔ v = d) ∧
      (a < y ∧ y < b ↔ c < v ∧ v < d) := by
  by_cases hab0 : a = b
  · have hcd0 := hz.mp hab0
    have hy0 : y = a := by linarith
    have hv0 : v = c := by linarith
    simp [hab0, hcd0, hy0, hv0]
  · have hcd0 : c ≠ d := fun h => hab0 (hz.mpr h)
    have habpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab hab0)
    have hcdpos : 0 < d - c := sub_pos.mpr (lt_of_le_of_ne hcd hcd0)
    have hlow : y = a ↔ v = c := by
      constructor <;> intro h <;> nlinarith
    have hupp : y = b ↔ v = d := by
      constructor <;> intro h <;> nlinarith
    refine ⟨hlow, hupp, ?_⟩
    constructor
    · rintro ⟨hay, hyb⟩
      exact ⟨lt_of_le_of_ne hv.1 (fun h => (ne_of_gt hay) (hlow.mpr h.symm)),
        lt_of_le_of_ne hv.2 (fun h => (ne_of_lt hyb) (hupp.mpr h))⟩
    · rintro ⟨hcv, hvd⟩
      exact ⟨lt_of_le_of_ne hy.1 (fun h => (ne_of_gt hcv) (hlow.mp h.symm)),
        lt_of_le_of_ne hy.2 (fun h => (ne_of_lt hvd) (hupp.mp h))⟩

end HodgeLean.Foundations.Program
