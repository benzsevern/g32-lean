import Mathlib.Order.Fin.Basic
import Mathlib.Basic.Real.Basic

/-! A height belongs to at most one ordered root graph or adjacent-root open interval. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ordered_cell_labels {r : ℕ}
    (f : Fin r → ℝ) (hf : StrictMono f) (t : ℝ)
    (a b : Fin r ⊕ {p : Fin r × Fin r // p.1.val + 1 = p.2.val})
    (ha : match a with
      | .inl i => t = f i
      | .inr p => f p.val.1 < t ∧ t < f p.val.2)
    (hb : match b with
      | .inl i => t = f i
      | .inr p => f p.val.1 < t ∧ t < f p.val.2) : a = b := by
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (hf.injective (ha.symm.trans hb))
    | inr p =>
      have hlo : p.val.1 < i := hf.lt_iff_lt.mp (ha ▸ hb.1)
      have hhi : i < p.val.2 := hf.lt_iff_lt.mp (ha ▸ hb.2)
      have hp := p.property
      have hlo' : p.val.1.val < i.val := hlo
      have hhi' : i.val < p.val.2.val := hhi
      omega
  | inr p =>
    cases b with
    | inl j =>
      have hlo : p.val.1 < j := hf.lt_iff_lt.mp (hb ▸ ha.1)
      have hhi : j < p.val.2 := hf.lt_iff_lt.mp (hb ▸ ha.2)
      have hp := p.property
      have hlo' : p.val.1.val < j.val := hlo
      have hhi' : j.val < p.val.2.val := hhi
      omega
    | inr q =>
      have hleft : p.val.1 = q.val.1 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have hle : p.val.2 ≤ q.val.1 := by
            have hp := p.property
            change p.val.2.val ≤ q.val.1.val
            have hlt' : p.val.1.val < q.val.1.val := hlt
            omega
          exact (lt_of_lt_of_le ha.2 (hf.monotone hle)).asymm hb.1
        · have hle : q.val.2 ≤ p.val.1 := by
            have hq := q.property
            change q.val.2.val ≤ p.val.1.val
            have hlt' : q.val.1.val < p.val.1.val := hlt
            omega
          exact (lt_of_lt_of_le hb.2 (hf.monotone hle)).asymm ha.1
      have hright : p.val.2 = q.val.2 := by
        apply Fin.ext
        have hp := p.property
        have hq := q.property
        have he := congrArg Fin.val hleft
        omega
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hleft hright))

end HodgeLean.Foundations.Program
