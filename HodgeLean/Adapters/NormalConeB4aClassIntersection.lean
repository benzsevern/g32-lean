import HodgeLean.Adapters.NormalConeB4aClassBoundary

/-! # Codimension of intersections of distinct component supports

Route: a point specializing from two distinct generic points specializes
strictly from at least one of them. Coheight increases along that step.
-/

noncomputable section
namespace HodgeLean.Adapters
open AlgebraicGeometry

/-- Intersections of distinct component supports raise any common lower
codimension bound, including components of different dimensions. -/
theorem a3b4a_classComponent_intersection_coheight
    (Z : Scheme.{0}) (c : ℕ) (x y z : Z) (hxy : x ≠ y)
    (hx : (c : ℕ∞) ≤ Order.coheight x) (hy : (c : ℕ∞) ≤ Order.coheight y)
    (hzx : z ∈ closure ({x} : Set Z)) (hzy : z ∈ closure ({y} : Set Z)) :
    ((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
  have hzx' : z ≤ x := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hzx)
  have hzy' : z ≤ y := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hzy)
  have hlt : z < x ∨ z < y := by
    by_cases he : z = x
    · right
      refine lt_iff_le_not_ge.mpr ⟨hzy', fun hyz => ?_⟩
      have hzyEq : z = y := ((Scheme.le_iff_specializes.mp hyz).antisymm
        (Scheme.le_iff_specializes.mp hzy')).eq
      exact hxy (he.symm.trans hzyEq)
    · left
      exact lt_iff_le_not_ge.mpr ⟨hzx', fun hxz => he
        (((Scheme.le_iff_specializes.mp hxz).antisymm (Scheme.le_iff_specializes.mp hzx')).eq)⟩
  have hbase : (c : ℕ∞) + 1 ≤ Order.coheight z := by
    rcases hlt with hlt | hlt
    · exact (show (c : ℕ∞) + 1 ≤ Order.coheight x + 1 by
        simpa only [add_comm] using add_le_add_right hx 1).trans
        (Order.coheight_add_one_le hlt)
    · exact (show (c : ℕ∞) + 1 ≤ Order.coheight y + 1 by
        simpa only [add_comm] using add_le_add_right hy 1).trans
        (Order.coheight_add_one_le hlt)
  simpa only [Nat.cast_add, Nat.cast_one] using hbase

end HodgeLean.Adapters
