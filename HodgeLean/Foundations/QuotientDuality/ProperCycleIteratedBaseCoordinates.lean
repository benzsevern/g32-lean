import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedBaseTransport
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportCoordinates

/-! # Actual finite coordinates under literal iterated base transport
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual iterated base map leaves every finite real tangential coordinate fixed and applies the original map to the literal base coordinate.
Source: properCycle_iterated_real_base_map; properCycle_real_support_coordinates.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_real_base_coordinates {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (z : properCycle_real_support_space X n) :
    properCycle_real_support_coordinates Y n (properCycle_iterated_real_base_map f n z) =
      ((properCycle_real_support_coordinates X n z).1, f (properCycle_real_support_coordinates X n z).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Fin.cons (α := fun _ : Fin (n+1) => ℝ) z.1
      (properCycle_real_support_coordinates Y n (properCycle_iterated_real_base_map f n z.2)).1,
      (properCycle_real_support_coordinates Y n (properCycle_iterated_real_base_map f n z.2)).2) =
      (Fin.cons (α := fun _ : Fin (n+1) => ℝ) z.1 (properCycle_real_support_coordinates X n z.2).1,
        f (properCycle_real_support_coordinates X n z.2).2)
    rw [ih z.2]

end HodgeLean.Foundations.QuotientDuality
