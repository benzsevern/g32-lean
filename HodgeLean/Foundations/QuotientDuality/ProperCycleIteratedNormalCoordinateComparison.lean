import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedRealLocalCoordinates

/-! # Actual finite coordinates of the specified iterated normal local class
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual recursive local coordinates retain the literal initial real coordinates as their finite tangential prefix.
Source: properCycle_iterated_real_local_coordinates; properCycle_real_support_coordinates.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_normal_coordinates_prefix (d n : ℕ)
    (z : Fin (d*2+n) → ℝ) (i : Fin n) :
    (properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) n
      (properCycle_iterated_real_local_coordinates d n z)).1 i = z ⟨i.val, by omega⟩ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) n
        (properCycle_iterated_real_local_coordinates d n (fun k => z k.succ))).1 j =
        z ⟨j.val+1, by omega⟩
      rw [ih (fun k => z k.succ) j]
      rfl

/-- The actual recursive local coordinates retain the original complex normal inverse coordinates on the literal real tail after every tangential factor.
Source: properCycle_iterated_real_local_coordinates; properCycle_real_support_coordinates; Complex.piCoordCLE.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_normal_coordinates_tail (d n : ℕ)
    (z : Fin (d*2+n) → ℝ) :
    (properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) n
      (properCycle_iterated_real_local_coordinates d n z)).2 =
      (Complex.piCoordCLE d).symm (fun j : Fin (d*2) => z ⟨n+j.val, by omega⟩) := by
  induction n with
  | zero =>
    change (Complex.piCoordCLE d).symm z =
      (Complex.piCoordCLE d).symm (fun j : Fin (d*2) => z ⟨0+j.val, by omega⟩)
    apply congrArg (Complex.piCoordCLE d).symm
    funext j
    congr 1
    apply Fin.ext
    change j.val = 0+j.val
    omega
  | succ n ih =>
    change (properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) n
      (properCycle_iterated_real_local_coordinates d n (fun k => z k.succ))).2 = _
    rw [ih (fun k => z k.succ)]
    apply congrArg (Complex.piCoordCLE d).symm
    funext j
    congr 1
    apply Fin.ext
    change n+j.val+1 = n+1+j.val
    omega

end HodgeLean.Foundations.QuotientDuality
