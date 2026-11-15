import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexBlockCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedNormalCoordinateComparison

/-! # Actual mixed real and complex coordinates in the ordered product model
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual recursive real normal coordinates, grouped into consecutive complex tangential coordinates, equal the literal ordered complex block coordinates of the specified complex real inverse.
Source: properCycle_iterated_normal_coordinates_prefix; properCycle_iterated_normal_coordinates_tail; properCycle_complex_real_coordinate_inverse.
HC no distance; AV milestone no distance. -/
theorem properCycle_mixed_complex_real_coordinates (r d : ℕ)
    (z : Fin ((r+d)*2) → ℝ) :
    let z' : Fin (d*2+r*2) → ℝ := fun k => z ⟨k.val, by omega⟩
    let w := properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) (r*2)
      (properCycle_iterated_real_local_coordinates d (r*2) z')
    properCycle_complex_block_coordinates r d ((Complex.piCoordCLE (r+d)).symm z) =
      ((Complex.piCoordCLE r).symm w.1, w.2) := by
  let z' : Fin (d*2+r*2) → ℝ := fun k => z ⟨k.val, by omega⟩
  let w := properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) (r*2)
    (properCycle_iterated_real_local_coordinates d (r*2) z')
  apply Prod.ext
  · funext i
    change (Complex.piCoordCLE (r+d)).symm z (Fin.castAdd d i) = (Complex.piCoordCLE r).symm w.1 i
    simp only [properCycle_complex_real_coordinate_inverse]
    apply Complex.ext
    · change z (finProdFinEquiv (Fin.castAdd d i,0)) = w.1 (finProdFinEquiv (i,0))
      dsimp only [w]
      rw [properCycle_iterated_normal_coordinates_prefix]
      rfl
    · change z (finProdFinEquiv (Fin.castAdd d i,1)) = w.1 (finProdFinEquiv (i,1))
      dsimp only [w]
      rw [properCycle_iterated_normal_coordinates_prefix]
      rfl
  · funext j
    change (Complex.piCoordCLE (r+d)).symm z (Fin.natAdd r j) = w.2 j
    dsimp only [w]
    rw [properCycle_iterated_normal_coordinates_tail]
    simp only [properCycle_complex_real_coordinate_inverse]
    apply Complex.ext
    · dsimp only [z']
      congr 1
      apply Fin.ext
      change 0+2*(r+j.val) = r*2+(0+2*j.val)
      omega
    · dsimp only [z']
      congr 1
      apply Fin.ext
      change 1+2*(r+j.val) = r*2+(1+2*j.val)
      omega

end HodgeLean.Foundations.QuotientDuality
