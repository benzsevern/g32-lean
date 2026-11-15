import HodgeConjecture.Lemmas.LinearAlgebra.ComplexOrientation

/-! # Literal ordered real coordinates of the specified complex orientation
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified complex real-coordinate map retains the original consecutive basis coordinates at every finite complex coordinate.
Source: Complex.piCoordCLE; Module.Basis.smulTower'_repr; Module.Basis.repr_reindex_apply.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_real_coordinate_apply (d : ℕ) (z : Fin d → ℂ)
    (i : Fin d) (j : Fin 2) :
    Complex.piCoordCLE d z (finProdFinEquiv (i,j)) = Complex.basisOneI.repr (z i) j := by
  change (Complex.piBasisOneI d).repr z (finProdFinEquiv (i,j)) = _
  rw [Complex.piBasisOneI, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.smulTower'_repr]
  rfl

/-- Every specified complex coordinate has its literal real part followed by its literal imaginary part in the original ordered real coordinate map.
Source: properCycle_complex_real_coordinate_apply; Complex.coe_basisOneI_repr.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_real_coordinate_pair (d : ℕ) (z : Fin d → ℂ) (i : Fin d) :
    Complex.piCoordCLE d z (finProdFinEquiv (i,0)) = (z i).re ∧
      Complex.piCoordCLE d z (finProdFinEquiv (i,1)) = (z i).im := by
  constructor <;> rw [properCycle_complex_real_coordinate_apply] <;> rfl

/-- The specified inverse complex real-coordinate map reconstructs each complex coordinate from the original consecutive real and imaginary entries.
Source: properCycle_complex_real_coordinate_pair; Complex.piCoordCLE.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_real_coordinate_inverse (d : ℕ) (z : Fin (d*2) → ℝ)
    (i : Fin d) :
    (Complex.piCoordCLE d).symm z i =
      ⟨z (finProdFinEquiv (i,0)), z (finProdFinEquiv (i,1))⟩ := by
  apply Complex.ext
  · have h := (properCycle_complex_real_coordinate_pair d ((Complex.piCoordCLE d).symm z) i).1
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm
  · have h := (properCycle_complex_real_coordinate_pair d ((Complex.piCoordCLE d).symm z) i).2
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm

end HodgeLean.Foundations.QuotientDuality
