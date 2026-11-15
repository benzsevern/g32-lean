import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualMarked
import HodgeLean.Foundations.Program.G32Native.PairedResidualAnyHyperplane

/-! # Normalizing a retained residue coordinate

The equation over the slice records the projective coordinate change.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Exchange the retained residue coordinate and coordinate zero.
Source: Hartshorne, Algebraic Geometry, II.2, homogeneous coordinates. -/
def pairedC3CoordinateSwap (k : ℕ) (j : Fin (k + 1)) :
    (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun v := v ∘ Equiv.swap 0 j
  invFun v := v ∘ Equiv.swap 0 j
  left_inv v := by ext i; simp only [Function.comp_apply, Equiv.swap_apply_self]
  right_inv v := by ext i; simp only [Function.comp_apply, Equiv.swap_apply_self]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pullback of the standard hyperplane is the actual retained hyperplane.
Source: Hartshorne, Algebraic Geometry, II.2, homogeneous coordinates. -/
theorem pairedC3_coordinate_swap_hyperplane (k : ℕ) (j : Fin (k + 1)) :
    residualLinearHyperplane k (pairedC3CoordinateSwap k j) =
      s2e_s2b_residueIdeal k j := by
  rw [residual_linear_hyperplane_zero_scheme]
  have heq (v : Fin (k + 1) → ℂ) : (pairedC3CoordinateSwap k j v) 0 = v j := by
    change v (Equiv.swap 0 j 0) = v j
    rw [Equiv.swap_apply_left]
  simp only [heq]
  unfold s2e_s2b_residueIdeal
  congr 1
  apply TopologicalSpace.Closeds.ext
  exact s2e_coordinate_hyperplane_closure k j

/-- The inverse coordinate exchange supplies the exact ideal equation used
by the normalized numerical consumer.
Source: Hartshorne, Algebraic Geometry, II.2, homogeneous coordinates. -/
theorem pairedC3_coordinate_swap_inverse_hyperplane (k : ℕ) (j : Fin (k + 1)) :
    (s2e_s2b_residueIdeal k j).comap
        (s2e_linearProjectiveOverIso (pairedC3CoordinateSwap k j)).inv.left =
      s2e_hyperplaneIdeal k := by
  let e := s2e_linearProjectiveOverIso (pairedC3CoordinateSwap k j)
  have h : e.inv.left ≫ e.hom.left = 𝟙 _ :=
    congrArg Over.Hom.left e.inv_hom_id
  rw [← pairedC3_coordinate_swap_hyperplane k j]
  change ((s2e_hyperplaneIdeal k).comap e.hom.left).comap e.inv.left = _
  rw [← Scheme.IdealSheafData.comap_comp, h, Scheme.IdealSheafData.comap_id]

#print axioms pairedC3_coordinate_swap_inverse_hyperplane

#print axioms pairedC3CoordinateSwap
#print axioms pairedC3_coordinate_swap_hyperplane
end HodgeLean.Foundations.Program.G32Native
