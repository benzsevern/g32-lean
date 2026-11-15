import HodgeLean.Foundations.Program.SchoenSelectedGeometrySphereImage

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Projecting the algebraic tuple map recovers its prescribed sphere coordinate.
Source: the universal property of products and the sphere comparison. -/
theorem s0_sphere_power_coordinate_recovery {C : Type} (n : ℕ)
    (F : Fin n → C → OnePoint ℂ) (i : Fin n) (x : C) :
    let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
    s0_sphere_projective_homeomorph.symm
      (Point.map (g3_proj A n i) ((s0_power_point_homeomorph A n).symm
        (fun j ↦ s0_sphere_projective_homeomorph (F j x)))) = F i x := by
  let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  have hp := s0_power_point_homeomorph_projection A n
    ((s0_power_point_homeomorph A n).symm
      (fun j ↦ s0_sphere_projective_homeomorph (F j x))) i
  rw [Homeomorph.apply_symm_apply] at hp
  change s0_sphere_projective_homeomorph.symm _ = _
  rw [← hp, Homeomorph.symm_apply_apply]

#print axioms s0_sphere_power_coordinate_recovery
end HodgeLean.Foundations.Program
