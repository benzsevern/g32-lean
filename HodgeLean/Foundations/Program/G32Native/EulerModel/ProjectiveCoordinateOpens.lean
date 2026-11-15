import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveCoordinateBaseChange
import HodgeLean.Foundations.Program.SchoenCycleS2bDefs

/-! # Specified coordinate permutations retain the actual projective basic opens -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified complex coordinate isomorphism retains its integral projective projection. -/
theorem complexProjectiveCoordinateIso_hom_snd {ι κ : Type} (e : ι ≃ κ) :
    (complexProjectiveCoordinateIso e).hom.left ≫
      pullback.snd (terminal.from (Spec ↧ℂ))
        (terminal.from (Proj (homogeneousSubmodule κ (ULift.{0} ℤ)))) =
    pullback.snd (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (homogeneousSubmodule ι (ULift.{0} ℤ)))) ≫
        (integralProjectiveCoordinateIso e).hom := by
  exact pullback.lift_snd _ _ _

#print axioms complexProjectiveCoordinateIso_hom_snd
/-- The specified coordinate permutation pulls back the literal native basic open to its original coordinate open. -/
theorem complexProjectiveCoordinateIso_basicOpen (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 1)) :
    (complexProjectiveCoordinateIso e).hom.left ⁻¹ᵁ
        projectiveSpaceBasicOpen k (X j) =
      projectiveSpaceBasicOpen k (X (e.symm j)) := by
  change ((complexProjectiveCoordinateIso e).hom.left ≫
    pullback.snd (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (UniversalGrading k)))) ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading k) (X j) = _
  rw [complexProjectiveCoordinateIso_hom_snd]
  change pullback.snd (terminal.from (Spec ↧ℂ))
    (terminal.from (Proj (UniversalGrading k))) ⁻¹ᵁ
      (Proj.map (projectiveCoordinateRename e.symm)
        (projectiveCoordinateRename_irrelevant e.symm) ⁻¹ᵁ
          Proj.basicOpen (UniversalGrading k) (X j)) = _
  rw [Proj.map_preimage_basicOpen, projectiveCoordinateRename_X]
  rfl

#print axioms complexProjectiveCoordinateIso_basicOpen
/-- The specified projective coordinate permutation retains the literal residue-hyperplane support. -/
theorem complexProjectiveCoordinateIso_hyperplane_support (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 1)) :
    (complexProjectiveCoordinateIso e).hom.left ⁻¹'
        (s2e_s2b_residueIdeal k j).support.carrier =
      (s2e_s2b_residueIdeal k (e.symm j)).support.carrier := by
  simp only [s2e_s2b_residueIdeal]
  exact congrArg (fun U : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Opens =>
    U.carrierᶜ) (complexProjectiveCoordinateIso_basicOpen k e j)

#print axioms complexProjectiveCoordinateIso_hyperplane_support
/-- The actual coordinate isomorphism maps the entire specified residue hyperplane onto its target hyperplane. -/
theorem complexProjectiveCoordinateIso_hyperplane_image (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 1)) :
    (complexProjectiveCoordinateIso e).hom.left ''
        (s2e_s2b_residueIdeal k (e.symm j)).support.carrier =
      (s2e_s2b_residueIdeal k j).support.carrier := by
  rw [← complexProjectiveCoordinateIso_hyperplane_support k e j]
  exact Set.image_preimage_eq _
    (Scheme.Hom.homeomorph (complexProjectiveCoordinateIso e).hom.left).surjective

#print axioms complexProjectiveCoordinateIso_hyperplane_image
end HodgeLean.Foundations.Program.G32Native.EulerModel
