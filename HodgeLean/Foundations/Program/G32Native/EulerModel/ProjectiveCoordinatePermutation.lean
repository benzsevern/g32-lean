import HodgeLean.Foundations.Program.SchoenCycleProjCoordinateMaps
import HodgeLean.Foundations.Program.SchoenCycleProjectiveBaseChange

/-! # Specified permutations of actual projective homogeneous coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual graded coordinate renaming determined by the specified index equivalence. -/
def projectiveCoordinateRename {ι κ : Type} (e : ι ≃ κ) :
    homogeneousSubmodule ι (ULift.{0} ℤ) →+*ᵍ homogeneousSubmodule κ (ULift.{0} ℤ) :=
  s2e_gradedCoordinateSection e.toEmbedding

/-- Inverse coordinate renaming retains every original homogeneous polynomial. -/
theorem projectiveCoordinateRename_symm {ι κ : Type} (e : ι ≃ κ)
    (p : MvPolynomial ι (ULift.{0} ℤ)) :
    projectiveCoordinateRename e.symm (projectiveCoordinateRename e p) = p := by
  change rename e.symm (rename e p) = p
  simp

#print axioms projectiveCoordinateRename
#print axioms projectiveCoordinateRename_symm
/-- The specified coordinate renaming satisfies the actual projective irrelevant-ideal condition. -/
theorem projectiveCoordinateRename_irrelevant {ι κ : Type} (e : ι ≃ κ) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule κ (ULift.{0} ℤ)) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι (ULift.{0} ℤ))).map
        (projectiveCoordinateRename e) := by
  apply s2e_irrelevant_le_map_of_graded_retraction _ _
    (projectiveCoordinateRename e) (projectiveCoordinateRename e.symm)
  intro p
  simpa only [Equiv.symm_symm] using projectiveCoordinateRename_symm e.symm p

#print axioms projectiveCoordinateRename_irrelevant
/-- The actual integral projective scheme isomorphism retaining the specified coordinate equivalence. -/
def integralProjectiveCoordinateIso {ι κ : Type} (e : ι ≃ κ) :
    Proj (homogeneousSubmodule ι (ULift.{0} ℤ)) ≅
      Proj (homogeneousSubmodule κ (ULift.{0} ℤ)) where
  hom := Proj.map (projectiveCoordinateRename e.symm) (projectiveCoordinateRename_irrelevant e.symm)
  inv := Proj.map (projectiveCoordinateRename e) (projectiveCoordinateRename_irrelevant e)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (projectiveCoordinateRename e.symm).comp (projectiveCoordinateRename e) =
        GradedRingHom.id _ := by
      apply DFunLike.ext
      intro p
      exact projectiveCoordinateRename_symm e p
    simpa only [h] using
      (Proj.map_id (𝒜 := homogeneousSubmodule ι (ULift.{0} ℤ)))
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h : (projectiveCoordinateRename e).comp (projectiveCoordinateRename e.symm) =
        GradedRingHom.id _ := by
      apply DFunLike.ext
      intro p
      change projectiveCoordinateRename e (projectiveCoordinateRename e.symm p) = p
      simpa only [Equiv.symm_symm] using projectiveCoordinateRename_symm e.symm p
    simpa only [h] using
      (Proj.map_id (𝒜 := homogeneousSubmodule κ (ULift.{0} ℤ)))

#print axioms integralProjectiveCoordinateIso
/-- The specified graded renaming pulls each actual homogeneous variable to its specified coordinate. -/
theorem projectiveCoordinateRename_X {ι κ : Type} (e : ι ≃ κ) (j : ι) :
    projectiveCoordinateRename e (X j) = (X (e j) : MvPolynomial κ (ULift.{0} ℤ)) := by
  change rename e (X j) = _
  exact rename_X e j

#print axioms projectiveCoordinateRename_X
end HodgeLean.Foundations.Program.G32Native.EulerModel
