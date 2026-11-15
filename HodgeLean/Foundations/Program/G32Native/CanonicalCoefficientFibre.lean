import HodgeLean.Foundations.Program.G32Native.CanonicalNormalCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

/-! # Coefficient kernels on the retained projective component

The homogeneous line is taken over the image of the specified eQ.
This is the line selection used by the retained I1 homogeneous model.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The homogeneous line over the specified component point. -/
def g32n_homogeneousLine {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (x : ComplexPoint Q) : Projectivization ℂ (Fin (k + 1) → ℂ) :=
  Classical.choose (ComplexProjectiveSpace.surjective_projectivizationToComplexPoint
    (n := k) (Point.map eQ.hom x))

/-- The homogeneous line lies over the original projective identification. -/
theorem g32n_homogeneousLine_point {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (x : ComplexPoint Q) :
    ComplexProjectiveSpace.projectivizationToComplexPoint (g32n_homogeneousLine k eQ x) =
      Point.map eQ.hom x :=
  Classical.choose_spec (ComplexProjectiveSpace.surjective_projectivizationToComplexPoint
    (n := k) (Point.map eQ.hom x))

/-- Coefficient evaluation on the retained representative has the I1 homogeneous kernel. -/
theorem g32n_selected_coefficient_kernel {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (x : ComplexPoint Q) :
    LinearMap.ker (g32n_coefficientEvaluation k (g32n_homogeneousLine k eQ x).rep) =
      (g32n_homogeneousLine k eQ x).submodule.dualAnnihilator := by
  rw [g32n_coefficient_kernel, Projectivization.submodule_eq]

/-- The coefficient fibre over each retained point has the native rank. -/
theorem g32n_selected_coefficient_rank {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (x : ComplexPoint Q) :
    Module.finrank ℂ (g32n_homogeneousLine k eQ x).submodule.dualAnnihilator = k := by
  rw [← g32n_selected_coefficient_kernel]
  exact g32n_coefficient_kernel_rank k _ (g32n_homogeneousLine k eQ x).rep_nonzero

#print axioms g32n_homogeneousLine
#print axioms g32n_homogeneousLine_point
#print axioms g32n_selected_coefficient_kernel
#print axioms g32n_selected_coefficient_rank
end HodgeLean.Foundations.Program
