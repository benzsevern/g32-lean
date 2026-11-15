import HodgeLean.Foundations.Program.G32Native.TypeIIIFormDiagonalization
import HodgeLean.Foundations.Program.G32Native.TypeIIIActualDiscriminant

noncomputable section
set_option maxHeartbeats 400000
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- Changing homology coordinates does not change the discriminant class when
it retains the quaternion generator on the same polarized variety. -/
theorem TypeIIISixfoldData.discriminant_class_eq (Q R : TypeIIISixfoldData A pol)
    (hJ : Q.inducedWeilAction.J = R.inducedWeilAction.J) :
    (Q.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
      (R.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  rw [← Q.discriminant_class, ← R.discriminant_class]
  have hW : Q.inducedWeilAction = R.inducedWeilAction := by
    have he : ∀ (W W' : HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3), W.J = W'.J → W = W' := by
      intro W W' h
      cases W
      cases W'
      dsimp only at h
      cases h
      rfl
    exact he _ _ hJ
  simp only [hW]

/-- The class of −b disc(T), defined from the trace polarization and the
specified quaternion generator, without orthogonal coordinates in its value.
The diagonalization supplies only the square and skewness certificates. -/
def TypeIIIFormData.discriminantClass (F : TypeIIIFormData A pol) :
    ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  weilDetClass (polarizationForm (torusCohomology_cupProductOf A) F.nondegenerate)
    ⟨(abelianEnd0Action A (F.endomorphisms
      (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, F.b]))).unop, F.diagonal.generator_sq⟩
    ((isRosatiSkew_iff_dualForm F.nondegenerate _).1 F.diagonal.generator_rosati)
    (isAlt_polarizationForm _ _) (nondegenerate_polarizationForm _ _)

/-- The selected diagonal product represents the intrinsic class of the form. -/
theorem TypeIIIFormData.discriminantClass_eq (F : TypeIIIFormData A pol) :
    F.discriminantClass =
      (F.diagonal.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  exact F.diagonal.discriminant_class

/-- Any diagonal presentation of the same trace polarization and generator
has the same class; its orthogonal basis and three entries may vary. -/
theorem TypeIIIFormData.discriminantClass_eq_presentation (F : TypeIIIFormData A pol)
    (Q : TypeIIISixfoldData A pol)
    (hJ : Q.inducedWeilAction.J = (abelianEnd0Action A (F.endomorphisms
      (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, F.b]))).unop) :
    F.discriminantClass =
      (Q.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  rw [F.discriminantClass_eq]
  exact (Q.discriminant_class_eq F.diagonal hJ).symm

end HodgeLean.Foundations.Program.G32Native
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.discriminant_class_eq
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIIFormData.discriminantClass_eq
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIIFormData.discriminantClass_eq_presentation
