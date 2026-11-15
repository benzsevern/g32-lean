import HodgeLean.Foundations.Program.G32Native.PELSplitFamilyData

noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
namespace PELSplitFamily
variable {R : PELSplitReference} (F : PELSplitFamily R) (z : PELSplitComponent R)

/-- Every quaternion matrix is retained by the common rational marking.
Source: Birkenhake–Lange, §§1.2, 9.6. -/
theorem action_matrix (d : ℍ[ℚ, -3, 0, R.b]) :
    LinearMap.toMatrix (F.basis z) (F.basis z)
      (abelianEnd0Action (F.fibre z).X (F.action z d)).unop = R.operator d := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (F.basis z).repr
    ((abelianEnd0Action (F.fibre z).X (F.action z d)).unop (F.mark z (R.basis j))) i = _
  rw [F.action_eq, PELSplitReference.operator, LinearMap.toMatrix_apply]
  change R.basis.repr ((F.mark z).symm (F.mark z _)) i = _
  rw [LinearEquiv.symm_apply_apply]

/-- The complex polarization matrix is constant in the common marking.
Source: Birkenhake–Lange, §§5.2, 9.6. -/
theorem form_matrix :
    LinearMap.toMatrix₂ (Algebra.TensorProduct.basis ℂ (F.basis z))
      (Algebra.TensorProduct.basis ℂ (F.basis z))
      ((polarizationForm (torusCohomology_cupProductOf (F.fibre z).X)
        (F.polarized z).nondegenerate).baseChange ℂ) = R.form.map (algebraMap ℚ ℂ) := by
  ext i j
  simp only [LinearMap.toMatrix₂_apply, Algebra.TensorProduct.basis_apply,
    LinearMap.BilinForm.baseChange_tmul, one_mul, Matrix.map_apply,
    PELSplitReference.form, PELSplitFamily.basis, Module.Basis.map_apply]
  rw [F.form_eq, Algebra.algebraMap_eq_smul_one]

/-- The same reference coordinates retain the full quaternionic Rosati equation.
Source: Birkenhake–Lange, §§5.5, 9.6. -/
theorem action_adjoint (d : ℍ[ℚ, -3, 0, R.b])
    (x y : HQ (F.fibre z).X 1) :
    polarizationForm (torusCohomology_cupProductOf (F.fibre z).X)
      (F.polarized z).nondegenerate
      ((abelianEnd0Action (F.fibre z).X (F.action z d)).unop x) y =
    polarizationForm (torusCohomology_cupProductOf (F.fibre z).X)
      (F.polarized z).nondegenerate x
      ((abelianEnd0Action (F.fibre z).X (F.action z (star d))).unop y) := by
  obtain ⟨x, rfl⟩ := (F.mark z).surjective x
  obtain ⟨y, rfl⟩ := (F.mark z).surjective y
  rw [F.action_eq, F.action_eq, F.form_eq, F.form_eq]
  exact R.adjoint d x y

/-- The selected quadratic generator is unchanged on every fibre.
Source: Birkenhake–Lange, §§9.4–9.6. -/
theorem action_generator :
    (F.fibre z).W.J =
      (abelianEnd0Action (F.fibre z).X (F.action z ⟨0, 1, 0, 0⟩)).unop := by
  ext x
  obtain ⟨x, rfl⟩ := (F.mark z).surjective x
  rw [F.action_eq, ← R.eisenstein, F.generator_eq]

#print axioms action_matrix
#print axioms form_matrix
#print axioms action_adjoint
#print axioms action_generator
end PELSplitFamily
end HodgeLean.Foundations.Program.GeneralTypeIII
