import HodgeLean.Foundations.Program.G32Native.PrintedPolarizedTriple
import HodgeLean.Foundations.Program.G32Native.HomologicalFormReconstruction

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Module TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.RealDefs.Compare.Markman
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- Extension of the homological form agrees with extension of contraction.
Source: Bourbaki, Algebra, II §5; `IsBaseChange.toDualBaseChange_tmul`. -/
theorem printed_real_riemann_form (ω : ⋀[ℚ]^2 (HQ A 1))
    (φ ψ : Dual ℝ (ℝ ⊗[ℚ] HQ A 1)) :
    printedRealForm A (riemannForm ω) φ ψ = ψ (p1_realContract ω φ) := by
  letI := (torusCohomology_cupProductOf A).finite
  let e := (TensorProduct.isBaseChange ℚ (HQ A 1) ℝ).toDualBaseChange
  have he : (printedRealForm A (riemannForm ω)).compl₁₂ e.toLinearMap e.toLinearMap =
      ((Dual.eval ℝ (ℝ ⊗[ℚ] HQ A 1)).comp (p1_realContract ω)).compl₁₂
        e.toLinearMap e.toLinearMap := by
    ext x y
    simp [printedRealForm, p1_realContract, e, riemannForm,
      LinearMap.BilinForm.baseChange_tmul, LinearMap.baseChange_tmul,
      IsBaseChange.toDualBaseChange_tmul]
    simpa using ((TensorProduct.isBaseChange ℚ (HQ A 1) ℝ).toDualBaseChange_tmul
      1 y (contract ω x)).symm
  obtain ⟨x, rfl⟩ := e.surjective φ
  obtain ⟨y, rfl⟩ := e.surjective ψ
  exact congrArg (fun B : LinearMap.BilinForm ℝ (ℝ ⊗[ℚ] Dual ℚ (HQ A 1)) => B x y) he

#print axioms printed_real_riemann_form
end HodgeLean.Foundations.Program.G32Native
