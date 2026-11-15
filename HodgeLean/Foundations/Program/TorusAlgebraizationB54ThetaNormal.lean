import HodgeLean.Foundations.Program.TorusAlgebraizationB54NormalScheme
import HodgeLean.Foundations.Program.TorusAlgebraizationB54NormalSections
import HodgeLean.Foundations.Program.TorusAlgebraizationB54CoordinateRing

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b54_theta_model_normal_of_sections {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3))
    (hgen : Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤) :
    zmtiso_IsNormal (b5_model Λ F hF Q).left := by
  letI := b54_S_isDomain Λ F hF Q
  letI := b54_S_integrallyClosed Λ F hF Q
  let v := b54_basisGenerator Λ F hF Q b
  have hv (i : ι) : v i ∈ b5_grade Λ F hF Q 1 := ⟨b i, rfl⟩
  have hne (i : ι) : v i ≠ 0 := by
    intro hi
    have hh := congrArg (fun r : b5_S Λ F hF Q => r 1) hi
    apply b.ne_zero i
    simpa [v, b54_basisGenerator, DirectSum.of_apply] using hh
  exact b54_proj_normal_of_degree_one (b5_grade Λ F hF Q) v hv hne
    (b54_irrelevant_le_span_generators _ v hv
      (b54_basis_generates_over_gradeZero Λ F hF Q b hgen))

end HodgeLean.Foundations.Program
