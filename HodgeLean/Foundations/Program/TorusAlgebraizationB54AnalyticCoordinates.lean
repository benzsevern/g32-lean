import HodgeLean.Foundations.Program.TorusAlgebraizationDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b54_sectionEval (z : b5_V Λ F) : b5_sections Λ F hF Q 3 →ₗ[ℂ] ℂ :=
  (LinearMap.proj z).comp (b5_sections Λ F hF Q 3).subtype

def b54_sectionCoordinates {ι : Type*} (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3))
    (z : b5_V Λ F) : ι → ℂ := fun i ↦ (b i).val z

theorem b54_sectionCoordinates_ne_zero {ι : Type*}
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) (z : b5_V Λ F)
    (hz : ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0) :
    b54_sectionCoordinates Λ F hF Q b z ≠ 0 := by
  intro h
  have he : b54_sectionEval Λ F hF Q z = 0 := by
    apply b.ext
    intro i
    exact congrFun h i
  obtain ⟨s, hs⟩ := hz
  exact hs (LinearMap.congr_fun he s)

theorem b54_sectionCoordinates_continuous {ι : Type*}
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) :
    Continuous (b54_sectionCoordinates Λ F hF Q b) :=
  continuous_pi fun i ↦ (b i).property.1.continuous

theorem b54_sectionCoordinates_translate {ι : Type*}
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) (l : Λ) (z : b5_V Λ F) :
    b54_sectionCoordinates Λ F hF Q b (z + b5_lattice Λ F l) =
      b5_factor Λ F hF Q l z ^ 3 • b54_sectionCoordinates Λ F hF Q b z := by
  funext i
  exact (b i).property.2 l z

theorem b54_sectionCoordinates_proportional {ι : Type*}
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) (z w : b5_V Λ F) (c : ℂ)
    (h : b54_sectionCoordinates Λ F hF Q b w = c • b54_sectionCoordinates Λ F hF Q b z)
    (s : b5_sections Λ F hF Q 3) : s.val w = c * s.val z := by
  have he : b54_sectionEval Λ F hF Q w = c • b54_sectionEval Λ F hF Q z := by
    apply b.ext
    intro i
    exact congrFun h i
  exact LinearMap.congr_fun he s

end HodgeLean.Foundations.Program
