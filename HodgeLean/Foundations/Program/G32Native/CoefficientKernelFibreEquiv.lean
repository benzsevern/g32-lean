import HodgeLean.Foundations.Program.G32Native.CoefficientKernelTransport

/-! # Linear equivalences onto the original projective kernel fibres -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Bundle
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- Kernel membership is equivalent to annihilation of the ordered homogeneous line. -/
theorem coefficient_mem_projectiveKernel_iff (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ)))
    (a : Module.Dual ℂ (Fin (k + 1) → ℂ)) :
    (a (Pi.single 0 1), fun i : Fin k => a (Pi.single i.succ 1)) ∈
        projectiveNormalKernel k p ↔
      a ∈ (s2e_projectiveLinearEquiv (normalHomogeneousCoordinates k) p).submodule.dualAnnihilator := by
  refine ⟨?_, coefficient_mem_projectiveKernel k p a⟩
  induction p using Projectivization.ind with
  | h v hv =>
    intro ha
    rw [projectiveNormalKernel_mk, LinearMap.mem_ker, ← coefficient_evaluation_model] at ha
    apply (Submodule.mem_dualAnnihilator a).mpr
    intro w hw
    change w ∈ (Projectivization.mk ℂ (normalHomogeneousCoordinates k v) _).submodule at hw
    rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [map_smul, ha, smul_zero]

/-- Ordered evaluation identifies the whole covector space with model coordinates. -/
def coefficientModelCoordinates (k : ℕ) :
    Module.Dual ℂ (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (ℂ × (Fin k → ℂ)) :=
  (coefficientCoordinateEquiv k).trans (normalHomogeneousCoordinates k).symm

/-- The model coordinates are the literal ordered evaluations. -/
theorem coefficientModelCoordinates_apply (k : ℕ)
    (a : Module.Dual ℂ (Fin (k + 1) → ℂ)) :
    coefficientModelCoordinates k a =
      (a (Pi.single 0 1), fun i : Fin k => a (Pi.single i.succ 1)) := by
  apply Prod.ext
  · exact coefficientCoordinateEquiv_apply k a 0
  · ext i
    exact coefficientCoordinateEquiv_apply k a i.succ

/-- Every actual kernel vector has a unique covector on the specified homogeneous line. -/
def coefficientKernelFibreEquiv (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    (s2e_projectiveLinearEquiv (normalHomogeneousCoordinates k) p).submodule.dualAnnihilator ≃ₗ[ℂ]
      projectiveNormalKernel k p where
  toFun a := ⟨coefficientModelCoordinates k a.1, by
    rw [coefficientModelCoordinates_apply]
    exact coefficient_mem_projectiveKernel k p a.1 a.2⟩
  invFun v := ⟨(coefficientModelCoordinates k).symm v.1, by
    apply (coefficient_mem_projectiveKernel_iff k p _).mp
    rw [← coefficientModelCoordinates_apply, LinearEquiv.apply_symm_apply]
    exact v.2⟩
  left_inv a := Subtype.ext ((coefficientModelCoordinates k).symm_apply_apply a.1)
  right_inv v := Subtype.ext ((coefficientModelCoordinates k).apply_symm_apply v.1)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := Subtype.ext (map_smul _ _ _)

end HodgeLean.Foundations.Program.G32Native
