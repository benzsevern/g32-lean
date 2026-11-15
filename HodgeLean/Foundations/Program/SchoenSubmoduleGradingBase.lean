import HodgeLean.Foundations.Program.SchoenSubmoduleGradingBridge
import HodgeLean.Foundations.Program.SchoenProjMapBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual degree-zero coefficient-ring comparison for subgroup degree pieces. -/
def s2_submoduleDegreeZeroEquiv {K A : Type} [CommRing K] [CommRing A]
    [Algebra K A] (𝒢 : ℕ → Submodule K A) [GradedRing 𝒢] :
    letI := s2_submoduleGradingAsSubgroups 𝒢
    𝒢 0 ≃+* s2_submoduleGradedPieces 𝒢 0 := by
  letI := s2_submoduleGradingAsSubgroups 𝒢
  exact
    { toFun := fun a => ⟨a, a.property⟩
      invFun := fun a => ⟨a, a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }

/-- The actual subgroup grading Proj comparison preserves its explicit degree-zero coefficient map. -/
theorem s2_submoduleGradingProjIso_toSpecZero {K A : Type} [CommRing K] [CommRing A]
    [Algebra K A] (𝒢 : ℕ → Submodule K A) [GradedRing 𝒢] :
    letI := s2_submoduleGradingAsSubgroups 𝒢
    (s2_submoduleGradingProjIso 𝒢).hom ≫ Proj.toSpecZero 𝒢 =
      Proj.toSpecZero (s2_submoduleGradedPieces 𝒢) ≫
        Spec.map (s2_submoduleDegreeZeroEquiv 𝒢).toCommRingCatIso.hom := by
  letI := s2_submoduleGradingAsSubgroups 𝒢
  exact s2_projMap_toSpecZero 𝒢 (s2_submoduleGradedPieces 𝒢)
    { RingHom.id A with map_mem := fun {_} {_} ha => ha } _
    (s2_submoduleDegreeZeroEquiv 𝒢).toRingHom (fun _ => rfl)

end HodgeLean.Foundations.Program
