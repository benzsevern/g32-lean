import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction
import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver

/-! # Affine chart scalar structures and relative maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The affine chart inclusion with its actual complex scalar structure.
Source: Mathlib, `IsAffineOpen.SpecMap_appLE_fromSpec`; Hartshorne, II.2. -/
def s2e_u1_fromSpecOver (X : Over (Spec ↧ℂ)) (V : X.left.Opens) (hV : IsAffineOpen V) :
    letI := s2e_step1_sectionAlgebra X V
    s2e_u1_specOver Γ(X.left, V) ⟶ X := by
  letI := s2e_step1_sectionAlgebra X V
  refine Over.homMk hV.fromSpec ?_
  change hV.fromSpec ≫ X.hom =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ V le_top)
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact ((isAffineOpen_top _).SpecMap_appLE_fromSpec X.hom hV le_top).symm

/-- A map over the complex base induces a complex algebra map on chart sections.
Source: Hartshorne, Algebraic Geometry, II.2--II.3; Mathlib, `Scheme.Hom.appLE_comp_appLE`. -/
def s2e_u1_appLE_algHom (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (hVU : V ≤ f.left ⁻¹ᵁ U) :
    letI := s2e_step1_sectionAlgebra Y U
    letI := s2e_step1_sectionAlgebra X V
    Γ(Y.left, U) →ₐ[ℂ] Γ(X.left, V) := by
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X V
  refine ⟨(f.left.appLE U V hVU).hom, ?_⟩
  intro c
  have he : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Y.hom.appLE ⊤ U le_top ≫
      f.left.appLE U V hVU =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ V le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact congrArg (fun g : X.left ⟶ Spec ↧ℂ => g.appLE ⊤ V le_top) (Over.w f)
  exact congrArg (fun g : CommRingCat.of ℂ ⟶ Γ(X.left, V) => g.hom c) he

end HodgeLean.Foundations.Program
