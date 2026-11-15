import HodgeLean.Foundations.Program.SchoenCycleU1AffineCharts

/-! # Actual complex affine chart squares -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual morphism between specified affine chart sections reconstructs
the original scheme morphism on the source chart, over its complex base.
Source: Mathlib, `IsAffineOpen.SpecMap_appLE_fromSpec`; Hartshorne, II.2. -/
theorem s2e_u1_fromSpecOver_naturality
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens)
    (hUa : IsAffineOpen U) (hVa : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V) :
    letI := s2e_step1_sectionAlgebra X U
    letI := s2e_step1_sectionAlgebra Y V
    s2e_u1_fromSpecOver X U hUa ≫ f =
      s2e_u1_specOverMap (s2e_u1_appLE_algHom X Y f V U hUV) ≫
        s2e_u1_fromSpecOver Y V hVa := by
  letI := s2e_step1_sectionAlgebra X U
  letI := s2e_step1_sectionAlgebra Y V
  apply Over.OverMorphism.ext
  change hUa.fromSpec ≫ f.left = Spec.map (f.left.appLE V U hUV) ≫ hVa.fromSpec
  exact (hVa.SpecMap_appLE_fromSpec f.left hUa hUV).symm

end HodgeLean.Foundations.Program
