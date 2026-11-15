import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenCycleProjectiveAffineIdeals

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every commuting open source square retains the actual reduced strict
transform ideal sheaf after restricting its branch and centre ideals.
Source: Hartshorne, Algebraic Geometry, II.7, strict transforms;
Mathlib, `Scheme.IdealSheafData.support_comap`. -/
theorem s2v_i2a_strict_transform_open_square
    {X Y U V : Scheme.{0}} (f : X ⟶ Y) (u : U ⟶ X) [IsOpenImmersion u]
    (c : V ⟶ Y) (v : U ⟶ V) (hsq : u ≫ f = v ≫ c)
    (D K : Y.IdealSheafData) :
    (s2c_strictTransform f D K).comap u =
      s2c_strictTransform v (D.comap c) (K.comap c) := by
  unfold s2c_strictTransform
  rw [s2e_open_comap_vanishingIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  change u ⁻¹' closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) =
    closure (v ⁻¹' (((D.comap c).support : Set V) \ ((K.comap c).support : Set V)))
  rw [u.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage u.continuous,
    Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
  change closure ((u ≫ f) ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) =
    closure (v ⁻¹' (c ⁻¹' (D.support : Set Y) \ c ⁻¹' (K.support : Set Y)))
  rw [hsq, ← Set.preimage_sdiff]
  rfl

end HodgeLean.Foundations.Program
