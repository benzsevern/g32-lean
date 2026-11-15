import HodgeLean.Foundations.Program.SchoenTowerI2aStrictOpenSquare

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An absent branch stays absent on every commuting open strict-transform
chart over the specified base neighborhood.
Source: Hartshorne, Algebraic Geometry, II.7, strict transforms;
Mathlib, `Scheme.IdealSheafData.vanishingIdeal_bot`. -/
theorem s2v_i2a_absent_strict_branch_on_open_square
    {X Y U V : Scheme.{0}} (f : X ⟶ Y) (u : U ⟶ X) [IsOpenImmersion u]
    (c : V ⟶ Y) (v : U ⟶ V) (hsq : u ≫ f = v ≫ c)
    (D K : Y.IdealSheafData) (hD : D.comap c = ⊤) :
    (s2c_strictTransform f D K).comap u = ⊤ := by
  rw [s2v_i2a_strict_transform_open_square f u c v hsq, hD]
  unfold s2c_strictTransform
  simp
  change Scheme.IdealSheafData.vanishingIdeal (⊥ : TopologicalSpace.Closeds U) = ⊤
  exact Scheme.IdealSheafData.vanishingIdeal_bot

end HodgeLean.Foundations.Program
