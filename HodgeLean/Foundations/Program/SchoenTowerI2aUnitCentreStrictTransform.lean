import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- When the centre ideal is the unit ideal, the actual reduced strict
transform is the radical of the actual pulled-back branch ideal.
Source: Hartshorne, Algebraic Geometry, II.7, strict transforms;
Mathlib, `Scheme.IdealSheafData.vanishingIdeal_support`. -/
theorem s2v_i2a_strict_transform_unit_centre
    {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Y.IdealSheafData) :
    s2c_strictTransform f D ⊤ = (D.comap f).radical := by
  unfold s2c_strictTransform
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  apply TopologicalSpace.Closeds.ext
  have hc : IsClosed (f ⁻¹' (D.support : Set Y)) := D.support.isClosed.preimage f.continuous
  change closure (f ⁻¹' ((D.support : Set Y) \ ((⊤ : Y.IdealSheafData).support : Set Y))) =
    ((D.comap f).support : Set X)
  simp [Scheme.IdealSheafData.support_comap, hc.closure_eq]

end HodgeLean.Foundations.Program
