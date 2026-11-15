import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs

noncomputable section
set_option maxHeartbeats 100000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Equivariance transports a fixed point to the underlying scheme point. -/
theorem s2v_l1b_rotation_scheme_fixed
    {G Q : Type*} [Group G] [MulAction G Q]
    (Y : Over (Spec ↧ℂ)) (a : G → (Y ⟶ Y))
    (eY : Q → ComplexPoint Y)
    (he : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (u : G) (y : Q) (hy : u • y = y) :
    (a u).left ((eY y).left (IsLocalRing.closedPoint ℂ)) =
      (eY y).left (IsLocalRing.closedPoint ℂ) := by
  have h := he u y
  rw [hy] at h
  exact congrArg (fun z : ComplexPoint Y => z.left (IsLocalRing.closedPoint ℂ)) h

end HodgeLean.Foundations.Program
