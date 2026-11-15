import HodgeLean.Foundations.Program.SchoenCycleFixedStalkAction
import HodgeLean.Foundations.Program.SchoenCycleStalkScalars

/-! # Scalars under transported fixed-point stalk pullback -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Transport between equal scheme points preserves their actual complex scalars.
Source: Hartshorne, Algebraic Geometry, II.2, stalks over the base field. -/
theorem s2e_stalk_complex_scalar_transport
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (x y : X.left) (h : x = y) (c : ℂ) :
    (X.left.presheaf.stalkCongr (.of_eq h)).hom
      (HodgeLean.Foundations.Curves.stalkC x c) =
        HodgeLean.Foundations.Curves.stalkC y c := by
  subst y
  simp

/-- Transported fixed-point pullback over the complex base preserves its
actual complex scalar map.
Source: Hartshorne, Algebraic Geometry, II.2, stalks over the base field. -/
theorem s2e_fixed_point_stalkPullback_scalars
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (f : X ⟶ X) (p : X.left) (hp : f.left p = p) (c : ℂ) :
    s2e_fixed_point_stalkPullback X.left f.left p hp
      (HodgeLean.Foundations.Curves.stalkC p c) = HodgeLean.Foundations.Curves.stalkC p c := by
  have he : (X.left.presheaf.stalkCongr (.of_eq hp)).inv =
      (X.left.presheaf.stalkCongr (.of_eq hp.symm)).hom := by
    simp only [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkCongr_hom]
  change (f.left.stalkMap p).hom ((X.left.presheaf.stalkCongr (.of_eq hp)).inv.hom
    (HodgeLean.Foundations.Curves.stalkC p c)) = _
  rw [he]
  change f.left.stalkMap p ((X.left.presheaf.stalkCongr (.of_eq hp.symm)).hom
    (HodgeLean.Foundations.Curves.stalkC p c)) = _
  rw [s2e_stalk_complex_scalar_transport X p (f.left p) hp.symm c]
  exact s2e_stalkMap_complex_scalars X X f p c

end HodgeLean.Foundations.Program
