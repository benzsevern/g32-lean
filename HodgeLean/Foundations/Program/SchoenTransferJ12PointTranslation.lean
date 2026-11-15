import HodgeLean.Foundations.Program.SchoenTransferJ12PointConstant
import HodgeLean.Foundations.Program.SchoenTransferSuppliers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Translation by an actual complex point acts identically on every rational cohomology degree.
Source: primitive degree one, constant-point vanishing and the abelian exterior presentation. -/
theorem s4_selected_point_translation_pullback
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (e : ComplexPoint A) (n : ℕ) :
    homPullback (((Over.homMk A.hom : A ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) * 𝟙 A) n =
      LinearMap.id := by
  let t : A ⟶ A := ((Over.homMk A.hom : A ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) * 𝟙 A
  have h1 : homPullback t 1 = homPullback (𝟙 A) 1 := by
    rw [s4_homPullback_mul, s4_selected_point_constant_pullback_positive A A e 1 (by omega), zero_add]
  calc
    homPullback t n = homPullback (𝟙 A) n := by
      rw [spec_homPullback_eq_cupWedgeEquiv t n,
        spec_homPullback_eq_cupWedgeEquiv (𝟙 A) n, h1]
    _ = LinearMap.id := spec_homPullback_id n

#print axioms s4_selected_point_translation_pullback
end HodgeLean.Foundations.Program
