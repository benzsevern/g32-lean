import HodgeLean.Foundations.Program.SchoenCycleC11AffineAssemblyHelpers
import HodgeLean.Foundations.Curves.CubicGrpObj
import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected

/-! # Analytic fibres of the finite etale part of the retained cover -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A finite etale cover over a smooth integral complex base gives an actual
analytic covering with finite fibres. -/
theorem s2e_c1_finite_etale_analytic_cover
    (X Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsCoveringMap (Point.map f) ∧
      (∀ y : ComplexPoint Y, Set.Finite ((Point.map f) ⁻¹' {y})) := by
  haveI : LocallyOfFiniteType X.hom := by
    rw [← Over.w f]
    change LocallyOfFiniteType (f.left ≫ Y.hom)
    infer_instance
  apply s2e_c11_analytic_cover_of_affine_restrictions X Y f
  · exact s2e_c11_finite_etale_local_homeomorph_over_smooth
      (TopologicalSpace.dim Y.left) X Y f
  · intro U hU
    exact (s2e_c11_finite_affine_restriction_point_proper X Y f U hU).isClosedMap

/-- A deck map of an integral finite etale cover that fixes a complex point
is the identity on the actual scheme. -/
theorem s2e_c1_etale_deck_eq_id_of_fixed_point
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [IsIntegral Y.left] [Smooth Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (d : X ⟶ X) (hd : d ≫ f = f)
    (z : ComplexPoint X) (hz : Point.map d z = z) : d = 𝟙 X := by
  haveI : Smooth X.hom := by
    rw [← Over.w f]
    infer_instance
  haveI : IsSeparated X.hom := by
    rw [← Over.w f]
    infer_instance
  haveI : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  haveI : ConnectedSpace (ComplexPoint X) := AlgebraicGeometry.ComplexPoint.connectedSpace X
  have hcover := (s2e_c1_finite_etale_analytic_cover X Y f).1
  have hcomp : Point.map f ∘ Point.map d = Point.map f ∘ id := by
    funext x
    change (x ≫ d) ≫ f = x ≫ f
    rw [Category.assoc, hd]
  have hmap : Point.map d = id := hcover.eq_of_comp_eq
    (Point.continuous_map d) continuous_id hcomp z hz
  apply HodgeLean.Foundations.Curves.complexPoint_hom_ext
  intro x
  have hx : x ≫ d = x := congrFun hmap x
  exact hx.trans (Category.comp_id x).symm

end HodgeLean.Foundations.Program
