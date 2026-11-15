import HodgeLean.Foundations.Program.SchoenSelectedGeometryQuotientAction
import HodgeLean.Foundations.Program.RiemannSurfaceQuotientDefs

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Residual inverse action pulls back to inverse deck action on the original curve. -/
theorem s0_residual_deck_pullback
    {H C : Type} [Group H] [MulAction H C] [TopologicalSpace C]
    (K : Subgroup H) [K.Normal]
    (hC : ∀ h : H, Continuous (fun z : C ↦ h • z))
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (eC : C ≃ₜ ComplexPoint X) (eY : rsq_Quot K C ≃ₜ ComplexPoint Y)
    (q : X ⟶ Y) (a : H ⧸ K → (Y ⟶ Y))
    (hq : ∀ z, Point.map q (eC z) = eY (rsq_proj K C z))
    (ha : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (h : H) (n : ℕ) (x : HQ Y n) :
    cohomologyMap ℚ n (TopCat.ofHom ⟨eC, eC.continuous⟩)
      (cupComparison X n (homPullback q n (homPullback (a ((QuotientGroup.mk h)⁻¹)) n x))) =
    cohomologyMap ℚ n (TopCat.ofHom ⟨fun z : C ↦ h⁻¹ • z, hC h⁻¹⟩)
      (cohomologyMap ℚ n (TopCat.ofHom ⟨eC, eC.continuous⟩)
        (cupComparison X n (homPullback q n x))) := by
  apply s0_algebraic_quotient_action X Y ⟨eC, eC.continuous⟩
    ⟨fun z : C ↦ h⁻¹ • z, hC h⁻¹⟩ q (a ((QuotientGroup.mk h)⁻¹)) _ n x
  intro z
  change Point.map (a ((QuotientGroup.mk h)⁻¹)) (Point.map q (eC z)) =
    Point.map q (eC (h⁻¹ • z))
  rw [hq, ha, hq]
  congr 1

#print axioms s0_residual_deck_pullback
end HodgeLean.Foundations.Program
