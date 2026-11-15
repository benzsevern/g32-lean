import HodgeLean.Foundations.Program.SchoenSelectedGeometryComplexFibers
import HodgeLean.Foundations.Program.RiemannSurfaceQuotientDefs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- An actual projective morphism realizing a finite orbit projection is finite. -/
theorem s4_selected_orbit_projection_finite
    (G C : Type) [Group G] [Finite G] [MulAction G C]
    (X Y : Over (Spec ↧ℂ)) [IsProjective X.hom] [IsProjective Y.hom]
    (q : X ⟶ Y) (eX : C ≃ ComplexPoint X) (eY : rsq_Quot G C ≃ ComplexPoint Y)
    (hq : ∀ x, Point.map q (eX x) = eY (rsq_proj G C x)) : IsFinite q.left := by
  classical
  haveI : IsProper (q.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  haveI : IsProper q.left := IsProper.of_comp q.left Y.hom
  apply s0_finite_of_finite_complex_fibers X Y q
  intro y
  let c : C := Quotient.out (eY.symm y)
  have hc : eY (rsq_proj G C c) = y := by
    change eY (Quotient.mk _ (Quotient.out (eY.symm y))) = y
    rw [Quotient.out_eq, eY.apply_symm_apply]
  apply (Set.finite_range (fun g : G => eX (g • c))).subset
  intro x hx
  have hx' : rsq_proj G C c = rsq_proj G C (eX.symm x) := by
    apply eY.injective
    rw [hc, ← hq, eX.apply_symm_apply]
    exact hx.symm
  obtain ⟨g, hg⟩ := (rsq_proj_isGaloisCover G C).2 c (eX.symm x) hx'
  exact ⟨g, (congrArg eX hg).trans (eX.apply_symm_apply x)⟩

#print axioms s4_selected_orbit_projection_finite

end HodgeLean.Foundations.Program
