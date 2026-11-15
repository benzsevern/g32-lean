import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosureCoefficientFibre
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineChartPointFibre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A retained base coefficient square identifies the original point fibre with the prescribed scalar coefficient evaluation fibre. -/
theorem original_coefficient_point_fibre_homeomorph
    {R A : Type} [CommRing R] [CommRing A] [Algebra ℂ R] [Algebra ℂ A]
    {X B : Over (Spec ↧ℂ)} (f : R →ₐ[ℂ] A)
    (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A))
    (c : Over.mk (ComplexPoint.affineSpecStructureMap R) ⟶ B) [Mono c]
    (q : X ⟶ B)
    (hbase : p ≫ (Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap f) :
        Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶
          Over.mk (ComplexPoint.affineSpecStructureMap R)) ≫ c = q)
    (φ : R →ₐ[ℂ] ℂ) (x : ComplexPoint B)
    (hx : Point.map c ((ComplexPoint.affineSpecEquiv R).symm φ) = x) :
    ∃ H : {z : ComplexPoint X // Point.map q z = x} ≃ₜ
        {z : ComplexPoint X // ComplexPoint.affineSpecComplexPointMap f (Point.map p z) =
          (ComplexPoint.affineSpecEquiv R).symm φ},
      ∀ z, (H z).val = z.val := by
  let fc : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap R) :=
    Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap f)
  have he (z : ComplexPoint X) :
      Point.map c (ComplexPoint.affineSpecComplexPointMap f (Point.map p z)) = Point.map q z := by
    change Point.map c (Point.map fc (Point.map p z)) = _
    rw [← Point.map_comp_apply, ← Point.map_comp_apply]
    exact congrArg (fun k => Point.map k z) hbase
  have hiff (z : ComplexPoint X) : Point.map q z = x ↔
      ComplexPoint.affineSpecComplexPointMap f (Point.map p z) =
        (ComplexPoint.affineSpecEquiv R).symm φ := by
    rw [← hx, ← he]
    exact cancel_mono c
  exact ⟨(Homeomorph.refl _).subtype hiff, fun _ => rfl⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
