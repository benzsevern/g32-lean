import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalCoefficientPointFibre
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CoveringSliceChartPoints

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual normal chart coefficient fibre identifies with precisely its original covering-slice chart locus and retains the original covering point. -/
theorem coefficient_chart_covering_slice_homeomorph
    {R A : Type} [CommRing R] [CommRing A] [Algebra ℂ R] [Algebra ℂ A]
    {U W B' B : Over (Spec ↧ℂ)} [IsSeparated B.hom]
    (f : R →ₐ[ℂ] A) (β : W ⟶ B') (b : B' ⟶ B) (x : ComplexPoint B)
    (i : U ⟶ W) [IsOpenImmersion i.left]
    (j : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ B')
    (n : U ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A))
    (hn : n ≫ j = i ≫ β)
    (c : Over.mk (ComplexPoint.affineSpecStructureMap R) ⟶ B) [Mono c]
    (hj : j ≫ b = Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap f) ≫ c)
    (φ : R →ₐ[ℂ] ℂ)
    (hx : Point.map c ((ComplexPoint.affineSpecEquiv R).symm φ) = x)
    (hirange : Set.range i.left = β.left ⁻¹' Set.range j.left) :
    ∃ H : {u : ComplexPoint U // ComplexPoint.affineSpecComplexPointMap f (Point.map n u) =
          (ComplexPoint.affineSpecEquiv R).symm φ} ≃ₜ
        {z : ComplexPoint (coveringSlice β b x) //
          (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
            (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left},
      ∀ u, Point.map (pullback.fst β (pullback.fst b x)) (H u).val = Point.map i u.val := by
  have hbase : n ≫ (Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap f) :
        Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶
          Over.mk (ComplexPoint.affineSpecStructureMap R)) ≫ c = i ≫ β ≫ b := by
    rw [← hj, ← Category.assoc, hn, Category.assoc]
  obtain ⟨Hc, hHc⟩ := original_coefficient_point_fibre_homeomorph f n c (i ≫ β ≫ b)
    hbase φ x hx
  obtain ⟨Hs, hHs⟩ := covering_slice_chart_point_homeomorph β b x i j hirange
  refine ⟨Hc.symm.trans Hs, ?_⟩
  intro u
  have he : (Hc.symm u).val = u.val := by
    have h := hHc (Hc.symm u)
    rw [Hc.apply_symm_apply] at h
    exact h.symm
  exact (hHs (Hc.symm u)).trans (congrArg (Point.map i) he)

end AlgebraicGeometry.RamifiedNormalization.StageFour
