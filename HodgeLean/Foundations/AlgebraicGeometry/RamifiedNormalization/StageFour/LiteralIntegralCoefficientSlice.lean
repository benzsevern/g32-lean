import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CoefficientChartSlice
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosureCoefficientFibre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A literal integral chart retains every integral evaluation on its actual covering-slice locus. -/
theorem literal_integral_coefficient_slice
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    {W X B : Over (Spec ↧ℂ)} [IsSeparated B.hom]
    (β : W ⟶ X) (b : X ⟶ B) (x : ComplexPoint B)
    (i : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶ W)
    [IsOpenImmersion i.left]
    (j : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X)
    (hi : (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))
      (ComplexPoint.specMap_comp_affineSpecStructureMap
        (IsScalarTower.toAlgHom ℂ A (integralClosure A L)))) ≫ j = i ≫ β)
    (f : R →ₐ[ℂ] A)
    (c : Over.mk (ComplexPoint.affineSpecStructureMap R) ⟶ B) [Mono c]
    (hj : j ≫ b = Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap f) ≫ c)
    (φ : R →ₐ[ℂ] ℂ) (hx : Point.map c ((ComplexPoint.affineSpecEquiv R).symm φ) = x)
    (hirange : Set.range i.left = β.left ⁻¹' Set.range j.left) :
    ∃ H : integralCoefficientFibre (L := L) f φ ≃ₜ
      {z : ComplexPoint (coveringSlice β b x) //
        (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
          (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left},
      ∀ z, Point.map (pullback.fst β (pullback.fst b x)) (H z).val =
        Point.map i ((ComplexPoint.affineSpecEquiv (integralClosure A L)).symm z.val) := by
  let n : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap A) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))
      (ComplexPoint.specMap_comp_affineSpecStructureMap
        (IsScalarTower.toAlgHom ℂ A (integralClosure A L)))
  obtain ⟨Hc, hHc⟩ := integral_closure_chart_coefficient_fibre_homeomorph f φ _ n
    (Iso.refl _) (by simp only [Iso.refl_hom, Category.id_comp]; rfl)
  obtain ⟨Hs, hHs⟩ := coefficient_chart_covering_slice_homeomorph f β b x i j n hi
    c hj φ hx hirange
  refine ⟨Hc.symm.trans Hs, ?_⟩
  intro z
  have he : (Hc.symm z).val =
      (ComplexPoint.affineSpecEquiv (integralClosure A L)).symm z.val := by
    apply (ComplexPoint.affineSpecEquiv (integralClosure A L)).injective
    rw [Equiv.apply_symm_apply]
    apply AlgHom.toRingHom_injective
    have hz := hHc (Hc.symm z)
    rw [Hc.apply_symm_apply] at hz
    change (Spec.preimage (Hc.symm z).val.left).hom = z.val.toRingHom
    simpa only [Iso.refl_hom, Category.comp_id, Spec.homEquivRingHom_apply,
      CategoryTheory.ConcreteCategory.homEquiv, Equiv.coe_fn_mk] using hz.symm
  exact (hHs (Hc.symm z)).trans (congrArg (Point.map i) he)

end AlgebraicGeometry.RamifiedNormalization.StageFour
