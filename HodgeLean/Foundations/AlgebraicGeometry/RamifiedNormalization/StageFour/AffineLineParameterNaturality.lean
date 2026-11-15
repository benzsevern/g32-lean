import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineLineParameter

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restricting an actual affine parameter along a complex algebra map retains the original element. -/
theorem affineLineParameter_naturality
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (q : A) :
    (Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap f) :
        Over.mk (ComplexPoint.affineSpecStructureMap B) ⟶
          Over.mk (ComplexPoint.affineSpecStructureMap A)) ≫ affineLineParameter q =
      affineLineParameter (f q) := by
  let aq : Polynomial ℂ →ₐ[ℂ] A := Polynomial.aeval q
  let bq : Polynomial ℂ →ₐ[ℂ] B := Polynomial.aeval (f q)
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom aq.toRingHom) =
    Spec.map (CommRingCat.ofHom bq.toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (f.comp aq).toRingHom = bq.toRingHom
  congr 1
  apply Polynomial.algHom_ext
  simp only [aq, bq, AlgHom.comp_apply, Polynomial.aeval_X]

end AlgebraicGeometry.RamifiedNormalization.StageFour
