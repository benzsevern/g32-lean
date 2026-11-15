import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosureChartPoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual original-field deck square determines its literal integral-chart action, without replacing the original chart or field point. -/
theorem original_normalized_chart_deck_square
    {A L : Type} [CommRing A] [Field L] [Algebra ℂ A]
    [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (W : Over (Spec ↧ℂ)) [IsSeparated W.hom]
    (η : Spec ↧L ⟶ W.left) [IsDominant η]
    (J : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶ W)
    [IsOpenImmersion J.left]
    (hJ : Spec.map (CommRingCat.ofHom (integralClosure A L).subtype) ≫ J.left = η)
    (d : W ⟶ W) (δ : L ≃ₐ[A] L)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ η = η ≫ d.left) :
    Spec.map (CommRingCat.ofHom δ.mapIntegralClosure.toRingHom) ≫ J.left = J.left ≫ d.left := by
  let p : Spec ↧L ⟶ Spec ↧(integralClosure A L) :=
    Spec.map (CommRingCat.ofHom ((integralClosure A L).subtype : integralClosure A L →+* L))
  haveI : IsDominant (p ≫ J.left) := hJ.symm ▸ inferInstance
  haveI : IsDominant p := IsDominant.of_comp_of_isOpenImmersion p J.left
  let ρ := δ.mapIntegralClosure.restrictScalars ℂ
  let D : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) :=
    Over.homMk (Spec.map (CommRingCat.ofHom ρ.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap ρ.toAlgHom)
  have hbase : (D.left ≫ J.left) ≫ W.hom = (J.left ≫ d.left) ≫ W.hom := by
    rw [Category.assoc, J.w, D.w, Category.assoc, d.w, J.w]
  haveI : IsReduced (Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L))).left := by
    change IsReduced (Spec ↧(integralClosure A L))
    infer_instance
  change D.left ≫ J.left = J.left ≫ d.left
  apply ext_of_isDominant_of_isSeparated W.hom hbase p
  have hρ : p ≫ D.left = Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ p := by
    change Spec.map (CommRingCat.ofHom ((integralClosure A L).subtype : integralClosure A L →+* L)) ≫
      Spec.map (CommRingCat.ofHom ρ.toRingHom) =
      Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((integralClosure A L).subtype : integralClosure A L →+* L))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  rw [← Category.assoc, hρ, Category.assoc, hJ, hδ, ← Category.assoc, hJ]

end AlgebraicGeometry.RamifiedNormalization.StageFour
