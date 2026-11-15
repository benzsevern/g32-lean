import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalNormalizedChartDeck
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientAction
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original integral coefficient action agrees with the actual retained scheme deck map on every point of its slice chart. -/
theorem integral_chart_slice_deck
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (W X B : Over (Spec ↧ℂ)) [IsSeparated W.hom]
    (β : W ⟶ X) (b : X ⟶ B) (x : ComplexPoint B)
    [Mono (pullback.fst β (pullback.fst b x))]
    (η : Spec ↧L ⟶ W.left) [IsDominant η]
    (J : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶ W)
    [IsOpenImmersion J.left]
    (hJ : Spec.map (CommRingCat.ofHom (integralClosure A L).subtype) ≫ J.left = η)
    (d : W ⟶ W) (hd : d ≫ β = β) (δ : L ≃ₐ[A] L)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ η = η ≫ d.left)
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ)
    (H : integralCoefficientFibre (L := L) f φ → ComplexPoint (coveringSlice β b x))
    (hH : ∀ z, Point.map J ((ComplexPoint.affineSpecEquiv (integralClosure A L)).symm z.val) =
      Point.map (pullback.fst β (pullback.fst b x)) (H z)) :
    ∀ z, H (integralCoefficientFibreDeck f φ δ z) = Point.map (sliceDeck β b x d hd) (H z) := by
  let C := Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L))
  let ρ := δ.mapIntegralClosure.restrictScalars ℂ
  let DC : C ⟶ C := Over.homMk (Spec.map (CommRingCat.ofHom ρ.toRingHom))
    (ComplexPoint.specMap_comp_affineSpecStructureMap ρ.toAlgHom)
  have hJD : DC ≫ J = J ≫ d := by
    apply Over.OverMorphism.ext
    exact original_normalized_chart_deck_square W η J hJ d δ hδ
  let p := fun z : integralCoefficientFibre (L := L) f φ =>
    (ComplexPoint.affineSpecEquiv (integralClosure A L)).symm z.val
  have hp (z) : Point.map DC (p z) = p (integralCoefficientFibreDeck f φ δ z) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom z.val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ρ.toRingHom) = _
    rw [← Spec.map_comp]
    rfl
  intro z
  let a := pullback.fst β (pullback.fst b x)
  have hh : Point.map a (H (integralCoefficientFibreDeck f φ δ z)) =
      Point.map a (Point.map (sliceDeck β b x d hd) (H z)) := by
    calc
      _ = Point.map J (p (integralCoefficientFibreDeck f φ δ z)) := (hH _).symm
      _ = Point.map J (Point.map DC (p z)) := congrArg (Point.map J) (hp z).symm
      _ = Point.map d (Point.map J (p z)) := by
        change (p z ≫ DC) ≫ J = (p z ≫ J) ≫ d
        simp only [Category.assoc, hJD]
      _ = Point.map d (Point.map a (H z)) := congrArg (Point.map d) (hH z)
      _ = _ := by
        change (H z ≫ a) ≫ d = (H z ≫ sliceDeck β b x d hd) ≫ a
        simp only [Category.assoc, a, sliceDeck, pullback.lift_fst]
  exact (cancel_mono a).mp hh

end AlgebraicGeometry.RamifiedNormalization.StageFour
