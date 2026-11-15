import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineNormalizationRestriction
import HodgeLean.Foundations.Program.SchoenTowerDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The literal normalization restriction constructs an actual complex open chart of the original normalization, with its coefficient square and exact image. -/
theorem actual_normalization_chart
    {A L : Type} [CommRing A] [Algebra ℂ A] [Field L]
    (X : Over (Spec ↧ℂ)) (η : Spec ↧L ⟶ X.left)
    [QuasiCompact η] [QuasiSeparated η]
    (j : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X) [IsOpenImmersion j.left]
    (F : A →+* L) (hF : Spec.map (CommRingCat.ofHom F) ≫ j.left = η) :
    ∃ (U : Over (Spec ↧ℂ)) (i : U ⟶ s2b_normalizationOver X η)
      (n : U ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A))
      (E : U.left ≅ Spec ↧(normalizedChart F)),
      IsOpenImmersion i.left ∧ n ≫ j = i ≫ s2b_normalizationMap X η ∧
      E.hom ≫ Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff F)) = n.left ∧
      Set.range i.left = η.fromNormalization ⁻¹' Set.range j.left := by
  let U : Over (Spec ↧ℂ) :=
    Over.mk (pullback.snd η.fromNormalization j.left ≫ ComplexPoint.affineSpecStructureMap A)
  let n : U ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A) :=
    Over.homMk (pullback.snd η.fromNormalization j.left) rfl
  let i : U ⟶ s2b_normalizationOver X η :=
    Over.homMk (pullback.fst η.fromNormalization j.left) (by
      change pullback.fst η.fromNormalization j.left ≫ (η.fromNormalization ≫ X.hom) = _
      rw [← Category.assoc, pullback.condition, Category.assoc, j.w]
      rfl)
  obtain ⟨E, _, hbase⟩ := affine_normalization_restriction η j.left F hF
  refine ⟨U, i, n, E, ?_, ?_, hbase, ?_⟩
  · change IsOpenImmersion (pullback.fst η.fromNormalization j.left)
    infer_instance
  · apply Over.OverMorphism.ext
    exact pullback.condition.symm
  · exact IsOpenImmersion.range_pullbackFst j.left η.fromNormalization

end AlgebraicGeometry.RamifiedNormalization.StageFour
