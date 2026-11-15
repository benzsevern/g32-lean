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

/-- The literal integral-ring spectrum is an actual complex open chart of the original normalization and retains its original field point. -/
theorem literal_normalized_chart_open
    {A L : Type} [CommRing A] [Algebra ℂ A] [Field L]
    (X : Over (Spec ↧ℂ)) (η : Spec ↧L ⟶ X.left)
    [QuasiCompact η] [QuasiSeparated η]
    (j : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X) [IsOpenImmersion j.left]
    (F : A →+* L) (hF : Spec.map (CommRingCat.ofHom F) ≫ j.left = η) :
    letI := ((StageTwo.integralCoeff F).comp (algebraMap ℂ A)).toAlgebra
    ∃ J : Over.mk (ComplexPoint.affineSpecStructureMap (normalizedChart F)) ⟶ s2b_normalizationOver X η,
      IsOpenImmersion J.left ∧
      J.left ≫ η.fromNormalization = Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff F)) ≫ j.left ∧
      Set.range J.left = η.fromNormalization ⁻¹' Set.range j.left ∧
      Spec.map (CommRingCat.ofHom (normalizedChart F).subtype) ≫ J.left = η.toNormalization := by
  letI := ((StageTwo.integralCoeff F).comp (algebraMap ℂ A)).toAlgebra
  let U : Over (Spec ↧ℂ) :=
    Over.mk (pullback.snd η.fromNormalization j.left ≫ ComplexPoint.affineSpecStructureMap A)
  let n : U ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A) :=
    Over.homMk (pullback.snd η.fromNormalization j.left) rfl
  let i : U ⟶ s2b_normalizationOver X η :=
    Over.homMk (pullback.fst η.fromNormalization j.left) (by
      change pullback.fst η.fromNormalization j.left ≫ (η.fromNormalization ≫ X.hom) = _
      rw [← Category.assoc, pullback.condition, Category.assoc, j.w]
      rfl)
  obtain ⟨E, hE, hb⟩ := affine_normalization_restriction η j.left F hF
  have hS : Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff F)) ≫
      ComplexPoint.affineSpecStructureMap A = ComplexPoint.affineSpecStructureMap (normalizedChart F) := by
    change _ = Spec.map (CommRingCat.ofHom (algebraMap ℂ A) ≫
      CommRingCat.ofHom (StageTwo.integralCoeff F))
    exact (Spec.map_comp _ _).symm
  have hEO : E.hom ≫ ComplexPoint.affineSpecStructureMap (normalizedChart F) = U.hom := by
    rw [← hS, ← Category.assoc, hb]
    rfl
  let EO : U ≅ Over.mk (ComplexPoint.affineSpecStructureMap (normalizedChart F)) := Over.isoMk E hEO
  let J := EO.inv ≫ i
  have hsurj : Function.Surjective E.inv := by
    intro x
    exact ⟨E.hom x, congrArg (fun f : U.left ⟶ U.left => f x) E.hom_inv_id⟩
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · change IsOpenImmersion (E.inv ≫ pullback.fst η.fromNormalization j.left)
    infer_instance
  · change E.inv ≫ pullback.fst η.fromNormalization j.left ≫ η.fromNormalization = _
    rw [pullback.condition]
    rw [← hb]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · change Set.range ((pullback.fst η.fromNormalization j.left) ∘ E.inv) = _
    rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
    exact IsOpenImmersion.range_pullbackFst j.left η.fromNormalization
  · change Spec.map (CommRingCat.ofHom (normalizedChart F).subtype) ≫
      E.inv ≫ pullback.fst η.fromNormalization j.left = _
    rw [← hE]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simp only [StageThree.restrictedFieldPoint, pullback.lift_fst]

end AlgebraicGeometry.RamifiedNormalization.StageFour
