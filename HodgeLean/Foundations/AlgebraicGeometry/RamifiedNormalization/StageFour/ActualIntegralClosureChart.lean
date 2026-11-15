import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ActualNormalizationChart
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosurePresentation

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual open normalization chart retains the original integral-closure coefficient algebra and its exact scheme image. -/
theorem actual_integral_closure_chart
    {A L : Type} [CommRing A] [Algebra ℂ A] [Field L] [Algebra A L]
    (X : Over (Spec ↧ℂ)) (η : Spec ↧L ⟶ X.left)
    [QuasiCompact η] [QuasiSeparated η]
    (j : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X) [IsOpenImmersion j.left]
    (hF : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ j.left = η) :
    ∃ (U : Over (Spec ↧ℂ)) (i : U ⟶ s2b_normalizationOver X η)
      (n : U ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A))
      (E : U.left ≅ Spec ↧(integralClosure A L)),
      IsOpenImmersion i.left ∧ n ≫ j = i ≫ s2b_normalizationMap X η ∧
      E.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) = n.left ∧
      Set.range i.left = η.fromNormalization ⁻¹' Set.range j.left := by
  obtain ⟨U, i, n, E, hi, hn, hb, hrange⟩ :=
    actual_normalization_chart X η j (algebraMap A L) hF
  let e := normalizedChartIntegralClosureEquiv (A := A) (L := L)
  let ES := (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm
  refine ⟨U, i, n, E ≪≫ ES, hi, hn, ?_, hrange⟩
  change E.hom ≫ ES.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) = _
  have hES : ES.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) =
      Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff (algebraMap A L))) := by
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    rfl
  rw [hES, hb]

end AlgebraicGeometry.RamifiedNormalization.StageFour
