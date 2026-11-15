import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ActualTwoChartMorphisms

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Compatible actual open-chart morphisms over a common base glue over that same base. -/
theorem glue_two_actual_open_charts_over
    {S : Scheme.{0}} (X U V Y : Over S) (jU : U ⟶ X) (jV : V ⟶ X)
    [IsOpenImmersion jU.left] [IsOpenImmersion jV.left]
    (hcover : ∀ x : X.left, (∃ u, jU.left u = x) ∨ ∃ v, jV.left v = x)
    (fU : U ⟶ Y) (fV : V ⟶ Y)
    (hUV : pullback.fst jU.left jV.left ≫ fU.left = pullback.snd jU.left jV.left ≫ fV.left) :
    ∃! f : X ⟶ Y, jU ≫ f = fU ∧ jV ≫ f = fV := by
  obtain ⟨f, hf, hfunique⟩ := glue_two_actual_open_charts X.left U.left V.left Y.left
    jU.left jV.left hcover fU.left fV.left hUV
  have hbase : pullback.fst jU.left jV.left ≫ U.hom = pullback.snd jU.left jV.left ≫ V.hom := by
    rw [← jU.w, ← Category.assoc, pullback.condition, Category.assoc, jV.w]
  obtain ⟨s, hs, hsunique⟩ := glue_two_actual_open_charts X.left U.left V.left S
    jU.left jV.left hcover U.hom V.hom hbase
  have hstruct : f ≫ Y.hom = X.hom := by
    apply (hsunique (f ≫ Y.hom) ?_).trans (hsunique X.hom ⟨jU.w, jV.w⟩).symm
    constructor
    · rw [← Category.assoc, hf.1, fU.w]
    · rw [← Category.assoc, hf.2, fV.w]
  let fO : X ⟶ Y := Over.homMk f hstruct
  refine ⟨fO, ⟨?_, ?_⟩, ?_⟩
  · apply Over.OverMorphism.ext
    exact hf.1
  · apply Over.OverMorphism.ext
    exact hf.2
  · intro g hg
    apply Over.OverMorphism.ext
    apply hfunique g.left
    exact ⟨congrArg (fun k => k.left) hg.1, congrArg (fun k => k.left) hg.2⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
