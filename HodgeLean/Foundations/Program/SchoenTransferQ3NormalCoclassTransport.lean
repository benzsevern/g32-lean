import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! Exact pullback of chart-normal coclasses under actual normal-coordinate agreement. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- An actual map of supported neighbourhood pairs retaining the normal
coordinates pulls back the specified normal coclass with coefficient one. -/
theorem s4_q3_normal_coclass_pullback
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin c → ℂ)))
    (S : Set M) (T : Set N)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ d.source, y ∈ T ↔ (d y).2 = 0)
    (V : Set M) (W : Set N) (hV : V ⊆ e.source) (hW : W ⊆ d.source)
    (φ : neighborhoodSupportComplementPair V S ⟶ neighborhoodSupportComplementPair W T)
    (hnormal : ∀ y : V, (d (TopPair.Hom.fst φ y).1).2 = (e y.1).2) :
    relativeCohomologyMap ℚ (2 * c) φ
      (chartNormalProjectionCoclass F c d T hT W hW) =
        chartNormalProjectionCoclass E c e S hS V hV := by
  have hcomp : φ ≫ chartNormalProjectionPair F c d T hT W hW =
      chartNormalProjectionPair E c e S hS V hV := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      apply Subtype.ext
      change (d (TopPair.Hom.snd φ y).1.1).2 = (e y.1.1).2
      have hw : (TopPair.Hom.snd φ y).1 = TopPair.Hom.fst φ y.1 :=
        TopPair.Hom.w_apply φ y
      rw [hw]
      exact hnormal y.1
    · ext y
      exact hnormal y
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomp]

end HodgeLean.Foundations.Program
