import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ComplexNeighborhoodOrientation

/-! Exact local-class transport through an open embedding of chart domains. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (j : M → N) (hj : IsOpenEmbedding j) (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)

theorem chartRadius_lift_openEmbedding :
    chartRadius d (e.lift_openEmbedding hj) (j x) ⟨x, hx, rfl⟩ =
      chartRadius d e x hx := by
  unfold chartRadius
  simp only [OpenPartialHomeomorph.lift_openEmbedding_target,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

theorem chartModelEmbedding_lift_openEmbedding (z : Fin d → ℂ) :
    chartModelEmbedding d (e.lift_openEmbedding hj) (j x) ⟨x, hx, rfl⟩ z =
      j (chartModelEmbedding d e x hx z) := by
  simp only [chartModelEmbedding, OpenPartialHomeomorph.trans_apply]
  rw [chartRadius_lift_openEmbedding j hj d e x hx]
  simp only [OpenPartialHomeomorph.lift_openEmbedding_apply,
    OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply]

theorem chartModelEmbeddingPair_lift_openEmbedding :
    chartModelEmbeddingPair d e x hx ≫
      imagePointPairMap (TopCat.ofHom ⟨j, hj.continuous⟩) hj.injective x =
    chartModelEmbeddingPair d (e.lift_openEmbedding hj) (j x) ⟨x, hx, rfl⟩ := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    exact (chartModelEmbedding_lift_openEmbedding j hj d e x hx _).symm
  · ext z
    exact (chartModelEmbedding_lift_openEmbedding j hj d e x hx _).symm

theorem localClassOfChart_lift_openEmbedding :
    relativeHomologyMap ℚ (2 * d)
      (imagePointPairMap (TopCat.ofHom ⟨j, hj.continuous⟩) hj.injective x)
      (localClassOfChart d e x hx) =
    localClassOfChart d (e.lift_openEmbedding hj) (j x) ⟨x, hx, rfl⟩ := by
  rw [localClassOfChart, localClassOfChart, ← LinearMap.comp_apply,
    ← relativeHomologyMap_comp, chartModelEmbeddingPair_lift_openEmbedding j hj d e x hx]
  rfl

#print axioms localClassOfChart_lift_openEmbedding
end HodgeLean.Foundations.QuotientDuality
