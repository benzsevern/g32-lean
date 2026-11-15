import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalGenerator
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cNeighborhoodOrientation
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory Topology AlgebraicTopology.Singular
variable (R : Type) [CommRing R] {M : Type} [TopologicalSpace M] [T1Space M]
variable (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)

set_option backward.isDefEq.respectTransparency false in
theorem b6m_chartModelEmbedding_relativeHomologyMap_bijective :
    Function.Bijective
      (relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e x hx)) := by
  have htarget : Function.Bijective
      (relativeHomologyMap R (2 * d)
        (standardComplexChartTargetPairIso d e x hx).hom) := by
    exact (ConcreteCategory.isIso_iff_bijective ((relativeHomologyFunctor R (2 * d)).map
      (standardComplexChartTargetPairIso d e x hx).hom)).mp inferInstance
  have hexcision := b6m_point_excision_bijective R
    (chartModelEmbedding d e x hx).target x (chartModelEmbedding d e x hx).open_target
      (chartModelEmbedding_mem_target d e x hx) (2 * d)
  rw [← standardComplexChartTargetPairIso_hom_comp_neighborhoodMap d e x hx,
    relativeHomologyMap_comp]
  exact hexcision.comp htarget

set_option backward.isDefEq.respectTransparency false in
theorem b6m_chartModelEmbedding_relativeHomologyMap_surjective :
    Function.Surjective
      (relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e x hx)) :=
  (b6m_chartModelEmbedding_relativeHomologyMap_bijective R d e x hx).2

set_option backward.isDefEq.respectTransparency false in
theorem b6m_span_localClassOfChart_eq_top (hd : 0 < d) :
    Submodule.span R {b6m_localClassOfChart R d e x hx} = ⊤ := by
  let f := relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e x hx)
  calc
    Submodule.span R {b6m_localClassOfChart R d e x hx} =
        (Submodule.span R {standardComplexLocalClass R d}).map f := by
      rw [Submodule.map_span]
      simp only [Set.image_singleton]
      rfl
    _ = (⊤ : Submodule R _).map f := by
      rw [b6m_span_standardComplexLocalClass_pos R d hd]
    _ = LinearMap.range f := Submodule.map_top f
    _ = ⊤ := LinearMap.range_eq_top.mpr
      (b6m_chartModelEmbedding_relativeHomologyMap_surjective R d e x hx)

theorem b6m_localClassOfChart_one_smul_bijective
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ)) (x : M) (hx : x ∈ e.source) :
    Function.Bijective (fun r : R => r • b6m_localClassOfChart R 1 e x hx) := by
  have h := (b6m_chartModelEmbedding_relativeHomologyMap_bijective R 1 e x hx).comp
    (b6m_standardComplexLocalClass_one_smul_bijective R)
  simpa only [Function.comp_def, map_smul, b6m_localClassOfChart] using h

end HodgeLean.Foundations.Program
