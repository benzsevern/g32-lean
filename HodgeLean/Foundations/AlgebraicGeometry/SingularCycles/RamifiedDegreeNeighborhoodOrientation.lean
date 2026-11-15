import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeCoordinateOrientation

/-! # Centered parametrizations inside prescribed neighbourhoods

A centered coordinate generator maps to the inverse-excision orientation
of any ambient neighbourhood containing the parametrization.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

def centeredChartNeighborhoodPairMap
    {M : Type} [TopologicalSpace M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (V : Set (Fin d → ℂ)) (hV : ∀ v ∈ V, v + e x ∈ e.target)
    (U : Set M) (hsrc : ∀ v ∈ V, e.symm (v + e x) ∈ U) :
    neighborhoodPointComplementPair V 0 ⟶ neighborhoodPointComplementPair U x :=
  let F := centeredChartPairMap d e x V hV
  TopPair.ofHom
    (TopCat.ofHom ⟨fun v => ⟨TopPair.Hom.fst F v, hsrc v.1 v.2⟩, (TopPair.Hom.fst F).hom.continuous.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun v => ⟨⟨(TopPair.Hom.snd F v).1, hsrc v.1.1 v.1.2⟩,
      (TopPair.Hom.snd F v).2⟩,
      ((continuous_subtype_val.comp (TopPair.Hom.snd F).hom.continuous).subtype_mk _).subtype_mk _⟩)
    (by ext v; rfl)

theorem centered_chart_neighborhood_generator
    {M : Type} [TopologicalSpace M] [T1Space M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (V : Set (Fin d → ℂ)) (hV : ∀ v ∈ V, v + e x ∈ e.target)
    (U : Set M) (hsrc : ∀ v ∈ V, e.symm (v + e x) ∈ U)
    (hU : IsOpen U) (hxU : x ∈ U)
    (z : RelativeHomology ℚ (neighborhoodPointComplementPair V 0) (2 * d))
    (hz : relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap V 0) z =
      standardComplexLocalClass ℚ d) :
    relativeHomologyMap ℚ (2 * d) (centeredChartNeighborhoodPairMap d e x V hV U hsrc) z =
      neighborhoodOrientation d e x hx U hU hxU := by
  apply (neighborhoodPointComplement_relativeHomologyMap_bijective U x hU hxU (2 * d)).1
  have hcomp : centeredChartNeighborhoodPairMap d e x V hV U hsrc ≫
      neighborhoodPointComplementPairMap U x = centeredChartPairMap d e x V hV := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext v <;> rfl
  change ((relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap U x)).comp
    (relativeHomologyMap ℚ (2 * d) (centeredChartNeighborhoodPairMap d e x V hV U hsrc))) z = _
  rw [← relativeHomologyMap_comp, hcomp, centered_chart_generator d e x hx V hV z hz]
  exact (ConcreteCategory.congr_hom
    (Iso.inv_hom_id (neighborhoodPointComplementRelativeHomologyIso U x hU hxU (2 * d)))
    (localClassOfChart d e x hx)).symm

end AlgebraicGeometry.SingularCycles
