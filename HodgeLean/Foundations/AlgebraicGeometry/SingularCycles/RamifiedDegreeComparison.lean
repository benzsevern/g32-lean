import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeNeighborhoodOrientation
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeCharts

/-! # Comparing centered coordinate degree with the actual isolated pair map

The coordinate calculation determines the image of the prescribed source
orientation and retains the specified target chart orientation.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem degree_of_centered_chart_expression
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [T1Space M]
    (f : TopCat.of M ⟶ TopCat.of N) (d : ℕ)
    (eX : OpenPartialHomeomorph M (Fin d → ℂ))
    (eZ : OpenPartialHomeomorph N (Fin d → ℂ))
    (x : M) (hx : x ∈ eX.source) (hz : f x ∈ eZ.source)
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U)
    (hiso : ∀ y ∈ U, f y = f x → y = x)
    (V : Set (Fin d → ℂ)) (hV : ∀ v ∈ V, v + eX x ∈ eX.target)
    (hsrc : ∀ v ∈ V, eX.symm (v + eX x) ∈ U)
    (hZ : ∀ v ∈ V, f (eX.symm (v + eX x)) ∈ eZ.source)
    (hc : ContinuousOn (centeredPointChartMap d f eX eZ x) V)
    (hzero : ∀ v ∈ V, centeredPointChartMap d f eX eZ x v = 0 → v = 0)
    (z : RelativeHomology ℚ (neighborhoodPointComplementPair V 0) (2 * d))
    (hzcoord : relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap V 0) z =
      standardComplexLocalClass ℚ d)
    (a : ℚ)
    (hdegree : relativeHomologyMap ℚ (2 * d)
      (a3b4_supportPairMap
        (TopCat.ofHom ⟨fun v : V => centeredPointChartMap d f eX eZ x v.1, hc.domRestrict⟩)
        {v : V | v.1 = 0} ({0} : Set (Fin d → ℂ)) (fun v hv => hzero v.1 v.2 hv)) z =
      a • standardComplexLocalClass ℚ d) :
    relativeHomologyMap ℚ (2 * d) (isolatedPairMap f U x hiso)
      (neighborhoodOrientation d eX x hx U hU hxU) = a • localClassOfChart d eZ (f x) hz := by
  let E := Fin d → ℂ
  let g := centeredPointChartMap d f eX eZ x
  let P := centeredChartNeighborhoodPairMap d eX x V hV U hsrc
  let F := a3b4_supportPairMap
    (TopCat.ofHom ⟨fun v : V => g v.1, hc.domRestrict⟩)
    {v : V | v.1 = 0} ({0} : Set E) (fun v hv => hzero v.1 v.2 hv)
  have htarget (v : V) : g v.1 + eZ (f x) ∈ eZ.target := by
    change eZ (f (eX.symm (v.1 + eX x))) - eZ (f x) + eZ (f x) ∈ eZ.target
    rw [sub_add_cancel]
    exact eZ.map_source (hZ v.1 v.2)
  have hmiss (v : {v : V | v.1 ≠ (0 : E)}) : g v.1.1 + eZ (f x) ≠ eZ (f x) := by
    intro h
    apply v.2
    apply hzero v.1.1 v.1.2
    exact add_right_cancel (h.trans (zero_add (eZ (f x))).symm)
  let Q : neighborhoodPointComplementPair V 0 ⟶
      neighborhoodPointComplementPair eZ.target (eZ (f x)) :=
    TopPair.ofHom
      (TopCat.ofHom ⟨fun v => ⟨g v.1 + eZ (f x), htarget v⟩,
        (hc.domRestrict.add continuous_const).subtype_mk htarget⟩)
      (TopCat.ofHom ⟨fun v => ⟨⟨g v.1.1 + eZ (f x), htarget v.1⟩, hmiss v⟩,
        (((hc.domRestrict.comp continuous_subtype_val).add continuous_const).subtype_mk
          (fun v => htarget v.1)).subtype_mk hmiss⟩)
      (by ext v; rfl)
  have htrans : Q ≫ neighborhoodPointComplementPairMap eZ.target (eZ (f x)) =
      F ≫ translationPointComplementPairMap E (eZ (f x)) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext v <;> rfl
  have hQdegree : relativeHomologyMap ℚ (2 * d)
      (neighborhoodPointComplementPairMap eZ.target (eZ (f x)))
      (relativeHomologyMap ℚ (2 * d) Q z) =
      a • HodgeLean.RealDefs.translatedStandardComplexLocalClass d (eZ (f x)) := by
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, htrans,
      relativeHomologyMap_comp, LinearMap.comp_apply, hdegree, map_smul]
    rfl
  have hfactor : P ≫ isolatedPairMap f U x hiso =
      Q ≫ chartTargetInverseAtSourcePairMap d eZ (f x) := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext v
      apply Subtype.ext
      change f (eX.symm (v.1.1 + eX x)) = eZ.symm (g v.1.1 + eZ (f x))
      dsimp only [g, centeredPointChartMap]
      rw [sub_add_cancel, eZ.left_inv (hZ v.1.1 v.1.2)]
    · ext v
      change f (eX.symm (v.1 + eX x)) = eZ.symm (g v.1 + eZ (f x))
      dsimp only [g, centeredPointChartMap]
      rw [sub_add_cancel, eZ.left_inv (hZ v.1 v.2)]
  have hP := centered_chart_neighborhood_generator d eX x hx V hV U hsrc hU hxU z hzcoord
  rw [← hP]
  change ((relativeHomologyMap ℚ (2 * d) (isolatedPairMap f U x hiso)).comp
    (relativeHomologyMap ℚ (2 * d) P)) z = _
  rw [← relativeHomologyMap_comp, hfactor, relativeHomologyMap_comp, LinearMap.comp_apply]
  exact chart_inverse_on_coordinate_generator d eZ (f x) hz
    (relativeHomologyMap ℚ (2 * d) Q z) a hQdegree

end AlgebraicGeometry.SingularCycles
