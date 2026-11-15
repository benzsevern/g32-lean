import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeComparison

/-! # Reading an isolated index in centered charts

An equality on the actual coordinate neighbourhood suffices to transfer
an index calculation to the original isolated point map.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem degree_of_chart_expression
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [T1Space M]
    (f : TopCat.of M ⟶ TopCat.of N) (d : ℕ)
    (eX : OpenPartialHomeomorph M (Fin d → ℂ))
    (eZ : OpenPartialHomeomorph N (Fin d → ℂ))
    (x : M) (hx : x ∈ eX.source) (hz : f x ∈ eZ.source)
    (hx0 : eX x = 0) (hz0 : eZ (f x) = 0)
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U)
    (hiso : ∀ y ∈ U, f y = f x → y = x)
    (V : Set (Fin d → ℂ)) (hVopen : IsOpen V) (h0V : (0 : Fin d → ℂ) ∈ V)
    (hV : V ⊆ eX.target) (hsrc : ∀ v ∈ V, eX.symm v ∈ U)
    (hZ : ∀ v ∈ V, f (eX.symm v) ∈ eZ.source)
    (F : (Fin d → ℂ) → (Fin d → ℂ))
    (hF : ∀ v ∈ V, F v = eZ (f (eX.symm v)))
    (hc : ContinuousOn F V) (hzero : ∀ v ∈ V, F v = 0 → v = 0) (a : ℚ)
    (hdegree : ∀ z : RelativeHomology ℚ (neighborhoodPointComplementPair V 0) (2 * d),
      relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap V 0) z =
        standardComplexLocalClass ℚ d →
      relativeHomologyMap ℚ (2 * d)
        (a3b4_supportPairMap (TopCat.ofHom ⟨fun v : V => F v.1, hc.domRestrict⟩)
          {v : V | v.1 = 0} {0} (fun v hv => hzero v.1 v.2 hv)) z =
        a • standardComplexLocalClass ℚ d) :
    relativeHomologyMap ℚ (2 * d) (isolatedPairMap f U x hiso)
      (neighborhoodOrientation d eX x hx U hU hxU) = a • localClassOfChart d eZ (f x) hz := by
  let G := centeredPointChartMap d f eX eZ x
  have hG : ∀ v ∈ V, G v = F v := by
    intro v hv
    simp only [G, centeredPointChartMap, hx0, hz0, add_zero, sub_zero]
    exact (hF v hv).symm
  have hcG : ContinuousOn G V := hc.congr hG
  have hzG : ∀ v ∈ V, G v = 0 → v = 0 := by
    intro v hv h
    exact hzero v hv ((hG v hv).symm.trans h)
  obtain ⟨z, hzcoord⟩ := neighborhoodPointComplement_relativeHomologyMap_surjective
    V 0 hVopen h0V (2 * d) (standardComplexLocalClass ℚ d)
  apply degree_of_centered_chart_expression f d eX eZ x hx hz U hU hxU hiso V
    (by simpa only [hx0, add_zero] using fun v hv => hV hv)
    (by simpa only [hx0, add_zero] using hsrc)
    (by simpa only [hx0, add_zero] using hZ) hcG hzG z hzcoord a
  have hmaps : a3b4_supportPairMap
      (TopCat.ofHom ⟨fun v : V => G v.1, hcG.domRestrict⟩)
      {v : V | v.1 = 0} ({0} : Set (Fin d → ℂ)) (fun v hv => hzG v.1 v.2 hv) =
      a3b4_supportPairMap (TopCat.ofHom ⟨fun v : V => F v.1, hc.domRestrict⟩)
        {v : V | v.1 = 0} {0} (fun v hv => hzero v.1 v.2 hv) := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext v
      apply Subtype.ext
      exact hG v.1.1 v.1.2
    · ext v
      exact hG v.1 v.2
  rw [hmaps]
  exact hdegree z hzcoord

end AlgebraicGeometry.SingularCycles
