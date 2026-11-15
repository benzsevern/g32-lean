import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartImageOverlap

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The first actual binomial chart is exactly the complement of the second strict-transform endpoint support. -/
theorem binomial_chart_image_complement
    {R : Type} [CommRing R] (u v : R) (X : Scheme)
    (j₁ : Spec ↧(RegularPairChart.ring u v) ⟶ X)
    (j₂ : Spec ↧(RegularPairChart.ring v u) ⟶ X)
    (hcover : ∀ x : X, (∃ a, j₁ a = x) ∨ ∃ a, j₂ a = x)
    (hintersection : ∀ y : Spec ↧(RegularPairChart.ring v u),
      (∃ a, j₁ a = j₂ y) ↔ RegularPairChart.ratio v u ∉ y.asIdeal)
    (D : Set X) (hD₁ : j₁ ⁻¹' D = ∅)
    (hD₂ : j₂ ⁻¹' D = PrimeSpectrum.zeroLocus {RegularPairChart.ratio v u}) :
    Set.range j₁ = Dᶜ := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩ hx
    have ha : a ∈ j₁ ⁻¹' D := hx
    rw [hD₁] at ha
    exact ha
  · intro hx
    rcases hcover x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, ha⟩
    · have hn : RegularPairChart.ratio v u ∉ a.asIdeal := by
        intro hr
        apply hx
        rw [← ha]
        change a ∈ j₂ ⁻¹' D
        rw [hD₂]
        exact Set.singleton_subset_iff.mpr hr
      obtain ⟨q, hq⟩ := (hintersection a).mpr hn
      exact ⟨q, hq.trans ha⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
