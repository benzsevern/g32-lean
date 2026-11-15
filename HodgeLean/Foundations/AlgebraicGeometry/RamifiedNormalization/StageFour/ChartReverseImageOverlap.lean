import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartImageOverlap

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The same original overlap comparison also identifies the second chart image inside the first chart. -/
theorem binomial_chart_reverse_image_overlap
    {R : Type} [CommRing R] (u v : R) (M : Scheme)
    (j₁ : Spec ↧(s2v_L1bChart u v) ⟶ M)
    (j₂ : Spec ↧(s2v_L1bChart v u) ⟶ M)
    (hintersection :
      let ε := Classical.choose (s2v_l1b_overlap_equiv u v)
      ∀ a b, j₁ a = j₂ b ↔ ∃ z : Spec ↧(s2v_L1bOverlap u v),
        Spec.map (CommRingCat.ofHom (algebraMap (s2v_L1bChart u v)
          (s2v_L1bOverlap u v))) z = a ∧
        (Spec.map (CommRingCat.ofHom ε.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (s2v_L1bChart v u)
            (s2v_L1bOverlap v u)))) z = b)
    (x : Spec ↧(s2v_L1bChart u v)) :
    (∃ y, j₂ y = j₁ x) ↔ RegularPairChart.ratio u v ∉ x.asIdeal := by
  let l := algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
  have he : (∃ y, j₂ y = j₁ x) ↔ ∃ z, Spec.map (CommRingCat.ofHom l) z = x := by
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, hz, _⟩ := (hintersection x y).mp hy.symm
      exact ⟨z, hz⟩
    · rintro ⟨z, hz⟩
      refine ⟨_, ((hintersection x _).mpr ⟨z, hz, rfl⟩).symm⟩
  rw [he]
  change x ∈ Set.range (PrimeSpectrum.comap l) ↔ _
  rw [PrimeSpectrum.localization_away_comap_range
    (s2v_L1bOverlap u v) (RegularPairChart.ratio u v)]
  rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
