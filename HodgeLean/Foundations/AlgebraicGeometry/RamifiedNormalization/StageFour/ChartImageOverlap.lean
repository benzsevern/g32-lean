import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialChartGluing

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- On the second binomial chart, membership in the first chart is precisely invertibility of the ratio. -/
theorem binomial_chart_image_overlap
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
    (y : Spec ↧(s2v_L1bChart v u)) :
    (∃ x, j₁ x = j₂ y) ↔ RegularPairChart.ratio v u ∉ y.asIdeal := by
  let e := Classical.choose (s2v_l1b_overlap_equiv u v)
  let eS := Scheme.Spec.mapIso e.toCommRingCatIso.op
  let l₂ := algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u)
  let g := eS.inv ≫ Spec.map (CommRingCat.ofHom l₂)
  have hgsurj : Function.Surjective eS.inv := by
    intro z
    refine ⟨eS.hom z, ?_⟩
    exact congrArg (fun h : Spec ↧(s2v_L1bOverlap v u) ⟶
      Spec ↧(s2v_L1bOverlap v u) => h z) eS.hom_inv_id
  have hrange : Set.range g = Set.range (Spec.map (CommRingCat.ofHom l₂)) := by
    change Set.range ((Spec.map (CommRingCat.ofHom l₂)) ∘ eS.inv) = _
    rw [Set.range_comp, hgsurj.range_eq, Set.image_univ]
  have hrangeL := PrimeSpectrum.localization_away_comap_range
    (s2v_L1bOverlap v u) (RegularPairChart.ratio v u)
  have he : (∃ x, j₁ x = j₂ y) ↔ ∃ z, g z = y := by
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz₁, hz₂⟩ := (hintersection x y).mp hx
      exact ⟨z, hz₂⟩
    · rintro ⟨z, hz⟩
      refine ⟨_, (hintersection _ y).mpr ⟨z, rfl, hz⟩⟩
  rw [he]
  change y ∈ Set.range g ↔ _
  rw [hrange]
  change y ∈ Set.range (PrimeSpectrum.comap l₂) ↔ _
  rw [hrangeL]
  rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
