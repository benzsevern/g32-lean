import HodgeLean.Foundations.Program.TorusAlgebraizationB54Naturality

noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G]

set_option backward.isDefEq.respectTransparency false in
theorem b54_chart_evaluation_denominator (q : A →+* ℂ)
    (hq : (HomogeneousIdeal.irrelevant G).toIdeal.map
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) = ⊤)
    {r : A} (hr : r ∈ G 1) (φ : Away G r →+* ℂ)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι G r hr zero_lt_one =
      Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) hq) :
    q r ≠ 0 := by
  intro hz
  have hU : (Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) hq)
      ⁻¹ᵁ Proj.basicOpen G r = ⊥ := by
    rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one hr]
    simp [hz]
  have hm : IsLocalRing.closedPoint ℂ ∈
      (Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) hq)
        ⁻¹ᵁ Proj.basicOpen G r := by
    rw [← hφ]
    change (Proj.awayι G r hr zero_lt_one)
      ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ)) ∈ Proj.basicOpen G r
    rw [← Proj.opensRange_awayι G r hr zero_lt_one]
    exact ⟨_, rfl⟩
  rw [hU] at hm
  exact hm

set_option backward.isDefEq.respectTransparency false in
theorem b54_chart_evaluation_eq (q : A →+* ℂ)
    (hq : (HomogeneousIdeal.irrelevant G).toIdeal.map
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) = ⊤)
    {r : A} (hr : r ∈ G 1) (φ : Away G r →+* ℂ)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι G r hr zero_lt_one =
      Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) hq) :
    φ = b54_awayEvaluation (G := G) q r
      (Ne.isUnit (b54_chart_evaluation_denominator G q hq hr φ hφ)) := by
  have he : Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (b54_awayEvaluation (G := G) q r
        (Ne.isUnit (b54_chart_evaluation_denominator G q hq hr φ hφ)))) := by
    apply (cancel_mono (Proj.awayι G r hr zero_lt_one)).mp
    rw [hφ, b54_fromOfGlobalSections_eq_awayEvaluation q hr zero_lt_one _ hq]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

end HodgeLean.Foundations.Program
