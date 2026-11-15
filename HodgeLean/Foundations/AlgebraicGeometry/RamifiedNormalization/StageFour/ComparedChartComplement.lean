import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartImageComplement
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialTransformSupport

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- In the retained scheme, the first compared chart is exactly the original affine neighbourhood minus the second transform support. -/
theorem compared_chart_image_complement
    {X B : Scheme.{0}} (p : X ⟶ B) (U : B.affineOpens)
    (I J : B.IdealSheafData) (u v : Γ(B, U))
    (hu : I.ideal U = Ideal.span {u}) (hv : J.ideal U = Ideal.span {v})
    (hureg : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hvreg : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v))
    (M : Scheme.{0}) (π : M ⟶ Spec Γ(B, U))
    (e : (p ⁻¹ᵁ U.1).toScheme ≅ M)
    (he : e.hom ≫ π ≫ U.2.fromSpec = (p ⁻¹ᵁ U.1).ι ≫ p)
    (j₁ : Spec ↧(RegularPairChart.ring u v) ⟶ M)
    (j₂ : Spec ↧(RegularPairChart.ring v u) ⟶ M)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hj₁ : j₁ ≫ π = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)))
    (hj₂ : j₂ ≫ π = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff v u)))
    (hcover : ∀ y : M, (∃ a, j₁ a = y) ∨ ∃ a, j₂ a = y)
    (hintersection : ∀ y : Spec ↧(RegularPairChart.ring v u),
      (∃ a, j₁ a = j₂ y) ↔ RegularPairChart.ratio v u ∉ y.asIdeal) :
    Set.range (j₁ ≫ e.inv ≫ (p ⁻¹ᵁ U.1).ι) =
      (p ⁻¹ᵁ U.1 : Set X) \ (s2c_strictTransform p J (I ⊔ J)).support := by
  let k := e.inv ≫ (p ⁻¹ᵁ U.1).ι
  have hk : k ≫ p = π ≫ U.2.fromSpec := by
    dsimp only [k]
    rw [Category.assoc, ← he]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h₁ : (j₁ ≫ k) ≫ p =
      Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫ U.2.fromSpec := by
    rw [Category.assoc, hk, ← Category.assoc, hj₁]
  have h₂ : (j₂ ≫ k) ≫ p =
      Spec.map (CommRingCat.ofHom (RegularPairChart.coeff v u)) ≫ U.2.fromSpec := by
    rw [Category.assoc, hk, ← Category.assoc, hj₂]
  haveI : IsOpenImmersion k := by dsimp [k]; infer_instance
  have hD₁ := (binomial_chart_transform_support p U u v I J hu hv hvreg (j₁ ≫ k) h₁).2
  have hD₂ := (binomial_chart_transform_support p U v u J I hv hu hureg (j₂ ≫ k) h₂).1
  rw [sup_comm J I] at hD₂
  let D : Set M := k ⁻¹' (s2c_strictTransform p J (I ⊔ J)).support
  have hD₁' : j₁ ⁻¹' D = ∅ := hD₁
  have hD₂' : j₂ ⁻¹' D = PrimeSpectrum.zeroLocus {RegularPairChart.ratio v u} := hD₂
  have hrange := binomial_chart_image_complement u v M j₁ j₂ hcover hintersection D hD₁' hD₂'
  have hksurj : Function.Surjective e.inv := by
    intro z
    exact ⟨e.hom z, congrArg (fun f : (p ⁻¹ᵁ U.1).toScheme ⟶
      (p ⁻¹ᵁ U.1).toScheme => f z) e.hom_inv_id⟩
  have hrangek : Set.range k = (p ⁻¹ᵁ U.1 : Set X) := by
    change Set.range ((p ⁻¹ᵁ U.1).ι ∘ e.inv) = _
    rw [Set.range_comp, hksurj.range_eq, Set.image_univ, Scheme.Opens.range_ι]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hrangek]
      exact ⟨j₁ a, rfl⟩
    · have hnot : j₁ a ∉ D := by
        rw [← Set.mem_compl_iff, ← hrange]
        exact ⟨a, rfl⟩
      exact hnot
  · rintro ⟨hx, hn⟩
    obtain ⟨y, rfl⟩ := hrangek.symm ▸ hx
    have hy : y ∈ Set.range j₁ := by
      rw [hrange]
      exact hn
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, rfl⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
