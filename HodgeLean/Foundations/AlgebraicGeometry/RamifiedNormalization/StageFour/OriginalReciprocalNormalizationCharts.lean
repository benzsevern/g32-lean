import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalRegularPairNormalizationChart
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartReverseImageOverlap

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Both actual reciprocal chart overlaps retain the original integral binomial generator and etale ratio. -/
theorem original_regular_pair_reciprocal_normalization_charts
    (B X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (p : X ⟶ B) (I J : B.left.IdealSheafData)
    (hcartier : ∀ z : X.left, ∃ V : X.left.affineOpens, z ∈ V.1 ∧
      Nonempty ((((I ⊔ J).comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ z : T.left, ∃ V : T.left.affineOpens, z ∈ V.1 ∧
        Nonempty ((((I ⊔ J).comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.left.affineOpens) (u v : Γ(B.left, U))
    (hu : I.ideal U = Ideal.span {u}) (hv : J.ideal U = Ideal.span {v})
    (hvreg : IsRegular v) (hureg : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hureg' : IsRegular u) (hvreg' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v))
    {L : Type} [Field L] (η : Spec ↧L ⟶ X.left)
    [IsDominant η] [QuasiCompact η] [QuasiSeparated η]
    (φ : Γ(B.left, U) →+* L)
    (hηbase : η ≫ p.left = Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec)
    (m α : ℕ) (hm : 0 < m) (hα : α ≤ m)
    (ε : Γ(B.left, U)ˣ) (t : L) (hu0 : φ u ≠ 0) (hv0 : φ v ≠ 0) (ht : t ≠ 0)
    (htgen : Subfield.closure (Set.range φ ∪ {t}) = ⊤)
    (hteq : t ^ m = φ ε * φ u ^ α * φ v ^ (m - α))
    (N : ℕ) (z : Fin N → Γ(B.left, U)) (a₀ a₁ : Fin N)
    (ha : a₀ ≠ a₁) (hza : u = z a₀) (hzb : v = z a₁)
    (hzet : (MvPolynomial.eval₂Hom (B.hom.appLE ⊤ U.1 le_top).hom z).Etale) :
      ∃ (M : Scheme) (π : M ⟶ Spec Γ(B.left, U))
        (eM : (p.left ⁻¹ᵁ U.1).toScheme ≅ M)
        (j₁ : Spec ↧(RegularPairChart.ring u v) ⟶ M)
        (j₂ : Spec ↧(RegularPairChart.ring v u) ⟶ M),
        IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
        eM.hom ≫ π ≫ U.2.fromSpec = (p.left ⁻¹ᵁ U.1).ι ≫ p.left ∧
        j₁ ≫ π = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ∧
        j₂ ≫ π = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff v u)) ∧
        (∀ y : M, (∃ a, j₁ a = y) ∨ ∃ a, j₂ a = y) ∧
        (∀ y : Spec ↧(RegularPairChart.ring v u),
          (∃ a, j₁ a = j₂ y) ↔ RegularPairChart.ratio v u ∉ y.asIdeal) ∧
        (∀ x : Spec ↧(RegularPairChart.ring u v),
          (∃ a, j₂ a = j₁ x) ↔ RegularPairChart.ratio u v ∉ x.asIdeal) ∧
      ∃ (j : Spec ↧(RegularPairChart.ring u v) ⟶ X.left)
        (F : RegularPairChart.ring u v →+* L),
        j = j₁ ≫ eM.inv ≫ (p.left ⁻¹ᵁ U.1).ι ∧
        IsOpenImmersion j ∧ Function.Injective F ∧
        j ≫ p.left = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫ U.2.fromSpec ∧
        F.comp (RegularPairChart.coeff u v) = φ ∧
        F (RegularPairChart.ratio u v) = φ u / φ v ∧
        φ u ≠ 0 ∧ φ v ≠ 0 ∧ t ≠ 0 ∧
        ∃ hFj : Spec.map (CommRingCat.ofHom F) ≫ j = η,
        ∃ (E : pullback η.fromNormalization j ≅ Spec ↧(normalizedChart F))
          (w : normalizedChart F),
          StageThree.restrictedFieldPoint η j (Spec.map (CommRingCat.ofHom F)) hFj ≫ E.hom =
            Spec.map (CommRingCat.ofHom (normalizedChart F).subtype) ∧
          E.hom ≫ Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff F)) =
            pullback.snd η.fromNormalization j ∧
          (w : L) = dividedGenerator t (φ v) ∧
          w ^ m = StageTwo.integralCoeff F
            (RegularPairChart.coeff u v ε * RegularPairChart.ratio u v ^ α) ∧
          Subfield.closure (Set.range F ∪ {(w : L)}) = ⊤ ∧
          ∃ (z : Fin N → RegularPairChart.ring u v) (a₀ a₁ : Fin N),
            a₀ ≠ a₁ ∧ z a₀ = RegularPairChart.ratio u v ∧
            z a₁ = RegularPairChart.coeff u v v ∧
            (MvPolynomial.eval₂Hom
              ((RegularPairChart.coeff u v).comp (B.hom.appLE ⊤ U.1 le_top).hom) z).Etale := by
  have hI : (I ⊔
      J).ideal U = Ideal.span {u, v} := by
    change (I).ideal U ⊔
      (J).ideal U = _
    rw [hu, hv, ← Ideal.span_union, Set.singleton_union]
  obtain ⟨M, j₁, j₂, π, hj₁, hj₂, hcover, hπ₁, hπ₂, htransition, hinter⟩ :=
    binomial_model_chart_intersection u v
  haveI : IsOpenImmersion j₁ := hj₁
  haveI : IsOpenImmersion j₂ := hj₂
  have hlift := s2v_l1b_model_source_lift u v M j₁ j₂ π hcover hπ₁ hπ₂ htransition
  have hoverlap := binomial_chart_image_overlap u v M j₁ j₂ hinter
  have hoverlap' := binomial_chart_reverse_image_overlap u v M j₁ j₂ hinter
  obtain ⟨eM, heM, _⟩ := s2v_l1b_charts_blowup_comparison
    B X p
    (I ⊔ J)
    hcartier hblowup U u v hI hvreg hureg hureg' hvreg'
    M j₁ j₂ π ⟨hj₁, hj₂, hcover, hπ₁, hπ₂, hlift⟩
  let j := j₁ ≫ eM.inv ≫ (p.left ⁻¹ᵁ U.1).ι
  haveI : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hj : j ≫ p.left = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫ U.2.fromSpec := by
    dsimp only [j]
    rw [Category.assoc, Category.assoc, ← heM]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [hπ₁]
  letI : Nontrivial (RegularPairChart.ring u v) := (chartMap φ u v hv0).domain_nontrivial
  obtain ⟨F, hFinj, hFc, hFr, hFj, E, hE, hEb⟩ := original_affine_chart_field u v
    η p.left U.2.fromSpec j hj φ hηbase hv0
  obtain ⟨wN, hwN, heqN, _⟩ := divided_chart_integral_element φ (RegularPairChart.coeff u v) F hFc
    m α hm hα
    ε u v t hu0 hv0 hteq (RegularPairChart.ratio u v) (RegularPairChart.chart_relation u v)
  have hgenN : Subfield.closure (Set.range F ∪ {(wN : L)}) = ⊤ := by
    rw [hwN]
    exact divided_generator_field_generation φ F (RegularPairChart.coeff u v) hFc t v hv0 htgen
  obtain ⟨zA, hzA, hz₀, hz₁⟩ : ∃ zA : Fin N → RegularPairChart.ring u v,
      (MvPolynomial.eval₂Hom
        ((RegularPairChart.coeff u v).comp (B.hom.appLE ⊤ U.1 le_top).hom) zA).Etale ∧
      zA a₀ = RegularPairChart.ratio u v ∧ zA a₁ = RegularPairChart.coeff u v v := by
    subst u
    subst v
    obtain ⟨zA, hzA, hz₀, hz₁, _⟩ := etale_binomial_ratio_coordinates
      (B.hom.appLE ⊤ U.1 le_top).hom z hzet a₀ a₁ ha hvreg hureg
    exact ⟨zA, hzA, hz₀, hz₁⟩
  refine ⟨M, π, eM, j₁, j₂, hj₁, hj₂, heM, hπ₁, hπ₂, hcover, hoverlap, hoverlap',
    j, F, rfl, inferInstance, hFinj, hj, hFc, hFr, hu0, hv0, ht,
    hFj, E, wN, hE, hEb, hwN, heqN, hgenN, ?_⟩
  exact ⟨zA, a₀, a₁, ha, hz₀, hz₁, hzA⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
