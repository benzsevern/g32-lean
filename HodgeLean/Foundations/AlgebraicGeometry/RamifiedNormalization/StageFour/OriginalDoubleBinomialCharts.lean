import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalReciprocalNormalizationCharts

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Both actual original chart embeddings retain their integral binomial generators, complementary powers, and etale ratio coordinates in the same original field. -/
theorem original_double_binomial_charts
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
              ((RegularPairChart.coeff u v).comp (B.hom.appLE ⊤ U.1 le_top).hom) z).Etale ∧
          ∃ (j' : Spec ↧(RegularPairChart.ring v u) ⟶ X.left)
            (G : RegularPairChart.ring v u →+* L),
            j' = j₂ ≫ eM.inv ≫ (p.left ⁻¹ᵁ U.1).ι ∧
            IsOpenImmersion j' ∧ Function.Injective G ∧
            j' ≫ p.left = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff v u)) ≫ U.2.fromSpec ∧
            G.comp (RegularPairChart.coeff v u) = φ ∧
            G (RegularPairChart.ratio v u) = φ v / φ u ∧
            Spec.map (CommRingCat.ofHom G) ≫ j' = η ∧
            ∃ w' : normalizedChart G,
              (w' : L) = dividedGenerator t (φ u) ∧
              w' ^ m = StageTwo.integralCoeff G
                (RegularPairChart.coeff v u ε * RegularPairChart.ratio v u ^ (m - α)) ∧
              Subfield.closure (Set.range G ∪ {(w' : L)}) = ⊤ ∧
              ∃ (z' : Fin N → RegularPairChart.ring v u) (a₀' a₁' : Fin N),
                a₀' ≠ a₁' ∧ z' a₀' = RegularPairChart.ratio v u ∧
                z' a₁' = RegularPairChart.coeff v u u ∧
                (MvPolynomial.eval₂Hom
                  ((RegularPairChart.coeff v u).comp (B.hom.appLE ⊤ U.1 le_top).hom) z').Etale := by
  obtain ⟨M, π, eM, j₁, j₂, hj₁, hj₂, heM, hπ₁, hπ₂, hcover, hoverlap, hoverlap',
    j, F, hjdef, hjopen, hFinj, hjbase, hFc, hFr, _, _, _, hFj, E, wN,
    hE, hEb, hwN, heqN, hgenN, zA, b₀, b₁, hb, hzb₀, hzb₁, hzA⟩ :=
    original_regular_pair_reciprocal_normalization_charts B X p I J hcartier hblowup U u v
      hu hv hvreg hureg hureg' hvreg' η φ hηbase m α hm hα ε t hu0 hv0 ht htgen hteq
      N z a₀ a₁ ha hza hzb hzet
  haveI : IsOpenImmersion j₂ := hj₂
  let j' := j₂ ≫ eM.inv ≫ (p.left ⁻¹ᵁ U.1).ι
  haveI : IsOpenImmersion j' := by dsimp [j']; infer_instance
  have hMb : (eM.inv ≫ (p.left ⁻¹ᵁ U.1).ι) ≫ p.left = π ≫ U.2.fromSpec := by
    rw [Category.assoc, ← heM]
    simp [← Category.assoc]
  have hj'base : j' ≫ p.left = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff v u)) ≫ U.2.fromSpec := by
    change (j₂ ≫ (eM.inv ≫ (p.left ⁻¹ᵁ U.1).ι)) ≫ p.left = _
    rw [Category.assoc, hMb, ← Category.assoc, hπ₂]
  haveI : Nontrivial (RegularPairChart.ring v u) := (chartMap φ v u hu0).domain_nontrivial
  obtain ⟨G, hGinj, hGc, hGr, hGj, EG, hEG, hEGb⟩ := original_affine_chart_field v u
    η p.left U.2.fromSpec j' hj'base φ hηbase hu0
  have hteq' : t ^ m = φ ε * φ v ^ (m - α) * φ u ^ (m - (m - α)) := by
    rw [Nat.sub_sub_self hα, hteq]
    ring
  obtain ⟨wB, hwB, heqB, _⟩ := divided_chart_integral_element φ (RegularPairChart.coeff v u) G hGc
    m (m - α) hm (Nat.sub_le _ _) ε v u t hv0 hu0 hteq'
    (RegularPairChart.ratio v u) (RegularPairChart.chart_relation v u)
  have hgenB : Subfield.closure (Set.range G ∪ {(wB : L)}) = ⊤ := by
    rw [hwB]
    exact divided_generator_field_generation φ G (RegularPairChart.coeff v u) hGc t u hu0 htgen
  have hcoordB := etale_binomial_ratio_coordinates (B.hom.appLE ⊤ U.1 le_top).hom z hzet
    a₁ a₀ ha.symm (by simpa only [hza] using hureg') (by
      have hh := hvreg'
      rw [hza, hzb] at hh
      exact hh)
  rw [← hza, ← hzb] at hcoordB
  obtain ⟨zB, hzB, hzb₂, hzb₃, _⟩ := hcoordB
  exact ⟨M, π, eM, j₁, j₂, hj₁, hj₂, heM, hπ₁, hπ₂, hcover, hoverlap, hoverlap',
    j, F, hjdef, hjopen, hFinj, hjbase, hFc, hFr, hu0, hv0, ht, hFj, E, wN,
    hE, hEb, hwN, heqN, hgenN, zA, b₀, b₁, hb, hzb₀, hzb₁, hzA,
    j', G, rfl, inferInstance, hGinj, hj'base, hGc, hGr, hGj,
    wB, hwB, heqB, hgenB, zB, a₁, a₀, ha.symm, hzb₂, hzb₃, hzB⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
