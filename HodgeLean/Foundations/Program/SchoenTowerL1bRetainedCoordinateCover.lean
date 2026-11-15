import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleChartImage
import HodgeLean.Foundations.Program.SchoenTowerL1bComparisonIso
import HodgeLean.Foundations.Program.SchoenTowerL1bModelDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bFlatRegularPair

/-! Direct model construction of retained coordinate covers.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained blowup of a coordinate pair has two actual affine etale charts
covering the whole inverse image, with explicit pullbacks of every coordinate. -/
theorem s2v_l1b_retained_coordinate_cover
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : X.left, ∃ V : X.left.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.left.affineOpens) {K σ : Type} [CommRing K] [IsDomain K] [DecidableEq σ]
    (c : K →+* Γ(B.left, U)) (z : σ → Γ(B.left, U))
    (het : (MvPolynomial.eval₂Hom c z).Etale) (a b : σ) (hab : a ≠ b)
    (hI : I.ideal U = Ideal.span {z a, z b}) :
    ∃ (V₁ V₂ : X.left.affineOpens)
      (h₁ : V₁.1 ≤ p.left ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p.left ⁻¹ᵁ U.1)
      (w₁ : σ → Γ(X.left, V₁)) (w₂ : σ → Γ(X.left, V₂)),
      V₁.1 ⊔ V₂.1 = p.left ⁻¹ᵁ U.1 ∧
      (MvPolynomial.eval₂Hom ((p.left.appLE U.1 V₁.1 h₁).hom.comp c) w₁).Etale ∧
      (MvPolynomial.eval₂Hom ((p.left.appLE U.1 V₂.1 h₂).hom.comp c) w₂).Etale ∧
      (∀ t, (p.left.appLE U.1 V₁.1 h₁).hom (z t) =
        if t = a then w₁ a * w₁ b else w₁ t) ∧
      (∀ t, (p.left.appLE U.1 V₂.1 h₂).hom (z t) =
        if t = b then w₂ b * w₂ a else w₂ t) := by
  obtain ⟨hb, ha⟩ := s2v_l1b_etale_coordinate_pair c z het a b hab
  obtain ⟨ha', hb'⟩ := s2v_l1b_etale_coordinate_pair c z het b a hab.symm
  obtain ⟨M, j₁, j₂, π, hj₁, hj₂, hcover, hp₁, hp₂, ht⟩ :=
    s2v_l1b_binomial_chart_scheme_transition (z a) (z b)
  letI := hj₁
  letI := hj₂
  let J := I.comap U.2.fromSpec
  have hJ := s2v_l1b_centre_fromSpec I U (z a) (z b) hI
  have hfree := s2v_l1b_given_model_invertible (z a) (z b) hb ha ha' hb' J hJ
    M j₁ j₂ π hcover hp₁ hp₂
  have hM : ∀ (T : Scheme) (g : T ⟶ Spec Γ(B.left, U)),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((J.comap g).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ M, u ≫ π = g := by
    intro T g hg
    apply s2v_l1b_model_source_lift (z a) (z b) M j₁ j₂ π hcover hp₁ hp₂ ht T g
    intro x
    obtain ⟨V, hx, hV⟩ := hg x
    refine ⟨V, hx, ?_⟩
    have heq := s2v_l1b_spectrum_pair_pullback J (z a) (z b) hJ g V
    dsimp only at heq ⊢
    exact heq ▸ hV
  obtain ⟨e, he⟩ := s2v_l1b_restricted_model_iso p.left I hcartier
    (s2v_l1b_blowup_scheme_lift B X p I hblowup) U M π hfree hM
  have heB : e.hom ≫ π ≫ U.2.fromSpec = (p.left ⁻¹ᵁ U.1).ι ≫ p.left := by
    rw [← Category.assoc, he, Category.assoc, IsAffineOpen.fromSpec,
      Iso.hom_inv_id_assoc, morphismRestrict_ι]
  let k₁ := j₁ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι
  let k₂ := j₂ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι
  have hei : e.inv ≫ (p.left ⁻¹ᵁ U.1).ι ≫ p.left = π ≫ U.2.fromSpec := by
    rw [← heB]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hk₁ : k₁ ≫ p.left = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span
        {Polynomial.C (z a) - Polynomial.X * Polynomial.C (z b)})).comp Polynomial.C)) ≫
        U.2.fromSpec := by
    change (j₁ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι) ≫ p.left = _
    rw [Category.assoc, Category.assoc, hei, ← Category.assoc, hp₁]
  have hk₂ : k₂ ≫ p.left = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span
        {Polynomial.C (z b) - Polynomial.X * Polynomial.C (z a)})).comp Polynomial.C)) ≫
        U.2.fromSpec := by
    change (j₂ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι) ≫ p.left = _
    rw [Category.assoc, Category.assoc, hei, ← Category.assoc, hp₂]
  obtain ⟨V₁, h₁, w₁, hV₁, hw₁, hz₁⟩ :=
    s2v_l1b_etale_binomial_chart_image p.left U c z het a b hab k₁ hk₁
  obtain ⟨V₂, h₂, w₂, hV₂, hw₂, hz₂⟩ :=
    s2v_l1b_etale_binomial_chart_image p.left U c z het b a hab.symm k₂ hk₂
  refine ⟨V₁, V₂, h₁, h₂, w₁, w₂, ?_, hw₁, hw₂, hz₁, hz₂⟩
  rw [hV₁, hV₂]
  exact s2v_l1b_iso_chart_cover (p.left ⁻¹ᵁ U.1) e j₁ j₂ hcover

end HodgeLean.Foundations.Program
