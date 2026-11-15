import HodgeLean.Foundations.Program.SchoenTowerL1bChartSections
import HodgeLean.Foundations.Program.SchoenTowerL1bChartGluing

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- Trivializations on an affine open cover give the retained local ideal-module freeness. -/
theorem s2v_l1b_affine_cover_trivialization {ι : Type*} {X : Scheme}
    (A : ι → Scheme) [∀ i, IsAffine (A i)]
    (j : ∀ i, A i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i a, j i a = x) (I : X.IdealSheafData)
    (h : ∀ i, Nonempty (((I.comap (j i)).ideal ⟨⊤, isAffineOpen_top _⟩)
      ≃ₗ[Γ(A i, ⊤)] Γ(A i, ⊤))) :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty ((I.ideal U) ≃ₗ[Γ(X, U)] Γ(X, U)) := by
  intro x
  obtain ⟨i, a, rfl⟩ := hcover x
  refine ⟨⟨j i ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion (j i)⟩, ?_, ?_⟩
  · exact ⟨a, trivial, rfl⟩
  · exact s2v_l1b_open_image_trivialization (j i) I (h i)

/-- The glued regular binomial model has the actual locally invertible pullback centre ideal. -/
theorem s2v_l1b_binomial_model_invertible {R : Type*} [CommRing R]
    (u v : R) (hv : IsRegular v)
    (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hu' : IsRegular u)
    (hv' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v))
    (I : (Spec (CommRingCat.of R)).IdealSheafData)
    (hI : I.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u,
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom v}) :
    ∃ (X : Scheme)
      (j₁ : Spec (CommRingCat.of (s2v_L1bChart u v)) ⟶ X)
      (j₂ : Spec (CommRingCat.of (s2v_L1bChart v u)) ⟶ X)
      (p : X ⟶ Spec (CommRingCat.of R)),
      IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
      (∀ x : X, (∃ a, j₁ a = x) ∨ ∃ b, j₂ b = x) ∧
      j₁ ≫ p = Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {C u - Polynomial.X * C v})).comp C)) ∧
      j₂ ≫ p = Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {C v - Polynomial.X * C u})).comp C)) ∧
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap p).ideal U) ≃ₗ[Γ(X, U)] Γ(X, U)) := by
  obtain ⟨X, j₁, j₂, p, hj₁, hj₂, hcover, hp₁, hp₂⟩ :=
    s2v_l1b_binomial_chart_scheme u v
  letI := hj₁
  letI := hj₂
  refine ⟨X, j₁, j₂, p, hj₁, hj₂, hcover, hp₁, hp₂, ?_⟩
  have h₁ : Nonempty ((((I.comap p).comap j₁).ideal ⟨⊤, isAffineOpen_top _⟩)
      ≃ₗ[Γ(Spec (CommRingCat.of (s2v_L1bChart u v)), ⊤)]
        Γ(Spec (CommRingCat.of (s2v_L1bChart u v)), ⊤)) := by
    rw [← Scheme.IdealSheafData.comap_comp, hp₁]
    exact s2v_l1b_chart_spectrum_trivialization u v hv hu I hI
  have h₂ : Nonempty ((((I.comap p).comap j₂).ideal ⟨⊤, isAffineOpen_top _⟩)
      ≃ₗ[Γ(Spec (CommRingCat.of (s2v_L1bChart v u)), ⊤)]
        Γ(Spec (CommRingCat.of (s2v_L1bChart v u)), ⊤)) := by
    rw [← Scheme.IdealSheafData.comap_comp, hp₂]
    apply s2v_l1b_chart_spectrum_trivialization v u hu' hv' I
    rw [hI, Set.pair_comm]
  intro x
  rcases hcover x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · refine ⟨⟨j₁ ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion j₁⟩,
      ⟨a, trivial, rfl⟩, ?_⟩
    exact s2v_l1b_open_image_trivialization j₁ (I.comap p) h₁
  · refine ⟨⟨j₂ ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion j₂⟩,
      ⟨a, trivial, rfl⟩, ?_⟩
    exact s2v_l1b_open_image_trivialization j₂ (I.comap p) h₂

end HodgeLean.Foundations.Program
