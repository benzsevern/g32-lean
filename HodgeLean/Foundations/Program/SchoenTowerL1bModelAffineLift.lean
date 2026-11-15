import HodgeLean.Foundations.Program.SchoenTowerL1bModelUniqueness

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A trivialized two-generated ideal on an affine source gives a unique lift into the model. -/
theorem s2v_l1b_model_affine_lift {R A : Type} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (I : Ideal A)
    (hu : f u ∈ I) (hv : f v ∈ I) (hI : I = Ideal.span {f u, f v})
    (e : I ≃ₗ[A] A) (M : Scheme)
    (j₁ : Spec (CommRingCat.of (s2v_L1bChart u v)) ⟶ M)
    (j₂ : Spec (CommRingCat.of (s2v_L1bChart v u)) ⟶ M)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (π : M ⟶ Spec (CommRingCat.of R))
    (hcover : ∀ z : M, (∃ a, j₁ a = z) ∨ ∃ a, j₂ a = z)
    (hp₁ : j₁ ≫ π = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp
        Polynomial.C)))
    (hp₂ : j₂ ≫ π = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp
        Polynomial.C)))
    (htransition :
      let ε := Classical.choose (s2v_l1b_overlap_equiv u v)
      Spec.map (CommRingCat.ofHom
        (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))) ≫ j₁ =
      Spec.map (CommRingCat.ofHom ε.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u))) ≫ j₂)
 :
    ∃! k : Spec (CommRingCat.of A) ⟶ M, k ≫ π = Spec.map (CommRingCat.ofHom f) := by
  let c : Bool → A := fun b => if b then e ⟨f v, hv⟩ else e ⟨f u, hu⟩
  have hc : Set.range c = {e ⟨f u, hu⟩, e ⟨f v, hv⟩} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp [c]
    · intro hx
      rcases hx with hx | hx
      · exact ⟨false, hx.symm⟩
      · exact ⟨true, (Set.mem_singleton_iff.mp hx).symm⟩
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of A) c (by
    rw [hc]
    exact s2v_l1b_invertible_ideal_coefficients I (f u) (f v) hu hv hI e)).openCover
  have hlocal : ∀ b : Bool, ∃ k : 𝒰.X b ⟶ M,
      k ≫ π = 𝒰.f b ≫ Spec.map (CommRingCat.ofHom f) := by
    intro b
    cases b
    · obtain ⟨k, hk, _⟩ := s2v_l1b_affine_chart_lift (B := Localization.Away (e ⟨f u, hu⟩)) v u f I hv hu e
        (IsLocalization.Away.algebraMap_isUnit (e ⟨f u, hu⟩))
      refine ⟨k ≫ j₂, ?_⟩
      rw [Category.assoc, hp₂, hk]
      change Spec.map (CommRingCat.ofHom ((algebraMap A _).comp f)) =
        Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ Spec.map (CommRingCat.ofHom f)
      rw [← Spec.map_comp]
      rfl
    · obtain ⟨k, hk, _⟩ := s2v_l1b_affine_chart_lift (B := Localization.Away (e ⟨f v, hv⟩)) u v f I hu hv e
        (IsLocalization.Away.algebraMap_isUnit (e ⟨f v, hv⟩))
      refine ⟨k ≫ j₁, ?_⟩
      rw [Category.assoc, hp₁, hk]
      change Spec.map (CommRingCat.ofHom ((algebraMap A _).comp f)) =
        Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ Spec.map (CommRingCat.ofHom f)
      rw [← Spec.map_comp]
      rfl
  choose k hk using hlocal
  have hcompat : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ k a =
      pullback.snd (𝒰.f a) (𝒰.f b) ≫ k b := by
    intro a b
    apply s2v_l1b_model_flat_hom_ext u v f I hu hv hI e M j₁ j₂ π hcover hp₁ hp₂
      htransition _ (pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a)
    · rw [Category.assoc, hk, Category.assoc]
    · rw [Category.assoc, hk, ← Category.assoc, ← pullback.condition, Category.assoc]
  refine ⟨𝒰.glueMorphisms k hcompat, ?_, ?_⟩
  · apply 𝒰.hom_ext
    intro a
    rw [← Category.assoc, 𝒰.ι_glueMorphisms, hk]
  · intro l hl
    apply s2v_l1b_model_flat_hom_ext u v f I hu hv hI e M j₁ j₂ π hcover hp₁ hp₂
      htransition _ (𝟙 _)
    · simpa only [Category.id_comp] using hl
    · simp only [Category.id_comp]
      apply 𝒰.hom_ext
      intro a
      rw [← Category.assoc, 𝒰.ι_glueMorphisms, hk]

end HodgeLean.Foundations.Program
