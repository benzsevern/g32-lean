import HodgeLean.Foundations.Program.SchoenTowerL1bOverlapDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bTargetCover
import Mathlib.AlgebraicGeometry.Morphisms.Flat

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A flat source over a trivializing affine ring has at most one lift into the two-chart model. -/
theorem s2v_l1b_model_flat_hom_ext {R A : Type} [CommRing R] [CommRing A]
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
    (T : Scheme) (h : T ⟶ Spec (CommRingCat.of A)) [Flat h]
    (k l : T ⟶ M)
    (hk : k ≫ π = h ≫ Spec.map (CommRingCat.ofHom f))
    (hl : l ≫ π = h ≫ Spec.map (CommRingCat.ofHom f)) : k = l := by
  let C : Bool → Scheme := fun b => if b then
    Spec (CommRingCat.of (s2v_L1bChart u v)) else Spec (CommRingCat.of (s2v_L1bChart v u))
  let j : ∀ b, C b ⟶ M := fun b => by cases b; exact j₂; exact j₁
  let 𝒰 : M.OpenCover := Scheme.Cover.mkOfCovers Bool C j (by
    intro x
    rcases hcover x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨true, a, ha⟩
    · exact ⟨false, a, ha⟩) (by intro b; cases b <;> infer_instance)
  apply s2v_l1b_target_cover_hom_ext π (h ≫ Spec.map (CommRingCat.ofHom f)) 𝒰 ?_ k l hk hl
  intro V _ a _ b c s t hs ht
  change Bool at b c
  let H := V.isoSpec.inv ≫ a ≫ h
  have hH : Flat H := inferInstance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective H
  letI : Algebra A Γ(V, ⊤) := ψ.hom.toAlgebra
  haveI : Module.Flat A Γ(V, ⊤) := by
    change ψ.hom.Flat
    exact Flat.SpecMap_iff.mp (hψ.symm ▸ hH)
  have hs' : (V.isoSpec.inv ≫ s) ≫ 𝒰.f b ≫ π =
      Spec.map (CommRingCat.ofHom ((algebraMap A Γ(V, ⊤)).comp f)) := by
    rw [Category.assoc, hs]
    change H ≫ Spec.map (CommRingCat.ofHom f) = _
    rw [← hψ, ← Spec.map_comp]
    rfl
  have ht' : (V.isoSpec.inv ≫ t) ≫ 𝒰.f c ≫ π =
      Spec.map (CommRingCat.ofHom ((algebraMap A Γ(V, ⊤)).comp f)) := by
    rw [Category.assoc, ht]
    change H ≫ Spec.map (CommRingCat.ofHom f) = _
    rw [← hψ, ← Spec.map_comp]
    rfl
  apply (cancel_epi V.isoSpec.inv).mp
  simp only [← Category.assoc]
  cases b <;> cases c
  · change (V.isoSpec.inv ≫ s) ≫ j₂ = (V.isoSpec.inv ≫ t) ≫ j₂
    change (V.isoSpec.inv ≫ s) ≫ j₂ ≫ π = _ at hs'
    change (V.isoSpec.inv ≫ t) ≫ j₂ ≫ π = _ at ht'
    rw [hp₂] at hs' ht'
    have hvunit := s2v_l1b_affine_chart_coefficient_unit v u f I hv hu
      (hI.trans (by rw [Set.pair_comm])) e _ hs'
    have heq := s2v_l1b_affine_chart_hom_ext v u ((algebraMap A Γ(V, ⊤)).comp f)
      (s2v_l1b_trivialization_element_flat I e ⟨f u, hu⟩ hvunit) _ _ hs' ht'
    rw [heq]
  · change (V.isoSpec.inv ≫ s) ≫ j₂ = (V.isoSpec.inv ≫ t) ≫ j₁
    change (V.isoSpec.inv ≫ s) ≫ j₂ ≫ π = _ at hs'
    change (V.isoSpec.inv ≫ t) ≫ j₁ ≫ π = _ at ht'
    rw [hp₂] at hs'
    rw [hp₁] at ht'
    have huunit := s2v_l1b_affine_chart_coefficient_unit v u f I hv hu
      (hI.trans (by rw [Set.pair_comm])) e _ hs'
    have hvunit := s2v_l1b_affine_chart_coefficient_unit u v f I hu hv hI e _ ht'
    exact (s2v_l1b_affine_opposite_lifts_agree u v f I hu hv e huunit hvunit M
      j₁ j₂ htransition _ _ ht' hs').symm
  · change (V.isoSpec.inv ≫ s) ≫ j₁ = (V.isoSpec.inv ≫ t) ≫ j₂
    change (V.isoSpec.inv ≫ s) ≫ j₁ ≫ π = _ at hs'
    change (V.isoSpec.inv ≫ t) ≫ j₂ ≫ π = _ at ht'
    rw [hp₁] at hs'
    rw [hp₂] at ht'
    have hvunit := s2v_l1b_affine_chart_coefficient_unit u v f I hu hv hI e _ hs'
    have huunit := s2v_l1b_affine_chart_coefficient_unit v u f I hv hu
      (hI.trans (by rw [Set.pair_comm])) e _ ht'
    exact s2v_l1b_affine_opposite_lifts_agree u v f I hu hv e huunit hvunit M
      j₁ j₂ htransition _ _ hs' ht'
  · change (V.isoSpec.inv ≫ s) ≫ j₁ = (V.isoSpec.inv ≫ t) ≫ j₁
    change (V.isoSpec.inv ≫ s) ≫ j₁ ≫ π = _ at hs'
    change (V.isoSpec.inv ≫ t) ≫ j₁ ≫ π = _ at ht'
    rw [hp₁] at hs' ht'
    have hvunit := s2v_l1b_affine_chart_coefficient_unit u v f I hu hv hI e _ hs'
    have heq := s2v_l1b_affine_chart_hom_ext u v ((algebraMap A Γ(V, ⊤)).comp f)
      (s2v_l1b_trivialization_element_flat I e ⟨f v, hv⟩ hvunit) _ _ hs' ht'
    rw [heq]

end HodgeLean.Foundations.Program
