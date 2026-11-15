import HodgeLean.Foundations.SegreProjective
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Homogeneous chart maps that differ by units on overlaps give a global morphism. -/
theorem n2b_glue_graded_chart_maps
    {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{0}} (𝒰 : X.OpenCover)
    (f : ∀ i, A →+* Γ(𝒰.X i, ⊤))
    (hf : ∀ i, (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f i) = ⊤)
    (hu : ∀ i j, ∃ v : Γ(pullback (𝒰.f i) (𝒰.f j), ⊤)ˣ,
      ∀ (d : ℕ) (a : A), a ∈ 𝒜 d →
        (pullback.snd (𝒰.f i) (𝒰.f j)).appTop.hom (f j a) =
          (v : Γ(pullback (𝒰.f i) (𝒰.f j), ⊤)) ^ d *
            (pullback.fst (𝒰.f i) (𝒰.f j)).appTop.hom (f i a)) :
    ∃ g : X ⟶ Proj 𝒜, ∀ i,
      𝒰.f i ≫ g = Proj.fromOfGlobalSections 𝒜 (f i) (hf i) := by
  let φ := fun i => Proj.fromOfGlobalSections 𝒜 (f i) (hf i)
  have hφ : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ φ i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ φ j := by
    intro i j
    let p := pullback.fst (𝒰.f i) (𝒰.f j)
    let q := pullback.snd (𝒰.f i) (𝒰.f j)
    have hp : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (p.appTop.hom.comp (f i)) = ⊤ := by
      rw [← Ideal.map_map, hf i, Ideal.map_top]
    have hq : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (q.appTop.hom.comp (f j)) = ⊤ := by
      rw [← Ideal.map_map, hf j, Ideal.map_top]
    change p ≫ Proj.fromOfGlobalSections 𝒜 (f i) (hf i) =
      q ≫ Proj.fromOfGlobalSections 𝒜 (f j) (hf j)
    rw [spec_g3c_comp_fromOfGlobalSections 𝒜 p (f i) (hf i) hp,
      spec_g3c_comp_fromOfGlobalSections 𝒜 q (f j) (hf j) hq]
    obtain ⟨v, hv⟩ := hu i j
    exact spec_g3c_fromOfGlobalSections_unit_twist 𝒜 _ _ hp hq v hv
  exact ⟨𝒰.glueMorphisms φ hφ, fun i => 𝒰.ι_glueMorphisms φ hφ i⟩

/-- An immersion on a source chart gives an immersion on its corresponding target open. -/
theorem n2b_immersion_restrict_of_opensRange {X Y Z : Scheme.{0}}
    (g : X ⟶ Y) (V : Y.Opens) (ι : Z ⟶ X) [IsOpenImmersion ι]
    (hι : ι.opensRange = g ⁻¹ᵁ V) [IsImmersion (ι ≫ g)] :
    IsImmersion (g ∣_ V) := by
  haveI : IsIso (ι ∣_ (g ⁻¹ᵁ V)) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
    obtain ⟨z, hz⟩ : y.1 ∈ Set.range ι := by
      change y.1 ∈ ι.opensRange
      rw [hι]
      exact y.2
    refine ⟨⟨z, ?_⟩, Subtype.ext ?_⟩
    · change ι z ∈ g ⁻¹ᵁ V
      rw [hz]
      exact y.2
    · rw [morphismRestrict_base_coe]
      exact hz
  have h : IsImmersion ((ι ≫ g) ∣_ V) := inferInstance
  rw [morphismRestrict_comp] at h
  haveI := h
  have hh : IsImmersion (inv (ι ∣_ (g ⁻¹ᵁ V)) ≫
      ((ι ∣_ (g ⁻¹ᵁ V)) ≫ (g ∣_ V))) := inferInstance
  simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using hh

/-- Matching source and target charts let the local immersions determine a global immersion. -/
theorem n2b_immersion_of_matching_charts {X Y : Scheme.{0}}
    (g : X ⟶ Y) (𝒰 : X.OpenCover) (V : 𝒰.I₀ → Y.Opens)
    (hpre : ∀ i, (𝒰.f i).opensRange = g ⁻¹ᵁ V i)
    [∀ i, IsImmersion (𝒰.f i ≫ g)] : IsImmersion g := by
  letI : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun i hi f hf => by
      haveI := hi
      haveI := hf
      exact IsImmersion.comp f i⟩
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) V
  · rintro _ ⟨x, rfl⟩
    apply le_iSup V (𝒰.idx x)
    change x ∈ g ⁻¹ᵁ V (𝒰.idx x)
    rw [← hpre]
    exact 𝒰.covers x
  · intro i
    exact n2b_immersion_restrict_of_opensRange g (V i) (𝒰.f i) (hpre i)

end HodgeLean.Foundations.Program
