import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Program

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem b54_graded_surjective_on_components (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) {n : ℕ} {b : B} (hb : b ∈ ℬ n) :
    ∃ a ∈ 𝒜 n, f a = b := by
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a n, (DirectSum.decompose 𝒜 a n).property, ?_⟩
  rw [f.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ hb]

theorem b54_away_map_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) {r : A} {n : ℕ} (hr : r ∈ 𝒜 n) :
    Function.Surjective (HomogeneousLocalization.Away.map f r) := by
  intro z
  obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective ℬ (f.map_mem hr) z
  obtain ⟨a, ha, rfl⟩ := b54_graded_surjective_on_components f hf hb
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 hr m a ha, ?_⟩
  convert HomogeneousLocalization.Away.map_mk f r hr m a ha using 1

set_option backward.isDefEq.respectTransparency false in
theorem b54_proj_map_isClosedImmersion_of_cover (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hsurj : Function.Surjective f) {ι : Type*} (v : ι → A) (d : ι → ℕ)
    (hv : ∀ i, v i ∈ 𝒜 (d i)) (hd : ∀ i, 0 < d i)
    (hcover : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range v)) :
    IsClosedImmersion (Proj.map f hf) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (Proj.iSup_basicOpen_eq_top _ v hcover)]
  intro i
  let eS := Proj.basicOpenIsoSpec ℬ (f (v i)) (f.map_mem (hv i)) (hd i)
  let eT := Proj.basicOpenIsoSpec 𝒜 (v i) (hv i) (hd i)
  let ePre : (Proj.map f hf ⁻¹ᵁ Proj.basicOpen 𝒜 (v i)).toScheme ≅
      (Proj.basicOpen ℬ (f (v i))).toScheme :=
    Scheme.isoOfEq _ (Proj.map_preimage_basicOpen f hf (v i))
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ eT.hom,
    ← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
      (ePre ≪≫ eS).inv]
  convert IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (HomogeneousLocalization.Away.map f (v i)))
    (b54_away_map_surjective f hsurj (hv i)) using 1
  let targetAway := Proj.awayι 𝒜 (v i) (hv i) (hd i)
  letI : Mono targetAway := by
    dsimp [targetAway, Proj.awayι]
    infer_instance
  apply (cancel_mono targetAway).1
  simp only [Category.assoc]
  rw [show eT.hom ≫ targetAway = (Proj.basicOpen 𝒜 (v i)).ι by
    simp [targetAway, eT, Proj.awayι]]
  rw [morphismRestrict_ι]
  dsimp [ePre, eS]
  simp only [Scheme.isoOfEq_inv, Category.assoc, Scheme.homOfLE_ι_assoc,
    Proj.basicOpenIsoSpec_inv_ι_assoc]
  exact Proj.awayι_comp_map f hf (hd i) (v i) (hv i)

theorem b54_irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ _
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro b hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨n, hn, hb⟩ := hb
  obtain ⟨a, ha, rfl⟩ := b54_graded_surjective_on_components f hf hb
  apply Ideal.mem_map_of_mem
  change a ∈ HomogeneousIdeal.irrelevant 𝒜
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
  exact DirectSum.decompose_of_mem_ne 𝒜 ha hn.ne'

theorem b54_proj_map_isClosedImmersion (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hsurj : Function.Surjective f) : IsClosedImmersion (Proj.map f hf) := by
  apply b54_proj_map_isClosedImmersion_of_cover f hf hsurj
    (ι := Σ n : PNat, 𝒜 n) (fun i ↦ i.2.val) (fun i ↦ i.1.val)
    (fun i ↦ i.2.property) (fun i ↦ i.1.property)
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro a ha
  simp only [Set.mem_iUnion] at ha
  obtain ⟨n, hn, ha⟩ := ha
  exact Ideal.subset_span ⟨⟨⟨n, hn⟩, ⟨a, ha⟩⟩, rfl⟩

end HodgeLean.Foundations.Program
