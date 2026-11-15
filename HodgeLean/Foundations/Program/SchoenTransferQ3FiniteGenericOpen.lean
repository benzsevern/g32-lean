import HodgeLean.Foundations.Program.SchoenTransferQ3Generalizing
import HodgeLean.Foundations.Program.SchoenTransferQ3EtaleRefinement

/-! Generic support refinements that preserve the finite ambient map. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- For a finite map from an integral support component, every open around
its generic point contains the inverse image of a target neighbourhood of
its generic image. -/
theorem s4_q3_finite_generic_open_refinement
    {C D : Scheme} [IsIntegral C] (f : C ⟶ D) [IsFinite f]
    (U : C.Opens) (hU : genericPoint C ∈ U) :
    ∃ V : D.Opens, f (genericPoint C) ∈ V ∧ f ⁻¹ᵁ V ≤ U := by
  let B : Set D := f '' (U : Set C)ᶜ
  have hB : IsClosed B := f.isClosedMap _ U.isOpen.isClosed_compl
  let V : D.Opens := ⟨Bᶜ, hB.isOpen_compl⟩
  have hgeneric : f (genericPoint C) ∉ B := by
    rintro ⟨p, hp, hfp⟩
    have heq : p = genericPoint C := by
      by_contra hne
      have hle : p ≤ genericPoint C := genericPoint_specializes p
      have hlt : p < genericPoint C := lt_iff_le_not_ge.mpr ⟨hle, fun hrev =>
        hne (((show Specializes (genericPoint C) p from hle).antisymm hrev).eq.symm)⟩
      have hflt := s2v_l1b_divisor_quasi_finite_strictMono f hlt
      rw [hfp] at hflt
      exact (lt_irrefl _ hflt)
    exact hp (heq.symm ▸ hU)
  refine ⟨V, hgeneric, ?_⟩
  intro p hp
  by_contra hnot
  exact hp ⟨p, hnot, rfl⟩

/-- The common smooth etale target can be refined so that its entire source
component lies in a prescribed generic support open. -/
theorem s4_q3_smooth_etale_refinement_in_source_open
    {C D : Over (Spec ↧ℂ)} [IsIntegral C.left] [IsIntegral D.left]
    [LocallyOfFinitePresentation D.hom] (f : C ⟶ D) [IsFinite f.left]
    (U₀ : D.left.Opens) (hU₀ : Dense (U₀ : Set D.left))
    (hEt₀ : Etale (f.left ∣_ U₀))
    (O : C.left.Opens) (hO : genericPoint C.left ∈ O) :
    ∃ U : D.left.Opens, Dense (U : Set D.left) ∧ U ≤ U₀ ∧ f.left ⁻¹ᵁ U ≤ O ∧
      Smooth (U.ι ≫ D.hom) ∧ Etale (f.left ∣_ U) ∧
      Smooth ((f.left ⁻¹ᵁ U).ι ≫ C.hom) := by
  obtain ⟨A, hA, hAO⟩ := s4_q3_finite_generic_open_refinement f.left O hO
  have hdA : Dense (A : Set D.left) := A.isOpen.dense ⟨_, hA⟩
  let B := U₀ ⊓ A
  have hdB : Dense (B : Set D.left) := hU₀.inter_of_isOpen_right hdA A.isOpen
  have hEtB : Etale (f.left ∣_ B) := by
    letI := hEt₀
    have hs : Etale ((f.left ∣_ U₀) ∣_ (U₀.ι ⁻¹ᵁ B)) := inferInstance
    have himage : U₀.ι ''ᵁ (U₀.ι ⁻¹ᵁ B) = B := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr inf_le_left
    exact (MorphismProperty.arrow_mk_iso_iff @Etale.{0}
      (morphismRestrictRestrict f.left U₀ (U₀.ι ⁻¹ᵁ B) ≪≫
        morphismRestrictEq f.left himage)).mp hs
  obtain ⟨U, hdU, hUB, hsD, hEt, hsC⟩ := s4_q3_smooth_etale_refinement f B hdB hEtB
  refine ⟨U, hdU, hUB.trans inf_le_left, ?_, hsD, hEt, hsC⟩
  intro p hp
  exact hAO ((hUB hp).2)

end HodgeLean.Foundations.Program
