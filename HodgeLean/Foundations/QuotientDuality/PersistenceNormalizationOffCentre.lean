import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationRestrictionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationOpenEtale
import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers

/-! The actual normalization transition away from a blowup centre. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_normalization_off_centre_iso
    {K : Type} [Field K] {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : Spec ↧K ⟶ X) (g : Spec ↧K ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    [QuasiCompact g] [QuasiSeparated g] [IsDominant g]
    (b : X ⟶ Y) (hfg : f ≫ b = g) (I : Y.IdealSheafData)
    (hblowup : ∀ (T : Scheme) (j : T ⟶ Y),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap j).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X, u ≫ b = j)
    (w : f.normalization ⟶ g.normalization)
    (hw : f.toNormalization ≫ w = g.toNormalization)
    (hwb : w ≫ g.fromNormalization = f.fromNormalization ≫ b)
    (V : Y.Opens) (hV : (V : Set Y).Nonempty)
    (havoid : ∀ y ∈ V, y ∉ I.support) :
    ∃ E : (f.fromNormalization ⁻¹ᵁ (b ⁻¹ᵁ V)).toScheme ≅
        (g.fromNormalization ⁻¹ᵁ V).toScheme,
      E.hom ≫ (g.fromNormalization ⁻¹ᵁ V).ι =
        (f.fromNormalization ⁻¹ᵁ (b ⁻¹ᵁ V)).ι ≫ w := by
  have hI : I.comap V.ι = ⊤ := by
    apply s2e_comap_eq_top_of_disjoint
    rw [Scheme.Opens.range_ι]
    exact Set.disjoint_left.mpr (fun y hy hi => havoid y hy hi)
  haveI : IsIso (pullback.snd b V.ι) :=
    s2e_blowup_scheme_isIso_off_centre b I hblowup V.ι hI
  haveI : IsIso (b ∣_ V) := by
    let E := pullbackRestrictIsoRestrict b V
    haveI : IsIso (E.hom ≫ (b ∣_ V)) := by
      rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
      infer_instance
    exact IsIso.of_isIso_comp_left E.hom (b ∣_ V)
  have hU : ((b ⁻¹ᵁ V) : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := hV
    obtain ⟨x, _⟩ := (b ∣_ V).surjective ⟨y, hy⟩
    exact ⟨x.val, x.property⟩
  obtain ⟨fU, hfqc, hfqs, hf⟩ :=
    s2e_c1_generic_source_lift_to_open X f (b ⁻¹ᵁ V) hU
  obtain ⟨gV, hgqc, hgqs, hg⟩ := s2e_c1_generic_source_lift_to_open Y g V hV
  letI := hfqc
  letI := hfqs
  letI := hgqc
  letI := hgqs
  have he : fU ≫ (b ∣_ V) = gV := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hf, hg, hfg]
  exact s2e_c1_normalization_transition_open_iso f g b w hw hwb
    (b ⁻¹ᵁ V) V (asIso (b ∣_ V)) (morphismRestrict_ι b V) fU gV hf hg he

lemma persistence_unique_scheme_fibre_of_open_iso
    {X Y : Scheme} (w : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hU : U = w ⁻¹ᵁ V) (E : U.toScheme ≅ V.toScheme)
    (hE : E.hom ≫ V.ι = U.ι ≫ w)
    (y : Y) (hy : y ∈ V) : ∃! x : X, w x = y := by
  let H := E.hom.homeomorph
  let u : U := H.symm ⟨y, hy⟩
  have hu : E.hom u = ⟨y, hy⟩ := H.apply_symm_apply ⟨y, hy⟩
  have hpoint (z : U) : (E.hom z).val = w z.val := by
    exact congrArg (fun f : U.toScheme ⟶ Y => f z) hE
  refine ⟨u.val, (hpoint u).symm.trans (congrArg Subtype.val hu), ?_⟩
  intro x hx
  have hxU : x ∈ U := by
    rw [hU]
    change w x ∈ V
    rw [hx]
    exact hy
  have heq : E.hom ⟨x, hxU⟩ = E.hom u := by
    rw [hu]
    apply Subtype.ext
    exact (hpoint ⟨x, hxU⟩).trans hx
  exact congrArg Subtype.val (H.injective heq)

end HodgeLean.Foundations.QuotientDuality
