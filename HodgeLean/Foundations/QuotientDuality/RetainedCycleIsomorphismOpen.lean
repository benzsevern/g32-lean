import HodgeLean.Foundations.QuotientDuality.RetainedCycleTowerGeometry

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_dense_isomorphism_of_generic_source {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsSeparated f]
    (s : Spec Y.functionField ⟶ X) [IsDominant s]
    (hs : s ≫ f = Y.fromSpecStalk (genericPoint Y)) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsIso (f ∣_ U) := by
  obtain ⟨U, hηU, g, hsg, hgf⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f s (by simpa only [Category.comp_id] using hs)
  have hUg : Set.range g ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro x ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (g u) ∈ U
    rw [← Scheme.Hom.comp_apply, hgf]
    exact u.property
  let g' := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι g hUg
  have hg' : g' ≫ (f ⁻¹ᵁ U).ι = g := IsOpenImmersion.lift_fac _ _ _
  have hsec : g' ≫ (f ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', hgf, Category.id_comp, Category.comp_id]
  letI : IsDominant (U.fromSpecStalkOfMem (genericPoint Y) hηU ≫ g) := by
    rw [← hsg]
    infer_instance
  letI : IsDominant g := IsDominant.of_comp (U.fromSpecStalkOfMem (genericPoint Y) hηU) g
  letI : IsDominant (g' ≫ (f ⁻¹ᵁ U).ι) := by rw [hg']; infer_instance
  letI : IsDominant g' := IsDominant.of_comp_of_isOpenImmersion g' (f ⁻¹ᵁ U).ι
  letI : IsClosedImmersion (g' ≫ (f ∣_ U)) := by rw [hsec]; infer_instance
  letI : IsClosedImmersion g' := IsClosedImmersion.of_comp g' (f ∣_ U)
  letI : Surjective g' := surjective_of_isDominant_of_isClosed_range g'
    g'.isClosedEmbedding.isClosed_range
  letI : IsIso g' := isIso_of_isClosedImmersion_of_surjective g'
  letI : IsIso (g' ≫ (f ∣_ U)) := by rw [hsec]; infer_instance
  exact ⟨U, U.isOpen.dense ⟨_, hηU⟩, IsIso.of_isIso_comp_left g' (f ∣_ U)⟩

theorem retained_isomorphism_restrict_of_le {X Y : Scheme.{0}} (f : X ⟶ Y)
    (U V : Y.Opens) (hUV : U ≤ V) [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  have houter : IsPullback (f ∣_ U)
      (X.homOfLE (f.preimage_mono hUV) ≫ (f ⁻¹ᵁ V).ι)
      (Y.homOfLE hUV ≫ V.ι) f := by
    simpa only [Scheme.homOfLE_ι] using isPullback_morphismRestrict f U
  exact (houter.of_bot (morphismRestrict_homOfLE f U V hUV)
    (isPullback_morphismRestrict f V)).isIso_fst_of_isIso

theorem retained_dense_smooth_isomorphism_of_generic_source
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsProper f.left]
    (s : Spec Y.left.functionField ⟶ X.left) [IsDominant s]
    (hs : s ≫ f.left = Y.left.fromSpecStalk (genericPoint Y.left)) :
    ∃ U : Y.left.Opens, Dense (U : Set Y.left) ∧
      Smooth (U.ι ≫ Y.hom) ∧ IsIso (f.left ∣_ U) := by
  obtain ⟨V, hV, hfV⟩ := retained_dense_isomorphism_of_generic_source f.left s hs
  letI : IsIso (f.left ∣_ V) := hfV
  let U := V ⊓ Y.hom.smoothLocus
  have hU : Dense (U : Set Y.left) :=
    hV.inter_of_isOpen_left Y.hom.dense_smoothLocus_of_perfectField V.isOpen
  have hsm : Smooth (U.ι ≫ Y.hom) := by
    letI : Smooth (Y.hom.smoothLocus.ι ≫ Y.hom) := Y.hom.smooth_restrict_smoothLocus
    have h : Smooth (Y.left.homOfLE (show U ≤ Y.hom.smoothLocus from inf_le_right) ≫
        (Y.hom.smoothLocus.ι ≫ Y.hom)) := inferInstance
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  exact ⟨U, hU, hsm, retained_isomorphism_restrict_of_le f.left U V inf_le_left⟩

theorem retained_normalization_dense_smooth_isomorphism {r : ℕ}
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (W W₀ : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsIntegral W₀.left] [IsProjective W₀.hom]
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (e₀ : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (e : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    [IsProper (retainedCycleModification
      (fun i => s2b_normalizationOver (B i) (η i)) e₀ e w).left]
    (hgeneric : (η 0).toNormalization ≫ e₀.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization) :
    ∃ U : W₀.left.Opens, Dense (U : Set W₀.left) ∧
      Smooth (U.ι ≫ W₀.hom) ∧ IsIso ((retainedCycleModification
        (fun i => s2b_normalizationOver (B i) (η i)) e₀ e w).left ∣_ U) := by
  letI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  letI : IsDominant (η (Fin.last r)).toNormalization := by infer_instance
  letI : IsDominant e.hom.left := by infer_instance
  let s := (η (Fin.last r)).toNormalization ≫ e.hom.left
  letI : IsDominant s := by
    change IsDominant ((η (Fin.last r)).toNormalization ≫ e.hom.left)
    infer_instance
  apply retained_dense_smooth_isomorphism_of_generic_source _ s
  exact (retained_endpoint_source_square
    (fun i => s2b_normalizationOver (B i) (η i)) e₀ e w
    (fun i => (η i).toNormalization) hw).trans hgeneric

end HodgeLean.Foundations.QuotientDuality
