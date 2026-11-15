import HodgeLean.Foundations.Program.SchoenTowerI2aNormalizationSourceIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An affine open chart retaining the specified field point presents the actual
normalization pullback over that chart by the integral closure in the same field.
Source: Mathlib, Scheme.Hom.normalizationPullback and Scheme.Hom.normalizationObjIso. -/
theorem s2v_i2a_open_field_normalization_square
    {K : Type} [Field K] {Y V : Scheme}
    (f : Spec ↧K ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (u : V ⟶ Y) [IsOpenImmersion u] [IsAffine V]
    (ηV : Spec ↧K ⟶ V) (hηV : ηV ≫ u = f) :
    let φ : Γ(V, ⊤) →+* K := (ηV.appTop ≫ (Scheme.ΓSpecIso ↧K).hom).hom
    letI := φ.toAlgebra
    ∃ e : pullback f.fromNormalization u ≅ Spec ↧(integralClosure Γ(V, ⊤) K),
      pullback.snd f.fromNormalization u ≫ V.toSpecΓ =
        e.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(V, ⊤) (integralClosure Γ(V, ⊤) K))) := by
  haveI : QuasiCompact ηV := by
    haveI : QuasiCompact (ηV ≫ u) := hηV.symm ▸ inferInstance
    exact QuasiCompact.of_comp ηV u
  haveI : QuasiSeparated ηV := by
    haveI : QuasiSeparated (ηV ≫ u) := hηV.symm ▸ inferInstance
    exact QuasiSeparated.of_comp ηV u
  let l : Spec ↧K ⟶ pullback f u := pullback.lift (𝟙 _) ηV (by simpa using hηV.symm)
  haveI : IsIso (pullback.fst f u) := by
    refine ⟨⟨l, ?_, ?_⟩⟩
    · apply pullback.hom_ext
      · simp [l]
      · rw [Category.assoc, show l ≫ pullback.snd f u = ηV from pullback.lift_snd ..]
        apply (cancel_mono u).mp
        rw [Category.assoc, hηV, pullback.condition, Category.id_comp]
    · simp [l]
  have hfield : (asIso (pullback.fst f u)).hom ≫ ηV = pullback.snd f u := by
    apply (cancel_mono u).mp
    rw [Category.assoc, hηV, asIso_hom]
    exact pullback.condition
  obtain ⟨E, hE⟩ := s2v_i2a_normalization_source_iso (pullback.snd f u) ηV
    (asIso (pullback.fst f u)) hfield
  obtain ⟨N, hN⟩ := s2v_i2a_field_normalization_square ηV ⊤ (isAffineOpen_top _) (by simp)
  haveI : IsIso (⊤ : V.Opens).ι := inferInstanceAs (IsIso V.topIso.hom)
  let T : pullback ηV.fromNormalization (⊤ : V.Opens).ι ≅ ηV.normalization :=
    asIso (pullback.fst _ _)
  refine ⟨(asIso (f.normalizationPullback u)).symm ≪≫ E ≪≫ T.symm ≪≫ N, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [← hN, Scheme.Opens.toSpecΓ_top]
  have hT : T.inv ≫ pullback.snd ηV.fromNormalization (⊤ : V.Opens).ι ≫
      (⊤ : V.Opens).ι = ηV.fromNormalization := by
    rw [← pullback.condition, ← Category.assoc]
    change T.inv ≫ T.hom ≫ ηV.fromNormalization = _
    rw [T.inv_hom_id_assoc]
  have hT' := congrArg (fun k => k ≫ V.toSpecΓ) hT
  have hE' := congrArg (fun k => k ≫ V.toSpecΓ) hE
  simp only [Category.assoc] at hT' hE' ⊢
  rw [hT', hE', ← Scheme.Hom.normalizationPullback_snd f u]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

end HodgeLean.Foundations.Program
