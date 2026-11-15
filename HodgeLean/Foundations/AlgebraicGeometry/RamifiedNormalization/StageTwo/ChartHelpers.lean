import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageTwo.Defs

noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageTwo

private lemma integral_transport {A B K L : Type*}
    [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    (f : A →+* K) (g : B →+* L) (a : A ≃+* B) (k : K ≃+* L)
    (h : g.comp a.toRingHom = k.toRingHom.comp f) {x : K}
    (hx : f.IsIntegralElem x) : g.IsIntegralElem (k x) := by
  obtain ⟨p, hp, hx⟩ := hx
  refine ⟨p.map a.toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, h]
  change Polynomial.eval₂ (k.toRingHom.comp f) (k.toRingHom x) p = 0
  rw [← Polynomial.hom_eval₂, hx, map_zero]

private def integralTransportEquiv {A B K L : Type*}
    [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    (f : A →+* K) (g : B →+* L) (a : A ≃+* B) (k : K ≃+* L)
    (h : g.comp a.toRingHom = k.toRingHom.comp f) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    integralClosure A K ≃+* integralClosure B L := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  have hi : f.comp a.symm.toRingHom = k.symm.toRingHom.comp g := by
    ext b
    apply k.injective
    change k (f (a.symm b)) = k (k.symm (g b))
    rw [k.apply_symm_apply]
    have hh := DFunLike.congr_fun h (a.symm b)
    change g (a (a.symm b)) = k (f (a.symm b)) at hh
    rw [a.apply_symm_apply] at hh
    exact hh.symm
  exact {
    toFun := fun x => ⟨k x, integral_transport f g a k h x.property⟩
    invFun := fun x => ⟨k.symm x, integral_transport g f a.symm k.symm hi x.property⟩
    left_inv := fun x => Subtype.ext (k.symm_apply_apply x)
    right_inv := fun x => Subtype.ext (k.apply_symm_apply x)
    map_mul' := fun x y => Subtype.ext (k.map_mul x y)
    map_add' := fun x y => Subtype.ext (k.map_add x y) }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem affine_chart_comparison {A K : Type} [CommRing A] [Field K] (f : A →+* K) :
    ∃ E : (Spec.map (CommRingCat.ofHom f)).normalization ≅
        Spec (CommRingCat.of (normalizedChart f)),
      (Spec.map (CommRingCat.ofHom f)).toNormalization ≫ E.hom =
        Spec.map (CommRingCat.ofHom (normalizedChart f).subtype) ∧
      E.hom ≫ Spec.map (CommRingCat.ofHom (integralCoeff f)) =
        (Spec.map (CommRingCat.ofHom f)).fromNormalization := by
  let F := Spec.map (CommRingCat.ofHom f)
  let U : (Spec (CommRingCat.of A)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let g : Γ(Spec (CommRingCat.of A), ⊤) →+* Γ(Spec (CommRingCat.of K), ⊤) :=
    F.appTop.hom
  let a := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let k := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hc : g.comp a.toRingHom = k.toRingHom.comp f := by
    exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm
  letI := f.toAlgebra
  letI := g.toAlgebra
  let e := integralTransportEquiv f g a k hc
  let q := F.normalizationOpenCover.f U
  haveI : IsIso q := isIso_of_isOpenImmersion_of_opensRange_eq_top q (by
    rw [← F.fromNormalization_preimage U]
    exact TopologicalSpace.Opens.map_top _)
  haveI : IsIso (F ⁻¹ᵁ U.1).ι := by
    change IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι
    exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  let E := (asIso q).symm ≪≫ Scheme.Spec.mapIso e.toCommRingCatIso.op
  refine ⟨E, ?_, ?_⟩
  · apply (cancel_epi (F ⁻¹ᵁ U.1).ι).mp
    rw [← Category.assoc, F.ι_toNormalization U]
    change (_ ≫ _ ≫ q) ≫ (inv q ≫ _) = _
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    change _ ≫ Spec.map (CommRingCat.ofHom (integralClosure Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of K), ⊤)).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) = _
    rw [← Spec.map_comp]
    change (⊤ : (Spec (CommRingCat.of K)).Opens).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom ((integralClosure Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of K), ⊤)).val.toRingHom.comp e.toRingHom)) = _
    have he : (integralClosure Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of K), ⊤)).val.toRingHom.comp e.toRingHom =
        k.toRingHom.comp (normalizedChart f).subtype := rfl
    rw [he, CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Opens.toSpecΓ_top]
    simp only [Category.assoc]
    congr 1
    change (Spec (CommRingCat.of K)).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ _ = _
    simp
  · apply (cancel_epi q).mp
    change q ≫ (inv q ≫ _) ≫ _ = _
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [F.ι_fromNormalization U]
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (integralCoeff f)) = _
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (e.toRingHom.comp (integralCoeff f))) =
      Spec.map (F.normalizationDiagramMap.app (.op U.1)) ≫ U.2.fromSpec
    have he : CommRingCat.ofHom (e.toRingHom.comp (integralCoeff f)) =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ F.normalizationDiagramMap.app (.op U.1) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      apply Subtype.ext
      change k (f x) = g (a x)
      exact (DFunLike.congr_fun hc x).symm
    rw [he, Spec.map_comp]
    congr 1
    apply (cancel_mono (Spec (CommRingCat.of A)).toSpecΓ).mp
    simp [U, IsAffineOpen.fromSpec_toSpecΓ]

end AlgebraicGeometry.RamifiedNormalization.StageTwo
