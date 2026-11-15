import HodgeLean.Foundations.Program.SchoenTowerL1bComparisonIso
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained blowup over an affine open with unit centre is the original
base affine scheme, by its actual ideal mapping property. -/
theorem s2v_l1b_blowup_unit_centre_iso
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : X.left, ∃ V : X.left.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (g : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap g.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! u : T ⟶ X, u ≫ p = g)
    (U : B.left.affineOpens) (hI : I.ideal U = ⊤) :
    IsIso (p.left ∣_ U.1) := by
  let J := I.comap U.2.fromSpec
  have hJ : J = ⊤ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [s2v_l1b_comap_ideal_affine_charts U.2.fromSpec I U
      ⟨⊤, isAffineOpen_top _⟩ U.2.fromSpec_preimage_self.ge, hI, Ideal.map_top]
    rfl
  have hfree : ∀ x : Spec Γ(B.left, U),
      ∃ V : (Spec Γ(B.left, U)).affineOpens, x ∈ V.1 ∧
        Nonempty (((J.comap (𝟙 _)).ideal V) ≃ₗ[Γ(Spec Γ(B.left, U), V)]
          Γ(Spec Γ(B.left, U), V)) := by
    intro x
    refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
    rw [hJ, Scheme.IdealSheafData.comap_top]
    exact ⟨Submodule.topEquiv⟩
  have hM : ∀ (T : Scheme) (g : T ⟶ Spec Γ(B.left, U)),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((J.comap g).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ Spec Γ(B.left, U), u ≫ 𝟙 _ = g := by
    intro T g _
    exact ⟨g, Category.comp_id _, fun u hu => (Category.comp_id u).symm.trans hu⟩
  obtain ⟨e, he⟩ := s2v_l1b_restricted_model_iso p.left I hcartier
    (s2v_l1b_blowup_scheme_lift B X p I hblowup) U _ (𝟙 _) hfree hM
  have hp : p.left ∣_ U.1 = e.hom ≫ U.2.isoSpec.inv := by
    rw [← Category.comp_id e.hom, he]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hp]
  infer_instance

/-- An etale restriction to a base affine open gives etale actual section
pullbacks on every affine source chart over that open. -/
theorem s2v_l1b_etale_appLE_of_restrict
    {X Y : Scheme} (p : X ⟶ Y) (U : Y.affineOpens)
    [Etale (p ∣_ U.1)] (V : X.affineOpens) (hV : V.1 ≤ p ⁻¹ᵁ U.1) :
    (p.appLE U.1 V.1 hV).hom.Etale := by
  letI : IsAffine U.1.toScheme := U.2
  letI := HasRingHomProperty.HasAffineProperty (P := @Etale)
  have hloc : sourceAffineLocally (fun f => RingHom.Etale f) (p ∣_ U.1) := by
    rw [← HasAffineProperty.iff_of_isAffine (P := @Etale)]
    infer_instance
  exact (sourceAffineLocally_morphismRestrict (fun f => RingHom.Etale f) p U.1 U.2).mp
    hloc V hV

/-- Etale coordinates pull back through a map which is etale over the chosen
base open, using the actual structure maps at both stages. -/
theorem s2v_l1b_etale_coordinates_of_restrict
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (U : B.left.affineOpens)
    [Etale (p.left ∣_ U.1)] (V : X.left.affineOpens)
    (hV : V.1 ≤ p.left ⁻¹ᵁ U.1) {σ : Type} (z : σ → Γ(B.left, U))
    (het : (MvPolynomial.eval₂Hom (B.hom.appLE ⊤ U.1 le_top).hom z).Etale) :
    (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom
      (fun i => (p.left.appLE U.1 V.1 hV).hom (z i))).Etale := by
  have heq : (p.left.appLE U.1 V.1 hV).hom.comp
      (MvPolynomial.eval₂Hom (B.hom.appLE ⊤ U.1 le_top).hom z) =
      MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom
        (fun i => (p.left.appLE U.1 V.1 hV).hom (z i)) := by
    apply MvPolynomial.ringHom_ext
    · intro s
      rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      change ((B.hom.appLE ⊤ U.1 le_top) ≫ p.left.appLE U.1 V.1 hV) s = _
      rw [Scheme.Hom.appLE_comp_appLE, Over.w p]
    · intro i
      rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  rw [← heq]
  exact RingHom.Etale.stableUnderComposition _ _ het
    (s2v_l1b_etale_appLE_of_restrict p.left U V hV)

end HodgeLean.Foundations.Program
