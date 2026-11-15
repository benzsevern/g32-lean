import HodgeLean.Foundations.Program.SchoenTowerL1bComparisonRestriction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An affine chart over a base open identifies its coefficient map with the actual section map. -/
theorem s2v_l1b_chart_image_sections {B X : Scheme} (p : X ⟶ B)
    (U : B.affineOpens) (A : CommRingCat)
    (j : Spec A ⟶ X) [IsOpenImmersion j] (a : Γ(B, U) ⟶ A)
    (hj : j ≫ p = Spec.map a ≫ U.2.fromSpec) :
    ∃ (V : X.affineOpens) (hV : V.1 ≤ p ⁻¹ᵁ U.1)
      (e : A ≃+* Γ(X, V)),
      V.1 = j ''ᵁ ⊤ ∧ e.toRingHom.comp a.hom = (p.appLE U.1 V.1 hV).hom := by
  let V : X.affineOpens := ⟨j ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion j⟩
  have hV : V.1 ≤ p ⁻¹ᵁ U.1 := by
    rintro _ ⟨z, _, rfl⟩
    have he := congrArg (fun f : Spec A ⟶ B => f z) hj
    change p (j z) ∈ U.1
    change p (j z) = U.2.fromSpec (Spec.map a z) at he
    rw [he]
    exact U.2.fromSpec_preimage_self.ge (show Spec.map a z ∈ (⊤ : (Spec Γ(B, U)).Opens) from trivial)
  let e := ((Scheme.ΓSpecIso A).symm ≪≫ (j.appIso ⊤).symm).commRingCatIsoToRingEquiv
  refine ⟨V, hV, e, rfl, ?_⟩
  have hs : (Spec.map a ≫ U.2.fromSpec).appLE U.1 ⊤
      (by intro z hz; exact U.2.fromSpec_preimage_self.ge trivial) =
      a ≫ (Scheme.ΓSpecIso A).inv := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map a) U.2.fromSpec U.1 ⊤ ⊤
      U.2.fromSpec_preimage_self.ge (by intro z hz; trivial), s2v_l1b_fromSpec_appLE]
    change (Scheme.ΓSpecIso Γ(B, U)).inv ≫ (Spec.map a).appTop = _
    exact (Scheme.ΓSpecIso_inv_naturality a).symm
  have hh : p.appLE U.1 V.1 hV ≫ (j.appIso ⊤).hom =
      a ≫ (Scheme.ΓSpecIso A).inv := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    have hc (f g : Spec A ⟶ B) (hfg : f = g)
        (hf : (⊤ : (Spec A).Opens) ≤ f ⁻¹ᵁ U.1)
        (hg : (⊤ : (Spec A).Opens) ≤ g ⁻¹ᵁ U.1) :
        f.appLE U.1 ⊤ hf = g.appLE U.1 ⊤ hg := by
      subst g
      rfl
    exact (hc _ _ hj _ _).trans hs
  have hh' := congrArg (fun f => f ≫ (j.appIso ⊤).inv) hh
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh'
  exact (congrArg CommRingCat.Hom.hom hh').symm

/-- A two-chart cover transports through an isomorphism onto the whole ambient open. -/
theorem s2v_l1b_iso_chart_cover {X M A₁ A₂ : Scheme} (O : X.Opens)
    (e : O.toScheme ≅ M)
    (j₁ : A₁ ⟶ M) [IsOpenImmersion j₁]
    (j₂ : A₂ ⟶ M) [IsOpenImmersion j₂]
    (hcover : ∀ z : M, (∃ a, j₁ a = z) ∨ ∃ a, j₂ a = z) :
    (j₁ ≫ e.inv ≫ O.ι) ''ᵁ ⊤ ⊔ (j₂ ≫ e.inv ≫ O.ι) ''ᵁ ⊤ = O := by
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨a, _, rfl⟩
      exact (e.inv (j₁ a)).property
    · rintro _ ⟨a, _, rfl⟩
      exact (e.inv (j₂ a)).property
  · intro x hx
    have he : e.inv (e.hom ⟨x, hx⟩) = ⟨x, hx⟩ := by
      exact congrArg (fun f : O.toScheme ⟶ O.toScheme => f ⟨x, hx⟩) e.hom_inv_id
    rcases hcover (e.hom ⟨x, hx⟩) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a, trivial, by
        change (e.inv (j₁ a)).val = x
        rw [ha, he]⟩
    · exact Or.inr ⟨a, trivial, by
        change (e.inv (j₂ a)).val = x
        rw [ha, he]⟩

end HodgeLean.Foundations.Program
