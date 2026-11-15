import HodgeLean.Foundations.Program.G32Native.PairedC3UnionGluing

/-! # Total-transform gluing for an integral slice and a Cartier centre cut -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Local ideal identities above the centre-slice intersection, together
with the actual off-centre isomorphism, give the global ideal identity.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_global_union
    {Q X Y : Scheme.{0}} [IsReduced Q] (i : Q ⟶ Y) [IsClosedImmersion i]
    (σ : X ⟶ Y) (K : Y.IdealSheafData)
    (U : Y.Opens) (hU : ∀ y, y ∈ U ↔ y ∉ K.support)
    (e : (σ ⁻¹ᵁ U).toScheme ≅ U.toScheme) (he : e.hom = σ ∣_ U)
    (hlocal : ∀ y : X, σ y ∈ i.ker.support → σ y ∈ K.support →
      ∃ V : X.affineOpens, y ∈ V.1 ∧
        (i.ker.comap σ).ideal V = (s2c_strictTransform σ i.ker K).ideal V ⊓
          ((K.comap σ).ideal V ⊔ (i.ker.comap σ).ideal V)) :
    i.ker.comap σ = s2c_strictTransform σ i.ker K ⊓ (K.comap σ ⊔ i.ker.comap σ) := by
  have hneighborhood : ∀ y : X, ∃ V : X.affineOpens, y ∈ V.1 ∧
      (i.ker.comap σ).ideal V = (s2c_strictTransform σ i.ker K).ideal V ⊓
        ((K.comap σ).ideal V ⊔ (i.ker.comap σ).ideal V) := by
    intro y
    by_cases hs : σ y ∈ i.ker.support
    · by_cases hk : σ y ∈ K.support
      · exact hlocal y hs hk
      · have hyW : y ∈ σ ⁻¹ᵁ U := (hU _).mpr hk
        obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open hyW (σ ⁻¹ᵁ U).isOpen
        let V' : X.affineOpens := ⟨V, hV⟩
        have hle : V ≤ σ ⁻¹ᵁ U := hVW
        have hf : V'.1.ι ≫ σ = X.homOfLE hle ≫ e.hom ≫ U.ι := by
          rw [he, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
        letI : IsOpenImmersion (V'.1.ι ≫ σ) := by
          rw [hf]
          infer_instance
        have hred := paired_c3_open_pullback_reduced i (V'.1.ι ≫ σ)
        rw [Scheme.IdealSheafData.comap_comp] at hred
        have hrad := paired_c3_affine_sections_radical (i.ker.comap σ) V' hred
        have havoid : ∀ z ∈ V, σ z ∉ K.support := by
          intro z hz
          exact (hU _).mp (hle hz)
        have hKtop : (K.comap σ).ideal V' = ⊤ := by
          apply paired_c3_ideal_top_of_avoid
          intro z hz hmem
          apply havoid z hz
          have hmem' : z ∈ ((K.comap σ).support : Set X) := hmem
          rw [Scheme.IdealSheafData.support_comap] at hmem'
          exact hmem'
        refine ⟨V', hyV, ?_⟩
        rw [paired_c3_strict_off_centre_sections σ i.ker K V' hKtop hrad, hKtop, top_sup_eq, inf_top_eq]
    · let O : X.Opens := ⟨(σ ⁻¹' (i.ker.support : Set Y))ᶜ,
        (i.ker.support.isClosed.preimage σ.continuous).isOpen_compl⟩
      have hyO : y ∈ O := hs
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVO⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hyO O.isOpen
      let V' : X.affineOpens := ⟨V, hV⟩
      have hItop : (i.ker.comap σ).ideal V' = ⊤ := by
        apply paired_c3_ideal_top_of_avoid
        intro z hz hmem
        apply hVO hz
        have hmem' : z ∈ ((i.ker.comap σ).support : Set X) := hmem
        rw [Scheme.IdealSheafData.support_comap] at hmem'
        exact hmem'
      exact ⟨V', hyV, paired_c3_union_off_slice_sections σ i.ker K V' hItop⟩
  choose V hyV hV using hneighborhood
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
  · apply top_unique
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyV y⟩
  · exact hV

#print axioms paired_c3_global_union
end HodgeLean.Foundations.Program.G32Native
