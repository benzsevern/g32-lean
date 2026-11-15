import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationOpenEtale
import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers

/-! # Normalization etaleness through the specified blowup away from its centre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained blowup property preserves etaleness of the actual
normalization cover on the full inverse image of an open avoiding its centre. -/
theorem s2e_c1_normalization_blowup_etale_off_centre
    {K : Type} [Field K] {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : Spec (CommRingCat.of K) ⟶ X) (g : Spec (CommRingCat.of K) ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    [QuasiCompact g] [QuasiSeparated g] [IsDominant g]
    (b : X ⟶ Y) (hfg : f ≫ b = g) (I : Y.IdealSheafData)
    (hblowup : ∀ (T : Scheme) (j : T ⟶ Y),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap j).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X, u ≫ b = j)
    (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    (havoid : ∀ y ∈ U, y ∉ I.support)
    [Etale (g.fromNormalization ∣_ U)] :
    Etale (f.fromNormalization ∣_ (b ⁻¹ᵁ U)) := by
  have hI : I.comap U.ι = ⊤ := by
    apply s2e_comap_eq_top_of_disjoint
    rw [Scheme.Opens.range_ι]
    exact Set.disjoint_left.mpr (fun y hy hi => havoid y hy hi)
  haveI : IsIso (pullback.snd b U.ι) :=
    s2e_blowup_scheme_isIso_off_centre b I hblowup U.ι hI
  let E := pullbackRestrictIsoRestrict b U
  haveI : IsIso (E.hom ≫ (b ∣_ U)) := by
    rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  haveI : IsIso (b ∣_ U) := IsIso.of_isIso_comp_left E.hom (b ∣_ U)
  have hpre : ((b ⁻¹ᵁ U) : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := hU
    obtain ⟨x, _⟩ := (b ∣_ U).surjective ⟨y, hy⟩
    exact ⟨x.val, x.property⟩
  exact s2e_c1_normalization_etale_of_open_base_iso f g b hfg (b ⁻¹ᵁ U) U hpre hU
    (asIso (b ∣_ U)) (morphismRestrict_ι b U)

end HodgeLean.Foundations.Program
