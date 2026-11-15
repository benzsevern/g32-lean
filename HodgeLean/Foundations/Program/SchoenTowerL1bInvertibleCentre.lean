import HodgeLean.Foundations.Program.SchoenTowerL1bComparisonRestriction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained blowup restricts to an isomorphism wherever the centre ideal is already invertible. -/
theorem s2v_l1b_blowup_isIso_on_invertible_open
    {B X : Scheme} (p : X ⟶ B) (I : B.IdealSheafData)
    (hcartier : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap p).ideal V) ≃ₗ[Γ(X, V)] Γ(X, V)))
    (hX : ∀ (T : Scheme) (f : T ⟶ B),
      (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.Opens)
    (hU : ∀ x : U.toScheme, ∃ V : U.toScheme.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap U.ι).ideal V) ≃ₗ[Γ(U.toScheme, V)] Γ(U.toScheme, V))) :
    IsIso (p ∣_ U) := by
  have hbase : ∀ x : U.toScheme, ∃ V : U.toScheme.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap ((𝟙 U.toScheme) ≫ U.ι)).ideal V)
        ≃ₗ[Γ(U.toScheme, V)] Γ(U.toScheme, V)) := by
    rw [Category.id_comp]
    exact hU
  obtain ⟨s, hs, _⟩ := s2v_l1b_blowup_open_lift p I hX U U.toScheme
    (𝟙 U.toScheme) hbase
  have hsource : ∀ x : (p ⁻¹ᵁ U).toScheme,
      ∃ V : (p ⁻¹ᵁ U).toScheme.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap ((p ∣_ U) ≫ U.ι)).ideal V)
          ≃ₗ[Γ((p ⁻¹ᵁ U).toScheme, V)] Γ((p ⁻¹ᵁ U).toScheme, V)) := by
    rw [morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
    exact s2v_l1b_local_trivialization_flat (p ⁻¹ᵁ U).ι (I.comap p) hcartier
  obtain ⟨k, hk, hu⟩ := s2v_l1b_blowup_open_lift p I hX U
    (p ⁻¹ᵁ U).toScheme (p ∣_ U) hsource
  have hps : (p ∣_ U) ≫ s = 𝟙 (p ⁻¹ᵁ U).toScheme := by
    exact (hu _ (by change ((p ∣_ U) ≫ s) ≫ (p ∣_ U) = (p ∣_ U); rw [Category.assoc, hs, Category.comp_id])).trans
      (hu _ (Category.id_comp _)).symm
  exact ⟨⟨s, hps, hs⟩⟩

end HodgeLean.Foundations.Program
