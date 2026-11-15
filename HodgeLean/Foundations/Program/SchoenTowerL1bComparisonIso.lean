import HodgeLean.Foundations.Program.SchoenTowerL1bComparisonRestriction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A model with the affine-base ideal mapping property identifies the whole restricted blowup. -/
theorem s2v_l1b_restricted_model_iso
    {B X : Scheme} (p : X ⟶ B) (I : B.IdealSheafData)
    (hcartier : ∀ z : X, ∃ V : X.affineOpens, z ∈ V.1 ∧
      Nonempty (((I.comap p).ideal V) ≃ₗ[Γ(X, V)] Γ(X, V)))
    (hX : ∀ (T : Scheme) (f : T ⟶ B),
      (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.affineOpens) (M : Scheme) (π : M ⟶ Spec Γ(B, U))
    (hfree : ∀ z : M, ∃ V : M.affineOpens, z ∈ V.1 ∧
      Nonempty ((((I.comap U.2.fromSpec).comap π).ideal V) ≃ₗ[Γ(M, V)] Γ(M, V)))
    (hM : ∀ (T : Scheme) (f : T ⟶ Spec Γ(B, U)),
      (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
        Nonempty ((((I.comap U.2.fromSpec).comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! k : T ⟶ M, k ≫ π = f) :
    ∃ e : (p ⁻¹ᵁ U.1).toScheme ≅ M,
      e.hom ≫ π = (p ∣_ U.1) ≫ U.2.isoSpec.hom := by
  let O := (p ⁻¹ᵁ U.1).toScheme
  let q := (p ∣_ U.1) ≫ U.2.isoSpec.hom
  have hO := s2v_l1b_blowup_affine_trivialization p I hcartier U
  obtain ⟨f, hf, _⟩ := hM O q hO
  obtain ⟨g, hg, _⟩ := s2v_l1b_blowup_affine_lift p I hX U M π hfree
  have hfg : f ≫ g = 𝟙 O := by
    obtain ⟨k, hk, hu⟩ := s2v_l1b_blowup_affine_lift p I hX U O q hO
    exact (hu _ (by change (f ≫ g) ≫ q = q; rw [Category.assoc, hg, hf])).trans
      (hu _ (Category.id_comp q)).symm
  have hgf : g ≫ f = 𝟙 M := by
    obtain ⟨k, hk, hu⟩ := hM M π hfree
    exact (hu _ (by change (g ≫ f) ≫ π = π; rw [Category.assoc, hf]; exact hg)).trans
      (hu _ (Category.id_comp π)).symm
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end HodgeLean.Foundations.Program
