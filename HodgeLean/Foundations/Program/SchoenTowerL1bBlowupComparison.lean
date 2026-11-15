import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two models with the retained invertible-ideal mapping property are isomorphic over the base. -/
theorem s2v_l1b_blowup_comparison
    (B X Y : Over (Spec ↧ℂ)) (I : B.left.IdealSheafData)
    (p : X ⟶ B) (q : Y ⟶ B)
    (hp : ∀ x : X.left, ∃ U : X.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap p.left).ideal U) ≃ₗ[Γ(X.left, U)] Γ(X.left, U)))
    (hq : ∀ y : Y.left, ∃ U : Y.left.affineOpens, y ∈ U.1 ∧
      Nonempty (((I.comap q.left).ideal U) ≃ₗ[Γ(Y.left, U)] Γ(Y.left, U)))
    (hX : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ X, u ≫ p = f)
    (hY : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ Y, u ≫ q = f) :
    ∃ e : X ≅ Y, e.hom ≫ q = p ∧ e.inv ≫ p = q := by
  obtain ⟨f, hf, _⟩ := hY X p hp
  obtain ⟨g, hg, _⟩ := hX Y q hq
  have hfg : f ≫ g = 𝟙 X := by
    obtain ⟨k, hk, hu⟩ := hX X p hp
    exact (hu _ (by change (f ≫ g) ≫ p = p; rw [Category.assoc, hg, hf])).trans
      (hu _ (Category.id_comp p)).symm
  have hgf : g ≫ f = 𝟙 Y := by
    obtain ⟨k, hk, hu⟩ := hY Y q hq
    exact (hu _ (by change (g ≫ f) ≫ q = q; rw [Category.assoc, hf, hg])).trans
      (hu _ (Category.id_comp q)).symm
  exact ⟨⟨f, g, hfg, hgf⟩, hf, hg⟩

end HodgeLean.Foundations.Program
