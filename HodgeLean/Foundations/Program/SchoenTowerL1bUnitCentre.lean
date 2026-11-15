import HodgeLean.Foundations.Program.SchoenTowerL1bInvertibleCentre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- No inverse-image points are lost when restricting the retained blowup to an open with unit centre ideal. -/
theorem s2v_l1b_blowup_isIso_on_unit_open
    {B X : Scheme} (p : X ⟶ B) (I : B.IdealSheafData)
    (hcartier : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap p).ideal V) ≃ₗ[Γ(X, V)] Γ(X, V)))
    (hX : ∀ (T : Scheme) (f : T ⟶ B),
      (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.Opens) (hU : I.comap U.ι = ⊤) :
    IsIso (p ∣_ U) := by
  apply s2v_l1b_blowup_isIso_on_invertible_open p I hcartier hX U
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : U.toScheme.Opens) from trivial)
  refine ⟨⟨V, hV⟩, hxV, ?_⟩
  rw [hU, Scheme.IdealSheafData.ideal_top, Pi.top_apply]
  exact ⟨Submodule.topEquiv⟩

end HodgeLean.Foundations.Program
