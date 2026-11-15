import HodgeLean.Foundations.Program.SchoenTowerL1bUnitCentre
import HodgeLean.Foundations.Program.SchoenTowerL1aIdealOpenRestriction

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The affine section equation for a unit centre suffices for the actual restricted isomorphism. -/
theorem s2v_l1b_blowup_isIso_on_unit_affine
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : X.left, ∃ V : X.left.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.left.affineOpens) (hU : I.ideal U = ⊤) :
    IsIso (p.left ∣_ U.1) := by
  apply s2v_l1b_blowup_isIso_on_unit_open p.left I hcartier
    (s2v_l1b_blowup_scheme_lift B X p I hblowup) U.1
  letI : IsAffine U.1.toScheme := U.2
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [s2v_l1a_open_ideal_top, hU, Ideal.comap_top,
    Scheme.IdealSheafData.ideal_top, Pi.top_apply]

end HodgeLean.Foundations.Program
