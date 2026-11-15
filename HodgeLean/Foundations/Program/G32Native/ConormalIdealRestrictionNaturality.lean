import HodgeLean.Foundations.Program.SchoenCycleC2OpenIdealRestrictionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleSectionsHelpers

/-! # Naturality of the original ideal sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

/-- Restriction of the ideal section retains the specified original equation. -/
theorem originalIdealSection_restrict
    {Q W : Scheme.{0}} (j : Q ⟶ W) {A B : W.Opens} (hBA : B ≤ A)
    (u : RingHom.ker (j.app A).hom) (v : RingHom.ker (j.app B).hom)
    (hv : v.val = W.presheaf.map (homOfLE hBA).op u.val) :
    (s2c_idealModule j).val.map (homOfLE hBA).op
        ((s2e_idealModule_sections_equiv j A).symm u) =
      (s2e_idealModule_sections_equiv j B).symm v := by
  apply (s2e_idealModule_sections_equiv j B).injective
  apply Subtype.ext
  rw [LinearEquiv.apply_symm_apply, s2e_idealModule_sections_equiv_restrict,
    LinearEquiv.apply_symm_apply, hv]

end HodgeLean.Foundations.TubularEuler
