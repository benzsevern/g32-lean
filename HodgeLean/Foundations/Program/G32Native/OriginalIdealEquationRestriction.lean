import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleSectionsHelpers

/-! # Restricting original immersion equations in the actual ideal module

The equation and its section are transported together on the original scheme.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

/-- Restrict an original ideal equation using the specified presheaf map.
Source: naturality of `Scheme.Hom.app`. -/
def originalIdealEquationRestrict
    {Q W : Scheme.{0}} (j : Q ⟶ W) {A B : W.Opens} (hBA : B ≤ A)
    (u : RingHom.ker (j.app A).hom) : RingHom.ker (j.app B).hom := by
  refine ⟨W.presheaf.map (homOfLE hBA).op u.val, ?_⟩
  change j.app B (W.presheaf.map (homOfLE hBA).op u.val) = 0
  rw [← CommRingCat.comp_apply, j.naturality, CommRingCat.comp_apply,
    (show j.app A u.val = 0 from u.property), map_zero]

/-- The restriction retains the actual restricted regular function.
Source: definition of `originalIdealEquationRestrict`. -/
theorem originalIdealEquationRestrict_val
    {Q W : Scheme.{0}} (j : Q ⟶ W) {A B : W.Opens} (hBA : B ≤ A)
    (u : RingHom.ker (j.app A).hom) :
    (originalIdealEquationRestrict j hBA u).val = W.presheaf.map (homOfLE hBA).op u.val := rfl

/-- Restriction of an original equation is still in the original immersion
ideal, and its actual ideal-module section is the restriction of the original
section. No affine presentation or module isomorphism is selected here.
Source: `s2e_idealModule_sections_equiv_restrict` and
`s2e_idealModule_sections_equiv_coe`; Hartshorne, Algebraic Geometry, II.5.
HC no distance; AV milestone no distance. -/
theorem originalIdealEquation_restriction
    {Q W : Scheme.{0}} (j : Q ⟶ W) {A B : W.Opens} (h : B ≤ A)
    (u : RingHom.ker (j.app A).hom) :
    ∃ v : RingHom.ker (j.app B).hom,
      v.val = W.presheaf.map (homOfLE h).op u.val ∧
      (s2c_idealModule j).val.map (homOfLE h).op
        ((s2e_idealModule_sections_equiv j A).symm u) =
        (s2e_idealModule_sections_equiv j B).symm v := by
  let s := (s2e_idealModule_sections_equiv j A).symm u
  let t := (s2c_idealModule j).val.map (homOfLE h).op s
  refine ⟨s2e_idealModule_sections_equiv j B t, ?_, ?_⟩
  · have hv := s2e_idealModule_sections_equiv_restrict j h s
    simpa only [s, LinearEquiv.apply_symm_apply] using hv
  · exact ((s2e_idealModule_sections_equiv j B).symm_apply_apply t).symm

#print axioms originalIdealEquationRestrict_val
#print axioms originalIdealEquation_restriction

end HodgeLean.Foundations.TubularEuler
