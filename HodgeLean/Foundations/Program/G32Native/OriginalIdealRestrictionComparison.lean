import HodgeLean.Foundations.Program.SchoenCycleC2OpenIdealRestrictionHelpers

/-! # Original ideal inclusions under ambient open restriction

The existing restriction isomorphism is compared with the kernel inclusion,
so it retains actual equations rather than an arbitrary module isomorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual ideal restriction isomorphism preserves its inclusion into the
original structure module.
Source: Hartshorne, Algebraic Geometry, II.5, restriction of kernels;
`PreservesKernel.iso` and `kernel.mapIso`.
HC no distance; AV milestone no distance. -/
theorem original_ideal_restriction_inclusion
    {Q W : Scheme.{0}} (j : Q ⟶ W) (U : W.Opens) :
    (s2e_idealModule_restrict_iso j U).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (j ∣_ U).toRingCatSheafHom) =
      (Scheme.Modules.restrictFunctor U.ι).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom := by
  simp [s2e_idealModule_restrict_iso, Category.assoc]

#print axioms original_ideal_restriction_inclusion

end HodgeLean.Foundations.Program
