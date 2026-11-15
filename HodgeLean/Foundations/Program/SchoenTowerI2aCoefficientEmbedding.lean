import HodgeLean.Foundations.Program.SchoenTowerI2aDeckCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Injective actual affine coefficients at a dominant field point
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual coefficient map of a dominant field point in a reduced scheme is injective.
Source: Mathlib, IsSchemeTheoreticallyDominant.of_isDominant and Scheme.Hom.app_injective. -/
theorem s2v_i2a_field_point_coefficient_injective
    {K : Type*} [Field K] {U : Scheme} [IsReduced U]
    (η : Spec (CommRingCat.of K) ⟶ U) [IsDominant η] :
    Function.Injective (η.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom := by
  haveI : Subsingleton (Spec (CommRingCat.of K)) := by
    change Subsingleton (PrimeSpectrum K)
    infer_instance
  haveI : QuasiCompact η := ⟨fun V _ _ =>
    (show (η ⁻¹' V).Subsingleton from fun _ _ _ _ => Subsingleton.elim _ _).finite.isCompact⟩
  haveI : IsSchemeTheoreticallyDominant η := .of_isDominant η
  have hinj : Function.Injective η.appTop.hom := by
    simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, TopologicalSpace.Opens.map_top] using η.app_injective ⊤
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective.comp hinj

end HodgeLean.Foundations.Program
