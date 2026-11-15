import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericStalk

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The spectrum of any stalk of an integral scheme maps dominantly to that scheme. -/
theorem s2v_l1b_divisor_stalk_spectrum_dominant
    (X : Scheme.{0}) [IsIntegral X] (x : X) : IsDominant (X.fromSpecStalk x) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec X).def]
  apply closure_mono
  rintro y rfl
  rw [Scheme.range_fromSpecStalk]
  exact genericPoint_specializes x

/-- A dominant map of integral schemes has injective stalk maps without a compactness requirement. -/
theorem s2v_l1b_divisor_dominant_stalk_injective
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) : Function.Injective (f.stalkMap x).hom := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply (s2v_l1b_functionFieldPullback f).hom.injective
  rw [s2v_l1b_divisor_generic_stalk, s2v_l1b_divisor_generic_stalk, hab]

/-- The canonical map from a stalk spectrum induces isomorphisms on all its stalks. -/
theorem s2v_l1b_divisor_stalk_spectrum_stalkMap_isIso
    (X : Scheme.{0}) [IsIntegral X] (x : X) (z : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap z) := by
  letI : IsDominant (X.fromSpecStalk x) := s2v_l1b_divisor_stalk_spectrum_dominant X x
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨s2v_l1b_divisor_dominant_stalk_injective (X.fromSpecStalk x) z,
    (X.fromSpecStalk x).stalkMap_surjective z⟩

/-- The canonical stalk spectrum preserves the codimension of each of its points. -/
theorem s2v_l1b_divisor_stalk_spectrum_coheight
    (X : Scheme.{0}) [IsIntegral X] (x : X) (z : Spec (X.presheaf.stalk x)) :
    Order.coheight ((X.fromSpecStalk x) z) = Order.coheight z := by
  letI := s2v_l1b_divisor_stalk_spectrum_stalkMap_isIso X x z
  have H := ringKrullDim_eq_of_ringEquiv
    (asIso ((X.fromSpecStalk x).stalkMap z)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at H
  exact WithBot.coe_injective H

end HodgeLean.Foundations.Program
