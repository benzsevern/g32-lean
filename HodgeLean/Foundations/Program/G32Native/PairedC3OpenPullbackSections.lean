import HodgeLean.Foundations.Program.G32Native.PairedC3PullbackSections

/-! # Invertible canonical pullback sections on an open immersion range -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The restriction-adjunction unit is invertible on every open in the range. -/
theorem paired_c3_open_restrict_unit_isIso {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (V : Y.Opens) (hV : V ≤ f.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app V) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have he : f ''ᵁ f ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have hh : homOfLE (f.image_preimage_le V) = eqToHom he := Subsingleton.elim _ _
  rw [hh]
  infer_instance

/-- The canonical pullback unit is bijective on every open in the immersion range. -/
theorem paired_c3_open_pullback_section_bijective {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (V : Y.Opens) (hV : V ≤ f.opensRange) :
    Function.Bijective (pairedC3PullbackSection f M V) := by
  haveI : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app V) :=
    paired_c3_open_restrict_unit_isIso f M V hV
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction f) (Scheme.Modules.pullbackPushforwardAdjunction f) M
  have ha := congrArg (fun t => t.app V) h
  change ((Scheme.Modules.restrictAdjunction f).unit.app M).app V ≫
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)).app V =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V at ha
  haveI : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V) := by
    rw [← ha]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

#print axioms paired_c3_open_pullback_section_bijective
end HodgeLean.Foundations.Program.G32Native
