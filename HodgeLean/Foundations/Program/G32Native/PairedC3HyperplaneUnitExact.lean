import HodgeLean.Foundations.Program.G32Native.PairedC3ModificationUnitLift
import HodgeLean.Foundations.Program.G32Native.PairedConormalPullbackEquivalence
import HodgeLean.Foundations.Program.G32Native.PairedConormalDivisorSequence

/-! # Exactness of the original hyperplane restriction map -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The adjunction-defined restriction is the native structure-module map. -/
theorem paired_c3_subscheme_unit_eq {X Y : Scheme.{0}} (i : X ⟶ Y) :
    pairedC3SubschemeUnit i =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom := by
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    i.toRingCatSheafHom

/-- The actual coordinate-hyperplane restriction is an epimorphism. -/
theorem paired_c3_hyperplane_unit_epi (k : ℕ) (j : Fin (k + 1)) :
    Epi (pairedC3HyperplaneUnit k j) := by
  let i := (HodgeLean.Foundations.Program.s2e_s2b_residueIdeal k j).subschemeι
  haveI : Epi (pairedC3SubschemeUnit i) := by
    rw [paired_c3_subscheme_unit_eq]
    exact (paired_closedImmersion_ideal_shortExact i).epi_g
  let e := HodgeLean.Foundations.Program.s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))
  let F := Scheme.Modules.pullback e.hom
  letI : F.IsEquivalence := conormal_pullback_isEquivalence e
  haveI : Epi (F.map (pairedC3SubschemeUnit i)) := F.map_epi _
  change Epi ((Scheme.Modules.pullbackUnitIso e.hom).inv ≫ F.map (pairedC3SubschemeUnit i))
  infer_instance

#print axioms paired_c3_hyperplane_unit_epi
#print axioms paired_c3_subscheme_unit_eq
end HodgeLean.Foundations.Program.G32Native
