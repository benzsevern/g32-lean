import HodgeLean.Foundations.Program.G32Native.PairedResidualRelativeSmooth
import Mathlib.RingTheory.LocalRing.Module

/-! # Relative smoothness detected on the original residue differential -/
noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Injectivity on residue differentials gives relative formal smoothness
for a local absolute smooth algebra with finite differential modules.
Source: Stacks Project, Tags 00S2 and 00TI; Nakayama's lemma. -/
theorem residual_local_formallySmooth_of_residue_differential
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [IsLocalRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]
    [Module.Finite S Ω[S⁄R]] [Module.Finite T Ω[T⁄R]]
    (h : Function.Injective
      ((KaehlerDifferential.mapBaseChange R S T).lTensor (IsLocalRing.ResidueField T))) :
    Algebra.FormallySmooth S T := by
  letI : Module.Free T Ω[T⁄R] := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective
      (KaehlerDifferential.mapBaseChange R S T)).mpr h
  exact residual_formallySmooth_of_differential_retraction R S T s hs

#print axioms residual_local_formallySmooth_of_residue_differential
end HodgeLean.Foundations.Program.G32Native
