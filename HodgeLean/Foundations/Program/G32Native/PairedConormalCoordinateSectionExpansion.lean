import HodgeLean.Foundations.Program.G32Native.PairedConormalRelationCoefficients
import HodgeLean.Foundations.Program.G32Native.PairedConormalLinearCoordinateCocycle
import HodgeLean.Foundations.Program.G32Native.PairedConormalTensorPowerOne

/-! # Actual coordinate-section expansions of the supplied relation map -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

variable (k : ℕ)
local notation "𝒳" => Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
local notation "ℐ" => Conormal.idealModule
  (Scheme.IdealSheafData.subschemeι (paired_nativeHyperplaneIdeal k))
local notation "𝒪" => SheafOfModules.unit (Scheme.ringCatSheaf 𝒳)
local notation "𝒫" => (SheafOfModules.free (R := Scheme.ringCatSheaf 𝒳) (Fin k)) ⊞ 𝒪

/-- The actual supplied ideal map has its original coordinate-section expansion. -/
theorem paired_nativeIdealMap_coordinate_cocycle (hk : 0 < k) (φ : ℐ ⟶ 𝒪) :
    pairedCechRestriction (ProjSpace.twistingSectionPresheaf ℂ k 1)
      (ProjSpace.stdCoverPullback (𝟙 𝒳))
      (paired_nativeIdealMapTwistingPowerSection k φ) =
    ∑ j : Fin (k + 1), paired_nativeIdealMapCoefficientVector k hk φ j •
      pairedCechRestriction (ProjSpace.twistingSectionPresheaf ℂ k 1)
        (ProjSpace.stdCoverPullback (𝟙 𝒳))
        (tensorPowSection (X := 𝒳) (L := ProjSpace.twistingSheaf ℂ k) (U := ⊤) (ProjSpace.twistingCoordinateSection ℂ k j) 1) :=
  (paired_nativeIdealMapCoefficientVector_spec k hk φ).symm.trans
    (paired_twisting_linear_cocycle_coordinates ℂ k
      (paired_nativeIdealMapCoefficientVector k hk φ))

/-- The original ideal inclusion has the original coordinate-zero coefficient vector. -/
theorem paired_nativeIdealMapCoefficientVector_inclusion (hk : 0 < k) :
    paired_nativeIdealMapCoefficientVector k hk
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (paired_nativeHyperplaneIdeal k).subschemeι.toRingCatSheafHom)) =
      Pi.single 0 1 := by
  apply paired_twisting_linear_coefficients_injective ℂ k
  let inc := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (paired_nativeHyperplaneIdeal k).subschemeι.toRingCatSheafHom)
  have hsec : paired_nativeIdealMapTwistingPowerSection k inc =
      tensorPowSection (X := 𝒳) (L := ProjSpace.twistingSheaf ℂ k) (U := ⊤) (ProjSpace.twistingCoordinateSection ℂ k 0) 1 := by
    exact (paired_tensorPowOneIso_inv_section (X := 𝒳) (ProjSpace.twistingSheaf ℂ k) ⊤
      (paired_nativeIdealMapTwistingSection k inc)).trans
        (congrArg (fun s : Γ(ProjSpace.twistingSheaf ℂ k, ⊤) => tensorPowSection (X := 𝒳) (L := ProjSpace.twistingSheaf ℂ k) (U := ⊤) s 1)
          (paired_nativeIdealMapTwistingSection_inclusion k))

  have hleft := paired_nativeIdealMapCoefficientVector_spec k hk inc
  have hmid := congrArg (pairedCechRestriction (ProjSpace.twistingSectionPresheaf ℂ k 1)
    (ProjSpace.stdCoverPullback (𝟙 𝒳))) hsec
  have hright := (congrArg (fun g => paired_twistCochainEquiv ℂ k 1 0
      (Twist.constSec ℂ 1 g)) (paired_twist_linearPolynomial_single ℂ k 0)).trans
    (paired_twist_coordinateCochain_actual ℂ k 0)
  exact hleft.trans (hmid.trans hright.symm)


end HodgeLean.Foundations.Program.G32Native
