import HodgeLean.Foundations.Program.G32Native.PairedConormalCoordinateSectionExpansion

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

/-- The relation's specified unit component fixes the first row's original index and scale. -/
theorem paired_nativeRelationCoefficientMatrix_zero_row (hk : 0 < k) (a : ℐ ⟶ 𝒫)
    (ha : a ≫ biprod.snd = kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (paired_nativeHyperplaneIdeal k).subschemeι.toRingCatSheafHom)) :
    paired_nativeRelationCoefficientMatrix k hk a 0 = Pi.single 0 1 := by
  dsimp only [paired_nativeRelationCoefficientMatrix, paired_nativeRelationProjection, Fin.cases_zero]
  exact (congrArg (paired_nativeIdealMapCoefficientVector k hk) ha).trans
    (paired_nativeIdealMapCoefficientVector_inclusion k hk)

end HodgeLean.Foundations.Program.G32Native
