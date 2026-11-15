import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealMapCoefficients
import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealMapChecks
import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeCoordinateProjection

/-! # Coefficients of the supplied ideal-to-free relation map -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

/-- Original scalar-first coordinates on the actual stabilized free module. -/
def paired_nativeRelationProjection (i : Fin (k + 1)) : 𝒫 ⟶ 𝒪 :=
  Fin.cases biprod.snd (fun j => biprod.fst ≫ paired_freeCoordinateProjection
    (𝒳).ringCatSheaf j) i

/-- Each row is selected from the corresponding component of the supplied relation map. -/
def paired_nativeRelationCoefficientMatrix (hk : 0 < k) (a : ℐ ⟶ 𝒫) :
    Fin (k + 1) → Fin (k + 1) → ℂ :=
  fun i => paired_nativeIdealMapCoefficientVector k hk
    (a ≫ paired_nativeRelationProjection k i)

/-- Every row retains the actual original ideal-map twisting cocycle. -/
theorem paired_nativeRelationCoefficientMatrix_row (hk : 0 < k) (a : ℐ ⟶ 𝒫)
    (i : Fin (k + 1)) :
    paired_twistCochainEquiv ℂ k 1 0
      (Twist.constSec ℂ 1 (paired_twist_linearPolynomial ℂ k
        (paired_nativeRelationCoefficientMatrix k hk a i))) =
      pairedCechRestriction (ProjSpace.twistingSectionPresheaf ℂ k 1)
        (ProjSpace.stdCoverPullback (𝟙 𝒳))
        (paired_nativeIdealMapTwistingPowerSection k
          (a ≫ paired_nativeRelationProjection k i)) :=
  paired_nativeIdealMapCoefficientVector_spec k hk (a ≫ paired_nativeRelationProjection k i)

/-- The relation's prescribed unit component retains coordinate zero with its original scale. -/
theorem paired_nativeRelation_scalar_section (a : ℐ ⟶ 𝒫)
    (ha : a ≫ biprod.snd = kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (paired_nativeHyperplaneIdeal k).subschemeι.toRingCatSheafHom)) :
    paired_nativeIdealMapTwistingSection k (a ≫ paired_nativeRelationProjection k 0) =
      ProjSpace.twistingCoordinateSection ℂ k 0 := by
  change paired_nativeIdealMapTwistingSection k (a ≫ biprod.snd) = _
  rw [ha]
  exact paired_nativeIdealMapTwistingSection_inclusion k

/-- The coefficient system acts linearly on the original homogeneous vector space. -/
def paired_nativeRelationCoefficientLinearMap (hk : 0 < k) (a : ℐ ⟶ 𝒫) :
    (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ) :=
  LinearMap.pi (fun i => ∑ j : Fin (k + 1),
    paired_nativeRelationCoefficientMatrix k hk a i j • LinearMap.proj j)

/-- Evaluation retains the supplied row and column indices. -/
theorem paired_nativeRelationCoefficientLinearMap_apply (hk : 0 < k) (a : ℐ ⟶ 𝒫)
    (x : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    paired_nativeRelationCoefficientLinearMap k hk a x i =
      ∑ j, paired_nativeRelationCoefficientMatrix k hk a i j * x j := by
  simp only [paired_nativeRelationCoefficientLinearMap, LinearMap.pi_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

end HodgeLean.Foundations.Program.G32Native
