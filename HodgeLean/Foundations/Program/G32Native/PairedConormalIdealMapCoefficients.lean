import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealMapTwisting
import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistLinearUnique
import HodgeLean.Foundations.Program.G32Native.PairedConormalCechSections

/-! # Homogeneous coefficient vectors of actual hyperplane ideal maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

variable (k : ℕ)
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
local notation "I" => Conormal.idealModule (Scheme.IdealSheafData.subschemeι (paired_nativeHyperplaneIdeal k))

/-- The actual ideal map gives a section in the degree-one tensor power. -/
def paired_nativeIdealMapTwistingPowerSection
    (φ : I ⟶ SheafOfModules.unit (X).ringCatSheaf) :
    Γ((ProjSpace.twistingSheaf ℂ k).tensorPow 1, ⊤) :=
  ((ProjSpace.twistingSheaf ℂ k).tensorPowOneIso.inv).val.app (Opposite.op ⊤)
    (paired_nativeIdealMapTwistingSection k φ)

/-- The homogeneous linear coefficients of an actual ideal map exist
uniquely in the original coordinate order. -/
theorem paired_nativeIdealMap_linear_coefficients (hk : 0 < k)
    (φ : I ⟶ SheafOfModules.unit (X).ringCatSheaf) :
    ∃! v : Fin (k + 1) → ℂ,
      paired_twistCochainEquiv ℂ k 1 0
        (Twist.constSec ℂ 1 (paired_twist_linearPolynomial ℂ k v)) =
      pairedCechRestriction (ProjSpace.twistingSectionPresheaf ℂ k 1)
        (ProjSpace.stdCoverPullback (𝟙 X))
        (paired_nativeIdealMapTwistingPowerSection k φ) := by
  let c := pairedCechRestriction (ProjSpace.twistingSectionPresheaf ℂ k 1)
    (ProjSpace.stdCoverPullback (𝟙 X))
    (paired_nativeIdealMapTwistingPowerSection k φ)
  have hc := pairedCechRestriction_cocycle (ProjSpace.twistingSectionPresheaf ℂ k 1)
    (ProjSpace.stdCoverPullback (𝟙 X)) (paired_nativeIdealMapTwistingPowerSection k φ)
  obtain ⟨v, hv⟩ := paired_twisting_zero_cocycle_linear ℂ k hk c hc
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact paired_twisting_linear_coefficients_injective ℂ k (hw.trans hv.symm)

/-- The unique coefficient vector selected from the actual ideal map. -/
def paired_nativeIdealMapCoefficientVector (hk : 0 < k)
    (φ : I ⟶ SheafOfModules.unit (X).ringCatSheaf) : Fin (k + 1) → ℂ :=
  Classical.choose (paired_nativeIdealMap_linear_coefficients k hk φ).exists

/-- Selection retains the actual original twisting cocycle. -/
theorem paired_nativeIdealMapCoefficientVector_spec (hk : 0 < k)
    (φ : I ⟶ SheafOfModules.unit (X).ringCatSheaf) :
    paired_twistCochainEquiv ℂ k 1 0
      (Twist.constSec ℂ 1 (paired_twist_linearPolynomial ℂ k
        (paired_nativeIdealMapCoefficientVector k hk φ))) =
      pairedCechRestriction (ProjSpace.twistingSectionPresheaf ℂ k 1)
        (ProjSpace.stdCoverPullback (𝟙 X))
        (paired_nativeIdealMapTwistingPowerSection k φ) :=
  Classical.choose_spec (paired_nativeIdealMap_linear_coefficients k hk φ).exists

end HodgeLean.Foundations.Program.G32Native
