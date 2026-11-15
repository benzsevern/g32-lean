import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeIdealForms
import HodgeLean.Foundations.Program.G32Native.PairedConormalVanishingMembership
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafLocalization

/-! # Actual linear forms of the reduced native coordinate hyperplane ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (k : ℕ)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (k + 1)) K
local notation "P" => Proj 𝒜

/-- The actual reduced hyperplane defined by vanishing of homogeneous coordinate zero. -/
def conormalNativeHyperplaneIdeal : (P).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(ProjSpace.standardOpen K k 0).carrierᶜ,
      (ProjSpace.standardOpen K k 0).isOpen.isClosed_compl⟩

/-- The normalized coordinate equation lies in the actual reduced hyperplane ideal on each chart. -/
theorem conormal_native_hyperplane_coordinate_mem (i : Fin (k + 1)) :
    ProjSpace.coordinateRatioSection K k i 0 ∈
      (conormalNativeHyperplaneIdeal K k).ideal (conormalNativeCoordinateOpen K k i) := by
  apply conormal_mem_vanishingIdeal_of_basicOpen
  intro x hx hb
  rw [ProjSpace.coordinateRatioSection_basicOpen] at hb
  exact hx hb.2

/-- Every map from the actual reduced hyperplane ideal has a homogeneous linear numerator. -/
theorem conormal_native_hyperplane_map_linear_form (hk : 1 ≤ k)
    (φ : idealModule (conormalNativeHyperplaneIdeal K k) ⟶
      SheafOfModules.unit (P).ringCatSheaf) :
    ∃ p : 𝒜 1, ∀ i : Fin (k + 1),
      conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal K k) φ
        (conormalNativeCoordinateOpen K k i) (ProjSpace.coordinateRatioSection K k i 0)
        (conormal_native_hyperplane_coordinate_mem K k i) =
      ProjSpace.homogeneousRatioSection K k 1 p i := by
  exact conormal_native_ideal_map_linear_form K k hk (conormalNativeHyperplaneIdeal K k)
    (conormal_native_hyperplane_coordinate_mem K k) φ

end HodgeLean.Foundations.Program.G32Native
