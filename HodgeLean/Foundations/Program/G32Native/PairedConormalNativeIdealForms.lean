import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealCoefficients
import HodgeLean.Foundations.Program.G32Native.PairedConormalCoefficientPolynomials

/-! # Homogeneous linear forms extracted from actual projective ideal maps -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (k : ℕ)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (k + 1)) K
local notation "P" => Proj 𝒜

/-- The original affine coordinate open, with its verified affineness. -/
def conormalNativeCoordinateOpen (i : Fin (k + 1)) : (P).affineOpens :=
  ⟨ProjSpace.standardOpen K k i, (ProjSpace.stdCover K k).isAffineOpen (ULift.up i)⟩

/-- The actual overlap of two original affine coordinate opens. -/
def conormalNativeCoordinateOverlap (i j : Fin (k + 1)) : (P).affineOpens :=
  ⟨ProjSpace.standardOpen K k i ⊓ ProjSpace.standardOpen K k j,
    Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated (ProjSpace.π K k)
      (conormalNativeCoordinateOpen K k i).property (conormalNativeCoordinateOpen K k j).property⟩

/-- An actual ideal-module map gives one homogeneous linear form in its normalized coordinate generators. -/
theorem conormal_native_ideal_map_linear_form (hk : 1 ≤ k)
    (I : (P).IdealSheafData)
    (hm : ∀ i : Fin (k + 1), ProjSpace.coordinateRatioSection K k i 0 ∈
      I.ideal (conormalNativeCoordinateOpen K k i))
    (φ : idealModule I ⟶ SheafOfModules.unit (P).ringCatSheaf) :
    ∃ p : 𝒜 1, ∀ i : Fin (k + 1),
      conormalIdealMapCoefficient I φ (conormalNativeCoordinateOpen K k i)
        (ProjSpace.coordinateRatioSection K k i 0) (hm i) =
      ProjSpace.homogeneousRatioSection K k 1 p i := by
  let c (i : Fin (k + 1)) := conormalIdealMapCoefficient I φ
    (conormalNativeCoordinateOpen K k i) (ProjSpace.coordinateRatioSection K k i 0) (hm i)
  apply conormal_twisting_coefficients_linear_polynomial K k hk c
  intro i j
  exact conormalIdealMapCoefficient_transition I φ
    (conormalNativeCoordinateOpen K k i) (conormalNativeCoordinateOpen K k j)
    (conormalNativeCoordinateOverlap K k i j)
    (by change ProjSpace.standardOpen K k i ⊓ ProjSpace.standardOpen K k j ≤ _; exact inf_le_left)
    (by change ProjSpace.standardOpen K k i ⊓ ProjSpace.standardOpen K k j ≤ _; exact inf_le_right)
    (ProjSpace.coordinateRatioSection K k i 0) (hm i)
    (ProjSpace.coordinateRatioSection K k j 0) (hm j)
    ((P).presheaf.map (homOfLE inf_le_left).op (ProjSpace.coordinateRatioSection K k i j))
    (ProjSpace.coordinateRatioSection_mul K k i j 0 inf_le_left inf_le_right).symm

end HodgeLean.Foundations.Program.G32Native
