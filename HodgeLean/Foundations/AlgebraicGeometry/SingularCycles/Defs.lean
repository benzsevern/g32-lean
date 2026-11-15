import HodgeLean.Adapters.CycleClassFlatPullback
import HodgeLean.Adapters.NormalConeB4Defs

/-! # Generic multiplicities and singular supported cycles

The inverse-image ideal, its generic stalk length, the inverse-image cycle,
and relative singular cohomology retain their existing definitions.
No smoothness is imposed on the ambient spaces in this module.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace AlgebraicGeometry.SingularCycles

/-- Natural coefficient of the fundamental cycle of the scheme-theoretic inverse image.
A finite-length certificate prevents truncation of an infinite extended length.
Source: Fulton, Intersection Theory, second edition, §1.5 and §1.7;
`HodgeLean.Adapters.ccm3_genericLength`. -/
def genericMultiplicity {X Z : Scheme} (f : X ⟶ Z) (x : Z)
    (y : (ccm3_inverseIdeal f x).subscheme)
    (_finiteLength : ccm3_genericLength f x y < ⊤) : ℕ :=
  (ccm3_genericLength f x y).toNat

example {X Z : Scheme} (f : X ⟶ Z) (x : Z)
    (y : (ccm3_inverseIdeal f x).subscheme)
    (h : ccm3_genericLength f x y = 2) : genericMultiplicity f x y (by rw [h]; exact ENat.coe_lt_top 2) = 2 := by
  simp only [genericMultiplicity, h, ENat.toNat_ofNat]

end AlgebraicGeometry.SingularCycles
