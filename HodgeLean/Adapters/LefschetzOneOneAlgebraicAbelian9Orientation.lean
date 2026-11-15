import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian9OrientationProofs

/-! # The universal ordered torus cell

This comparison uses the fixed coordinate torus and its coordinate circles. Transport to
an abelian variety's support pair is a further step. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Adapters

/-- The ordered torus coefficient is evaluation on the clamped relative square.
Source: Hatcher, Algebraic Topology, section 2.2 and Example 3.11, the oriented
square cell and the increasing product of its two degree-one generators. -/
theorem bh9_torus_cell (a : RelativeCohomology ℚ bh9_torusPair 2) :
    bh8_torusCoefficient (relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a) =
      relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
        (relativeCohomologyMap ℚ 2 bh9_squareTorusMap a) bh5_diskClass :=
  bh9_torus_cell_aux a

example :
    bh8_torusCoefficient (relativeCohomologyToAbsolute ℚ bh9_torusPair 2 0) =
      relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
        (relativeCohomologyMap ℚ 2 bh9_squareTorusMap 0) bh5_diskClass :=
  bh9_torus_cell 0

open HodgeLean.Foundations.Singular in
example : bh8_torusCoefficient
    (torusMonomialBasis 2 2 (Set.powersetCard.ofCard (by simp :
      (Finset.univ : Finset (Fin 2)).card = 2))) = 1 := by
  simp only [bh8_torusCoefficient, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

end HodgeLean.Adapters
