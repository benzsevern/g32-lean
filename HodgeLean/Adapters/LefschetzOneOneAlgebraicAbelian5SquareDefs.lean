import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5Defs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelianDefs
import HodgeLean.RealDefs.ComplexFundamentalClass
import HodgeLean.RealDefs.FundamentalClass.Chart

/-! # A topological carrier for period-square evaluation

The oriented disk class is defined by the existing convex-support homology equivalence.
The clamped affine map sends the complement of this disk to the square boundary.
No cohomological comparison is part of these definitions.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular Set Topology
open HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- Coordinate clamping to the unit interval.
Source: the standard retraction of the real line onto a closed interval. -/
def bh5_clamp (t : ℝ) : ℝ := max 0 (min 1 t)

example : bh5_clamp 0 = 0 := by norm_num [bh5_clamp]

/-- The affine square map, extended to the complex plane by coordinate clamping.
Source: Hatcher, *Algebraic Topology*, section 3.3, oriented relative evaluation. -/
def bh5_squareMap (n : ℕ) (l m z : Fin n → ℂ) : C((Fin 1 → ℂ), (Fin n → ℂ)) :=
  ⟨fun q ↦ z + bh5_clamp (((q 0).re + 1) / 2) • l +
    bh5_clamp (((q 0).im + 1) / 2) • m, by unfold bh5_clamp; fun_prop⟩

example : bh5_squareMap 1 0 0 0 0 = 0 := by simp [bh5_squareMap]
example : bh5_squareMap 2 0 0 0 0 = 0 := by simp [bh5_squareMap]

/-- The relative plane/disk pair carrying the square parameterization.
Source: Hatcher, section 3.3, homology along a compact convex support. -/
def bh5_diskPair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (Fin 1 → ℂ)) (Metric.closedBall 0 2)ᶜ

example : bh5_diskPair =
    TopPair.ofSubset (X := TopCat.of (Fin 1 → ℂ)) (Metric.closedBall 0 2)ᶜ := rfl

/-- The disk's complex orientation, transported from local homology at its center.
Source: `j5c_convex_restrict_bijective`; the standard complex local orientation. -/
def bh5_diskClass : RelativeHomology ℚ bh5_diskPair 2 :=
  (Equiv.ofBijective _ (j5c_convex_restrict_bijective
    (convex_closedBall (0 : Fin 1 → ℂ) (2 : ℝ)) (isCompact_closedBall 0 2)
    (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)) 2)).symm
      (standardComplexLocalClass ℚ 1)

example : relativeHomologyMap ℚ 2
    (supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
      (Set.singleton_subset_iff.mpr
        (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)))) bh5_diskClass =
      standardComplexLocalClass ℚ 1 :=
  by
    exact (Equiv.ofBijective _ (j5c_convex_restrict_bijective
      (convex_closedBall (0 : Fin 1 → ℂ) (2 : ℝ)) (isCompact_closedBall 0 2)
      (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)) 2)).apply_symm_apply _

end HodgeLean.Adapters
