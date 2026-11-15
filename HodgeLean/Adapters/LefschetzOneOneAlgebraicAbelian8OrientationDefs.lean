import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Defs

/-! # The ordered period torus

The map is built from the two specified lattice loops. Its top coefficient uses the
existing increasing-coordinate cup basis. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Singular
open Set Topology
open scoped CategoryTheory.MonObj
namespace HodgeLean.Adapters

/-- The translated map of the coordinate two-torus determined by the ordered periods.
Source: Birkenhake--Lange, second edition, section 1.3, exterior cohomology of a torus. -/
def bh8_periodTorus
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ) :
    C(UnitAddTorus (Fin 2), ComplexPoint X) :=
  ⟨fun t ↦ abelianExp X z * abelianLatticeLoop X l (t 0) * abelianLatticeLoop X m (t 1),
    (continuous_const.mul ((abelianLatticeLoop X l).continuous.comp (continuous_apply 0))).mul
      ((abelianLatticeLoop X m).continuous.comp (continuous_apply 1))⟩

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (s t : UnitAddCircle) :
    bh8_periodTorus X l m z ![s, t] =
      abelianExp X z * abelianLatticeLoop X l s * abelianLatticeLoop X m t := rfl

/-- Read the coefficient on the increasing product of the two oriented circle classes.
Source: `torusMonomialBasis`; Hatcher, *Algebraic Topology*, Example 3.11. -/
def bh8_torusCoefficient : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2 →ₗ[ℚ] ℚ :=
  (torusMonomialBasis 2 2).coord (Set.powersetCard.ofCard (by simp :
    (Finset.univ : Finset (Fin 2)).card = 2))

example : bh8_torusCoefficient
    (torusMonomialBasis 2 2 (Set.powersetCard.ofCard (by simp :
      (Finset.univ : Finset (Fin 2)).card = 2))) = 1 := by
  simp only [bh8_torusCoefficient, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

end HodgeLean.Adapters
