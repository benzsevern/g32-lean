import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Witnesses

/-! # Stage-eight leaves applied to the constructed witnesses

The witnesses are in `LefschetzOneOneAlgebraicAbelian8Witnesses`.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Curves HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Filter Set Topology
open scoped CategoryTheory.MonObj
namespace HodgeLean.Adapters

attribute [local instance] bh8_cubic_comm

example := bh8_singular_restriction_aux (dim E.left) bh8_cubicWitness.f
  bh8_cubicWitness.analytic bh8_cubicWitness.reduced
example := bh8_singular_restriction_aux (dim (g3_power E 2).left) bh8_productWitness.f
  bh8_productWitness.analytic bh8_productWitness.reduced

example := bh8_regular_normalization_aux E bh8_cubicWitness.x bh8_cubicWitness.codim
  bh8_cubicWitness.f bh8_cubicWitness.analytic bh8_cubicWitness.reduced bh8_cubicWitness.support
example := bh8_regular_normalization_aux (g3_power E 2) bh8_productWitness.x bh8_productWitness.codim
  bh8_productWitness.f bh8_productWitness.analytic bh8_productWitness.reduced bh8_productWitness.support

example := bh8_supported_pullback_aux E bh8_cubicWitness.x bh8_cubicWitness.codim
  bh8_cubicWitness.f bh8_cubicWitness.analytic bh8_cubicWitness.reduced bh8_cubicWitness.support
  0 0 bh8_cubicWitness.point (bh8_witness_boundary E bh8_cubicWitness).1
  (bh8_witness_boundary E bh8_cubicWitness).2
example := bh8_supported_pullback_aux (g3_power E 2) bh8_productWitness.x bh8_productWitness.codim
  bh8_productWitness.f bh8_productWitness.analytic bh8_productWitness.reduced bh8_productWitness.support
  0 0 bh8_productWitness.point (bh8_witness_boundary (g3_power E 2) bh8_productWitness).1
  (bh8_witness_boundary (g3_power E 2) bh8_productWitness).2

example := bh8_period_coefficient_aux E
  (abelianLatticeBasis E ⟨0, by rw [E_dim]; decide⟩)
  (abelianLatticeBasis E ⟨1, by rw [E_dim]; decide⟩)
  0 (cycleComponentSheafClass E bh8_cubicWitness.x bh8_cubicWitness.codim)

#print axioms bh8_cubicWitness
#print axioms bh8_productWitness
end HodgeLean.Adapters
