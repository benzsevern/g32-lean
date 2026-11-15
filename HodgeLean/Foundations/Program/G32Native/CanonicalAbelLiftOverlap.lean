import HodgeLean.Foundations.Program.G32Native.CanonicalAbelValue
import HodgeLean.Foundations.Program.G32Native.LocalModelOverlap

/-! # Original local Abel lifts on actual ambient overlaps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified original Abel lift read in its specified original
ambient chart, with its original coefficient values. -/
def canonicalChartAbelLift (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q) (w : ComplexPoint G.W) : Fin (G.k + 1) → ℂ :=
  F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)

#print axioms canonicalChartAbelLift
end HodgeLean.Foundations.Program.G32Native
