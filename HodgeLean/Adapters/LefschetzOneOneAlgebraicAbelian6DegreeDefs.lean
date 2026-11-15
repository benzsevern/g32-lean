import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5SquareMaps

/-! # The ordered boundary circuit for the degree split

The parameter interval is `[0,4]`, with one unit interval for each oriented edge.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Adapters
/-- Concatenate the four existing square edges in their specified order.
Source: Hatcher, section 2.2, oriented boundary degree; `bh4_squareEdge`. -/
def bh6_boundaryCircuit (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (t : ℝ) : Fin (dim X.left) → ℂ :=
  if t ≤ 1 then bh4_squareEdge X l m z 0 t
  else if t ≤ 2 then bh4_squareEdge X l m z 1 (t - 1)
  else if t ≤ 3 then bh4_squareEdge X l m z 2 (t - 2)
  else bh4_squareEdge X l m z 3 (t - 3)

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ) :
    bh6_boundaryCircuit X l m z 0 = bh4_squareEdge X l m z 0 0 := by
  simp [bh6_boundaryCircuit]
end HodgeLean.Adapters
