import HodgeLean.Foundations.Program.SchoenTransferC1a6Defs
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-! Integral domain for the period comparison: actual singular homology modulo torsion.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
/-- Integral singular degree-one homology of the complex-point space.
Source: Hatcher, Algebraic Topology, §2.1, singular homology. -/
abbrev s4_c1a6_integralH1 (Y : Over (Spec ↧ℂ)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ComplexPoint Y) : TopCat.{0})

example := s4_c1a6_integralH1

/-- The integral singular group modulo its actual torsion submodule.
Source: Hatcher, Algebraic Topology, §3.1; Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4. -/
abbrev s4_c1a6_integralLattice (Y : Over (Spec ↧ℂ)) :=
  s4_c1a6_integralH1 Y ⧸ Submodule.torsion ℤ (s4_c1a6_integralH1 Y)

example := s4_c1a6_integralLattice
end HodgeLean.Foundations.Program
