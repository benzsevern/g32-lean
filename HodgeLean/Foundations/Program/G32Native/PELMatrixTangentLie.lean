import HodgeLean.Foundations.MatrixAlgGroupLie
import Mathlib.Algebra.Lie.Semisimple.Defs

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

/-- The matrix tangent space with its commutator Lie structure. -/
def pelMatrixTangentLie (G : MatrixAlgGroup k n) :
    LieSubalgebra k (Matrix (Fin n) (Fin n) k) where
  toSubmodule := g1_lieAlgebra G
  lie_mem' hX hY := g1_lie_mem G _ _ hX hY

end HodgeLean.Foundations.Program.GeneralTypeIII
