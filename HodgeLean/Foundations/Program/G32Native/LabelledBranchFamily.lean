import HodgeLean.Ported.Hironaka.Scheme.Snc.Defs
import Mathlib.Data.Fintype.EquivFin

/-! Supply an auxiliary finite order while retaining the literal branch labels and ideals. -/
noncomputable section
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Regard a finite labelled branch function as a divisor family without changing its labels. -/
def g32l4_labelledBranchFamily {X : Scheme} {ι : Type} [Fintype ι]
    (D : ι → X.IdealSheafData) : Scheme.DivisorFamily X where
  ι := ι
  fintype := inferInstance
  linearOrder := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  component := D

end HodgeLean.Foundations.Program
