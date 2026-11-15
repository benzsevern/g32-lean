import HodgeLean.Port.Markman.Defs
import HodgeLean.Foundations.InvariantsExteriorBlocks
import HodgeLean.Adapters.PWTheorem42

/-!
# TT v0.15 skeleton: existing vocabulary

The G32 and QI cell conclusions use existing membership and Markman coordinate definitions.
The implication from geometric transfer data, dominance and spreading still lacks vocabulary.
The cell statements below are unasserted propositions, not geometric transfer proofs.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Papers

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

/-- The G32 cell conclusion, as an unasserted statement for the specified action and polarization.
Its proof needs geometric transfer, dominance and spreading.
Source: TT v0.15, Corollary 10.1 (`cor:g32`), first clause, through Theorem 7.1. -/
def TTG32CellStatement
    (w : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : Prop :=
  ∀ (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) w pol),
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) w hM.isWeilType

example
    (w : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) :
    TTG32CellStatement A w pol ↔
  ∀ (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) w pol),
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) w hM.isWeilType := Iff.rfl

/-- The QI cell conclusion as an unasserted coordinate-model statement.
A geometric interpretation requires actual algebraic cycle classes; the implication from
Hypothesis (C), Gale data, dominance and spreading is not yet expressible.
Source: TT v0.15, Corollary 11.1 (`cor:qi`), first conclusion conditional on (C). -/
def TTQICellStatement (Z : WeilClasses.CycleClasses) : Prop :=
  ∀ (B : WeilClasses.AbVar (2 * 3)) (X : WeilClasses.PolarizedWeilType B 1),
    X.DiscIs (-3) → X.toWeilType.HW ≤ Z.alg (2 * 3) B.J

example (Z : WeilClasses.CycleClasses) :
    TTQICellStatement Z ↔
      ∀ (B : WeilClasses.AbVar (2 * 3)) (X : WeilClasses.PolarizedWeilType B 1),
        X.DiscIs (-3) → X.toWeilType.HW ≤ Z.alg (2 * 3) B.J := Iff.rfl

end HodgeLean.Papers
