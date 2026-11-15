import HodgeLean.Adapters.PWTheorem42Eisenstein

/-! # G34 skeleton vocabulary

Theorems A and B use the actual-cycle vocabulary of `RealDefs.F1569`: positive polarized
Weil actions and `WeilClassesAlgebraic`. The dimension and discriminant components are
bound separately to cover split eightfolds and sixfolds of every discriminant.
The alternative coordinate vocabulary is in `Port.Markman.Defs`, with family-statement
shape in `RealDefs.Compare.Markman`. The G34 geometric proof is not presently composable.
-/

set_option maxHeartbeats 200000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic
open HodgeLean.Adapters

namespace HodgeLean.Papers

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

/-- G34 Theorem A, for split polarized Weil eightfolds, as an unasserted statement in the actual-cycle vocabulary.
The polarization and rational Hodge action use the components of `IsMemberOfM`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem A. -/
def G34TheoremAStatement : Prop :=
  ∀ (W : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
    (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
    (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (_hDim : TopologicalSpace.dim A.left = 8)
    (_hDisc : weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hη hRos = 1),
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW

example : G34TheoremAStatement A ↔
    (∀ (W : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
    (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
    (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (_hDim : TopologicalSpace.dim A.left = 8)
    (_hDisc : weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hη hRos = 1),
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) := Iff.rfl

/-- G34 Theorem B, for polarized Weil sixfolds of every discriminant, as an unasserted statement in the actual-cycle vocabulary.
The polarization and rational Hodge action use the components of `IsMemberOfM`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem B. -/
def G34TheoremBStatement : Prop :=
  ∀ (W : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
    (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (_hRos : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
    (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (_hDim : TopologicalSpace.dim A.left = 6),
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW

example : G34TheoremBStatement A ↔
    (∀ (W : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
    (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (_hRos : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
    (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (_hDim : TopologicalSpace.dim A.left = 6),
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) := Iff.rfl

end HodgeLean.Papers
