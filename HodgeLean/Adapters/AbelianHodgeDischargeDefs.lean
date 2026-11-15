import HodgeLean.Adapters.CupLeftFiltrationAbelian
import HodgeLean.Adapters.LedgerHarvestBetti
import HodgeLean.Adapters.AbelianMilestones

/-! # Definitions for the abelian discharge of `HodgeDecomposition` and `CupFiltered`

One definition, for `docs/briefs/cloud-spec-abl1.md`. Spec doc:
`docs/specs/AbelianHodgeDischarge.md`.

`F1569StatementFor cup` quantifies over proofs `hF : FiniteBetti X`, `hB : BettiDeRhamIso X` and
`hD : HodgeDecomposition X` inside its body. The ledger unfolds root-library definitions when it
reads a milestone's binders, so a milestone that takes `hF1569 : F1569StatementFor cup` is listed
with `HodgeDecomposition` even when it binds no `hD` itself (the trap recorded in
`docs/specs/LedgerHarvestBetti.md`). `F1569StatementForAbelian cup` is the same statement with
those three inner proofs supplied by `finbetti_finiteBetti`, `spec_bettiDeRhamIso_abelian` and
hl5's derivation of `HodgeDecomposition X`. The two are equivalent
(`f1569StatementForAbelian_iff`, in the frozen spec), since the three hypotheses are propositions.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

/-- **F-1569 for a cup-product family, with C1, C2 and C4 supplied.** For every abelian `X` with
`TorusCohomology (cup X)`, every Weil action `A` of type `d = 3` on `H¹` and every member
`(X, A, η)` of `M = (3, ℚ(√−3), [−2])`, the rational Weil classes of `A` are algebraic. This is
`F1569StatementFor cup` with its inner binders `hF`, `hB`, `hD` replaced by the proofs
`finbetti_finiteBetti X`, `spec_bettiDeRhamIso_abelian X` and
`spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
(spec_cupLeft_cupProductOf X)`; every other binder is unchanged. It is a statement, not proved.

Source: F-1569 (register), as for `F1569StatementFor` (`RealDefs/F1569.lean`); C1, C2, C4 through
`finbetti_finiteBetti`, `spec_bettiDeRhamIso_abelian` (batch 60) and hl5's
`spec_cupLeft_cupProductOf` with hlred's `spec_hodgeDecomposition_of_cupLeft_alone`. -/
def F1569StatementForAbelian (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom], CupProduct X) : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [GrpObj X]
    (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X)
        (spec_bettiDeRhamIso_abelian X)
        (spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
          (spec_cupLeft_cupProductOf X)) hT).weight1 3)
    (hW : letI := hT.finite; A.IsWeilType) (η : HQ X 2),
    IsMemberOfM (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
        (spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
          (spec_cupLeft_cupProductOf X)) hT A η →
      WeilClassesAlgebraic (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
        (spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
          (spec_cupLeft_cupProductOf X)) hT A hW

/-- `F1569StatementFor cup` gives `F1569StatementForAbelian cup` by instantiating `hF`, `hB` and
`hD`. -/
example (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom], CupProduct X) (h : F1569StatementFor cup) :
    F1569StatementForAbelian cup :=
  fun X _ _ _ _ hT A hW η hM => h X _ _ _ hT A hW η hM

end HodgeLean.Adapters
