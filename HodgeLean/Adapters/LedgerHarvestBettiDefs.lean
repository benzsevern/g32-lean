import HodgeLean.Adapters.F1575
import HodgeLean.RealDefs.FiniteBettiCompact

/-! # Definitions for ledger harvest 2: `FiniteBetti X` supplied

One definition, for `docs/briefs/cloud-spec-harvest2.md`. Spec doc:
`docs/specs/LedgerHarvestBetti.md`.

`F1569StatementFor cup` quantifies over a proof `hF : FiniteBetti X` inside its body. The ledger
unfolds root-library definitions when it reads a milestone's binders, so a milestone that takes
`hF1569 : F1569StatementFor cup` is listed with `FiniteBetti` even when it binds no `hF` itself.
`F1569StatementForBetti cup` is the same statement with that inner proof supplied by
`finbetti_finiteBetti`. The two are equivalent (`harvestBetti_f1569StatementForBetti_iff`, in the
frozen spec), since `FiniteBetti X` is a proposition. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- **F-1569 for a cup-product family, with finite Betti numbers supplied.** For every abelian
`X`, every Weil action `A` of type `d = 3` on `H¹` and every member `(X, A, η)` of
`M = (3, ℚ(√−3), [−2])`, the rational Weil classes of `A` are algebraic. This is
`F1569StatementFor cup` with its inner binder `hF : FiniteBetti X` replaced by the proof
`finbetti_finiteBetti X`; every other binder is unchanged.

Source: F-1569 (register), as for `F1569StatementFor` (`RealDefs/F1569.lean`); finite Betti
numbers by Hatcher, *Algebraic Topology*, Appendix, Corollary A.8 and Theorem 3.2, through
`finbetti_finiteBetti` (`RealDefs/FiniteBettiCompact.lean`). -/
def F1569StatementForBetti (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom], CupProduct X) : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [GrpObj X]
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        3)
    (hW : letI := hT.finite; A.IsWeilType) (η : HQ X 2),
    IsMemberOfM (finbetti_finiteBetti X) hB hD hT A η →
      WeilClassesAlgebraic (finbetti_finiteBetti X) hB hD hT A hW

/-- `F1569StatementFor cup` gives `F1569StatementForBetti cup` by instantiating its `hF`. -/
example (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom], CupProduct X) (h : F1569StatementFor cup) :
    F1569StatementForBetti cup :=
  fun X _ _ _ _ hB hD hT A hW η hM => h X (finbetti_finiteBetti X) hB hD hT A hW η hM

end HodgeLean.Adapters
