import HodgeLean.Adapters.LedgerHarvestBettiDefs

/-! # Proof obligations for ledger harvest 2 (`FiniteBetti X` supplied)

One obligation per statement of `HodgeLean.Adapters.LedgerHarvestBetti`. All fourteen are proved, by two parallel provers. Spec doc:
`docs/specs/LedgerHarvestBetti.md`.

Intended route, for every obligation: apply the original declaration, with its `hF` argument
`finbetti_finiteBetti X` (`RealDefs/FiniteBettiCompact.lean`) and every other argument passed
through. `FiniteBetti X` is a proposition, so the types agree by proof irrelevance. The two
F-1569 milestones first turn `F1569StatementForBetti cup` into `F1569StatementFor cup`, by the
equivalence (its forward direction: given `hF`, apply the hypothesis; the inner types agree by
proof irrelevance). -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X} [GrpObj X]

theorem harvestBetti_f1569StatementForBetti_iff_aux
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) :
    F1569StatementForBetti cup ↔ F1569StatementFor cup := by
  exact ⟨fun h X _ _ _ _ _ hB hD hT A hW η hM => h X hB hD hT A hW η hM,
    fun h X _ _ _ _ hB hD hT A hW η hM => h X (finbetti_finiteBetti X) hB hD hT A hW η hM⟩

theorem harvestBetti_hdg_le_span_of_hodgeConjectureFor_aux
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (h : letI := hT.finite
      HodgeBlocks.HodgeConjectureFor (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT)
        (fun {m} => isAlgebraicOf μ (m := m))) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_of_hodgeConjectureFor (finbetti_finiteBetti X) hB hD hT h

theorem harvestBetti_hdg_le_span_abelian_g1_aux (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hH : CycleClassIsHodge X) (h11 : LefschetzOneOneHyp) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_abelian_g1 (finbetti_finiteBetti X) hB hD hT hH h11 hg

theorem harvestBetti_hdg_le_span_abelian_g2_aux (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (h11 : LefschetzOneOneHyp) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_abelian_g2 (finbetti_finiteBetti X) hB hD hT hM hH hA hL h11 hg

theorem harvestBetti_hdg_le_span_abelian_g3_aux (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hC : CupFiltered X μ) (h11 : LefschetzOneOneHyp)
    (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_abelian_g3 (finbetti_finiteBetti X) hB hD hT hM hH hA hL hC h11 hg

theorem harvestBetti_weilClassOf_le_hdg_aux (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hC : CupFiltered X μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        d)
    (hW : letI := hT.finite; A.IsWeilType) :
    letI := hT.finite
    weilClassOf (finbetti_finiteBetti X) hB hD hT A hW ≤ Hdg^(Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1.H
        (1, 0)))(X; ℚ) := by
  exact weilClassOf_le_hdg (finbetti_finiteBetti X) hB hD hT hC A hW

theorem harvestBetti_hdg_le_span_of_weilClassesAlgebraic_aux
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        d)
    (hW : letI := hT.finite; A.IsWeilType)
    (hWA : WeilClassesAlgebraic (finbetti_finiteBetti X) hB hD hT A hW)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil (finbetti_finiteBetti X) hB hD hT A hW)
    (hM : CycleClassMultiplicative μ) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_of_weilClassesAlgebraic (finbetti_finiteBetti X) hB hD hT A hW hWA hGen hM h11

theorem harvestBetti_hdg_le_span_of_f1569Statement_aux
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementForBetti cup)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        3)
    {η : HQ X 2} (hM : IsMemberOfM (finbetti_finiteBetti X) hB hD hT A η)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil (finbetti_finiteBetti X) hB hD hT A
      hM.isWeilType)
    (hC9 : CycleClassMultiplicative (cup X)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_of_f1569Statement cup
    ((harvestBetti_f1569StatementForBetti_iff_aux cup).mp hF1569)
    (finbetti_finiteBetti X) hB hD hT A hM hGen hC9 h11

theorem harvestBetti_hdg_le_span_of_f1569Statement_of_hSU_aux
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementForBetti cup)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        3)
    {η : HQ X 2} (hM : IsMemberOfM (finbetti_finiteBetti X) hB hD hT A η)
    (hC : CupFiltered X (cup X))
    (hSU : F1575MemberHodgeGroupIsSU (finbetti_finiteBetti X) hB hD hT A hM)
    (hC9 : CycleClassMultiplicative (cup X)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_of_f1569Statement_of_hSU cup
    ((harvestBetti_f1569StatementForBetti_iff_aux cup).mp hF1569)
    (finbetti_finiteBetti X) hB hD hT A hM hC hSU hC9 h11

theorem harvestBetti_isExteriorOfWeightOne_of_cupFiltered_aux
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hC : CupFiltered X μ) :
    letI := hT.finite
    AbelianVarietyCohomology.IsExteriorOfWeightOne
      (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT) :=
  isExteriorOfWeightOne_of_cupFiltered (finbetti_finiteBetti X) hB hD hT hC

theorem harvestBetti_cycleClassPredicateOf_aux (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hη : η ∈ algebraicCycleClassSpan X 1) :
    letI := hT.finite
    HodgeBlocks.IsCycleClassPredicate (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) ((hT.cupWedgeEquiv 2).symm η) :=
  cycleClassPredicateOf (finbetti_finiteBetti X) hB hD hT hM hH hη

theorem harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf_aux (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (h11 : LefschetzOneOneHyp) :
    letI := hT.finite
    HodgeBlocks.LefschetzOneOne (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) :=
  lefschetzOneOne_abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT h11

theorem harvestBetti_polarizationTopPowerNonzero_abelianVarietyCohomologyOf_aux
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {η : HQ X 2}
    (hL : HardLefschetz X μ η) :
    letI := hT.finite
    HodgeBlocks.PolarizationTopPowerNonzero
      (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT)
      ((hT.cupWedgeEquiv 2).symm η) :=
  polarizationTopPowerNonzero_abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT hL

theorem harvestBetti_hodgeRingGeneratedByDivisorsAndWeil_of_hSU_aux
    {hB : BettiDeRhamIso X} {hD : HodgeDecomposition X} {hT : TorusCohomology μ}
    {A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        3}
    {η : HQ X 2} (hM : IsMemberOfM (finbetti_finiteBetti X) hB hD hT A η)
    (hC : CupFiltered X μ)
    (hSU : F1575MemberHodgeGroupIsSU (finbetti_finiteBetti X) hB hD hT A hM)
    (hW : letI := hT.finite; A.IsWeilType := hM.isWeilType) :
    HodgeRingGeneratedByDivisorsAndWeil (finbetti_finiteBetti X) hB hD hT A hW :=
  hodgeRingGeneratedByDivisorsAndWeil_of_hSU hM hC hSU hW

end HodgeLean.Adapters
