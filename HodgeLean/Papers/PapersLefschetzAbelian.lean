import HodgeLean.Adapters.LedgerHarvestBetti
import HodgeLean.Adapters.F1575
import HodgeLean.Foundations.ChowProjective

/-! # Abelian-variety milestones and Weil connectors with Lefschetz (1,1) supplied

The `RealDefs` restatements (`hdg_le_span_abelian_g1`–`g3`, the Weil and F-1569 connectors,
the Blocks `LefschetzOneOne` package) and their `LedgerHarvestBetti` wrappers without `h11`.

Each `papl_` theorem has the binders and conclusion of the theorem it names, except
`h11 : LefschetzOneOneHyp`; its proof is the original body with `chowG_lefschetzOneOne_abelian X`
(handoff 215) at the one variety where Lefschetz (1,1) is used. Each is an implication from the
remaining binders, which stay as they are. Not claimed: the universal `LefschetzOneOneHyp`, or
any remaining binder. Inventory in `docs/specs/PapersLefschetz.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters NumberField HodgeLean.Foundations.Curves

namespace HodgeLean.Papers

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X} [GrpObj X]

/-- **`lefschetzOneOne_abelianVarietyCohomologyOf` without `h11`.** The binders and conclusion of `lefschetzOneOne_abelianVarietyCohomologyOf` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_lefschetzOneOne_abelianVarietyCohomologyOf (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) :
    letI := hT.finite
    HodgeBlocks.LefschetzOneOne (abelianVarietyCohomologyOf hF hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) := by
  let := hT.finite
  exact ⟨fun v hv => (isAlgebraicOf_iff 1 v).mpr
    (chowG_lefschetzOneOne_abelian X ((isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT 1 v).mp hv))⟩

/-- The conclusion of `lefschetzOneOne_abelianVarietyCohomologyOf`, under its own hypotheses, from `papl_lefschetzOneOne_abelianVarietyCohomologyOf`. -/
example : type_of% @HodgeLean.RealDefs.lefschetzOneOne_abelianVarietyCohomologyOf := by
  intros
  apply @papl_lefschetzOneOne_abelianVarietyCohomologyOf

/--
info: 'HodgeLean.Papers.papl_lefschetzOneOne_abelianVarietyCohomologyOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms papl_lefschetzOneOne_abelianVarietyCohomologyOf

/-- **`hdg_le_span_abelian_g1` without `h11`.** The binders and conclusion of `hdg_le_span_abelian_g1` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: the degree argument of `HodgeBlocks.hodgeConjecture_g1`, using the
unit class, Lefschetz `(1,1)` and exterior-power vanishing directly;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_hdg_le_span_abelian_g1 (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hH : CycleClassIsHodge X) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_g1_of_degree_one hT (chowG_lefschetzOneOne_abelian X) hg

/-- The conclusion of `hdg_le_span_abelian_g1`, under its own hypotheses, from `papl_hdg_le_span_abelian_g1`. -/
example : type_of% @HodgeLean.RealDefs.hdg_le_span_abelian_g1 := by
  intros
  apply @papl_hdg_le_span_abelian_g1 <;> assumption

/--
info: 'HodgeLean.Papers.papl_hdg_le_span_abelian_g1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_hdg_le_span_abelian_g1

/-- **`hdg_le_span_abelian_g2` without `h11`.** The binders and conclusion of `hdg_le_span_abelian_g2` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: a restatement of the Blocks theorem `HodgeBlocks.hodgeConjecture_g2`
(`HodgeLean/Blocks/Milestone/HardLefschetz.lean`) through the transfer
`hdg_le_span_of_hodgeConjectureFor` (F-1689); the published inputs are the hypotheses in the
table, each with its own `Source:` line;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_hdg_le_span_abelian_g2 (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  let := hT.finite
  exact hdg_le_span_of_hodgeConjectureFor hF hB hD hT
    (HodgeBlocks.hodgeConjecture_g2 _ _ hg (cycleClassPredicateOf hF hB hD hT hM hH hA.η_mem)
      (papl_lefschetzOneOne_abelianVarietyCohomologyOf hF hB hD hT)
      (polarizationTopPowerNonzero_abelianVarietyCohomologyOf hF hB hD hT hL))

/-- The conclusion of `hdg_le_span_abelian_g2`, under its own hypotheses, from `papl_hdg_le_span_abelian_g2`. -/
example : type_of% @HodgeLean.RealDefs.hdg_le_span_abelian_g2 := by
  intros
  apply @papl_hdg_le_span_abelian_g2 <;> assumption

/--
info: 'HodgeLean.Papers.papl_hdg_le_span_abelian_g2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_hdg_le_span_abelian_g2

/-- **`hdg_le_span_abelian_g3` without `h11`.** The binders and conclusion of `hdg_le_span_abelian_g3` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: a restatement of the Blocks theorem `HodgeBlocks.hodgeConjecture_g3`
(`HodgeLean/Blocks/Milestone/HardLefschetz.lean`) through the transfer
`hdg_le_span_of_hodgeConjectureFor` (F-1689); the published inputs are the hypotheses in the
table, each with its own `Source:` line;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_hdg_le_span_abelian_g3 (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hC : CupFiltered X μ)
    (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  let := hT.finite
  exact hdg_le_span_of_hodgeConjectureFor hF hB hD hT
    (HodgeBlocks.hodgeConjecture_g3 _ _ hg (cycleClassPredicateOf hF hB hD hT hM hH hA.η_mem)
      (papl_lefschetzOneOne_abelianVarietyCohomologyOf hF hB hD hT)
      (hardLefschetzFromDegreeTwoOf hF hB hD hT hH hA hL hC hg)
      (polarizationTopPowerNonzero_abelianVarietyCohomologyOf hF hB hD hT hL))

/-- The conclusion of `hdg_le_span_abelian_g3`, under its own hypotheses, from `papl_hdg_le_span_abelian_g3`. -/
example : type_of% @HodgeLean.RealDefs.hdg_le_span_abelian_g3 := by
  intros
  apply @papl_hdg_le_span_abelian_g3 <;> assumption

/--
info: 'HodgeLean.Papers.papl_hdg_le_span_abelian_g3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_hdg_le_span_abelian_g3

/-- **`hdg_le_span_of_weilClassesAlgebraic` without `h11`.** The binders and conclusion of `hdg_le_span_of_weilClassesAlgebraic` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: Fulton, *Intersection Theory*, 2nd ed., Ergeb. Math. Grenzgeb. (3) 2, Ch. 19, Corollary 19.2 (through `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through `chowG_lefschetzOneOne_abelian`, handoff 215); the reduction itself is in Lean. -/
theorem papl_hdg_le_span_of_weilClassesAlgebraic (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hWA : WeilClassesAlgebraic hF hB hD hT A hW)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil hF hB hD hT A hW)
    (hM : CycleClassMultiplicative μ) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := fun p =>
  (hGen.generated p).trans <| divisorWeilSpan_le hF hB hD hT A hW
    (F := fun p => algebraicCycleClassSpan X p)
    { unit_mem := unitClass_mem_algebraicCycleClassSpan
      hdg_one_le := chowG_lefschetzOneOne_abelian X
      weil_le := hWA
      cup_mem := fun h a b ha hb => hM.mem h a b ha hb } p

/-- The Blocks-side statement for this `X` follows too: the transfer converse
`hodgeConjectureFor_of_hdg_le_span` applied to the connector's conclusion. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hWA : WeilClassesAlgebraic hF hB hD hT A hW)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil hF hB hD hT A hW)
    (hM : CycleClassMultiplicative μ) :
    letI := hT.finite
    HodgeBlocks.HodgeConjectureFor (abelianVarietyCohomologyOf hF hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) :=
  hodgeConjectureFor_of_hdg_le_span hF hB hD hT
    (papl_hdg_le_span_of_weilClassesAlgebraic hF hB hD hT A hW hWA hGen hM)

/-- The conclusion of `hdg_le_span_of_weilClassesAlgebraic`, under its own hypotheses, from `papl_hdg_le_span_of_weilClassesAlgebraic`. -/
example : type_of% @HodgeLean.RealDefs.hdg_le_span_of_weilClassesAlgebraic := by
  intros
  apply @papl_hdg_le_span_of_weilClassesAlgebraic <;> assumption

/--
info: 'HodgeLean.Papers.papl_hdg_le_span_of_weilClassesAlgebraic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_hdg_le_span_of_weilClassesAlgebraic

/-- **`hdg_le_span_of_f1569Statement` without `h11`.** The binders and conclusion of `hdg_le_span_of_f1569Statement` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: the reduction is `hdg_le_span_of_weilClassesAlgebraic` (Fulton, *Intersection Theory*,
Corollary 19.2, through `CycleClassMultiplicative`; Griffiths–Harris, Ch. 1 §2, through `chowG_lefschetzOneOne_abelian`, handoff 215); the generation hypothesis is van Geemen, LNM 1594 (Hodge group `SU_H`),
through `HodgeRingGeneratedByDivisorsAndWeil`. -/
theorem papl_hdg_le_span_of_f1569Statement
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementFor cup)
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil hF hB hD hT A hM.isWeilType)
    (hC9 : CycleClassMultiplicative (cup X)) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  papl_hdg_le_span_of_weilClassesAlgebraic hF hB hD hT A hM.isWeilType
    (weilClassesAlgebraic_of_f1569Statement cup hF1569 hF hB hD hT A hM) hGen hC9

/-- The conclusion of `hdg_le_span_of_f1569Statement`, under its own hypotheses, from `papl_hdg_le_span_of_f1569Statement`. -/
example : type_of% @HodgeLean.RealDefs.hdg_le_span_of_f1569Statement := by
  intros
  apply @papl_hdg_le_span_of_f1569Statement <;> assumption

/--
info: 'HodgeLean.Papers.papl_hdg_le_span_of_f1569Statement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_hdg_le_span_of_f1569Statement

/-- **`hdg_le_span_of_f1569Statement_of_hSU` without `h11`.** The binders and conclusion of `hdg_le_span_of_f1569Statement_of_hSU` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_hdg_le_span_of_f1569Statement_of_hSU
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementFor cup)
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η)
    (hC : CupFiltered X (cup X)) (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM)
    (hC9 : CycleClassMultiplicative (cup X)) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  papl_hdg_le_span_of_f1569Statement cup hF1569 hF hB hD hT A hM
    (hodgeRingGeneratedByDivisorsAndWeil_of_hSU hM hC hSU) hC9

/-- The conclusion of `hdg_le_span_of_f1569Statement_of_hSU`, under its own hypotheses, from `papl_hdg_le_span_of_f1569Statement_of_hSU`. -/
example : type_of% @HodgeLean.Adapters.hdg_le_span_of_f1569Statement_of_hSU := by
  intros
  apply @papl_hdg_le_span_of_f1569Statement_of_hSU <;> assumption

/--
info: 'HodgeLean.Papers.papl_hdg_le_span_of_f1569Statement_of_hSU' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_hdg_le_span_of_f1569Statement_of_hSU

/-- **`harvestBetti_hdg_le_span_abelian_g1` without `h11`.** The binders and conclusion of `harvestBetti_hdg_le_span_abelian_g1` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: `hdg_le_span_abelian_g1` (F-1690), by the shared degree argument; finite Betti
numbers by Hatcher, *Algebraic Topology*, Appendix, Corollary A.8, through `finbetti_finiteBetti`;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_harvestBetti_hdg_le_span_abelian_g1 (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hH : CycleClassIsHodge X) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact papl_hdg_le_span_abelian_g1 (finbetti_finiteBetti X) hB hD hT hH hg

/-- The conclusion of `harvestBetti_hdg_le_span_abelian_g1`, under its own hypotheses, from `papl_harvestBetti_hdg_le_span_abelian_g1`. -/
example : type_of% @HodgeLean.Adapters.harvestBetti_hdg_le_span_abelian_g1 := by
  intros
  apply @papl_harvestBetti_hdg_le_span_abelian_g1 <;> assumption

/--
info: 'HodgeLean.Papers.papl_harvestBetti_hdg_le_span_abelian_g1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_harvestBetti_hdg_le_span_abelian_g1

/-- **`harvestBetti_hdg_le_span_abelian_g2` without `h11`.** The binders and conclusion of `harvestBetti_hdg_le_span_abelian_g2` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: a restatement of the Blocks theorem `HodgeBlocks.hodgeConjecture_g2` through the transfer
`hdg_le_span_of_hodgeConjectureFor` (F-1689), as for `hdg_le_span_abelian_g2`; finite Betti
numbers by Hatcher, *Algebraic Topology*, Appendix, Corollary A.8, through `finbetti_finiteBetti`;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_harvestBetti_hdg_le_span_abelian_g2 (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact papl_hdg_le_span_abelian_g2 (finbetti_finiteBetti X) hB hD hT hM hH hA hL hg

/-- The conclusion of `harvestBetti_hdg_le_span_abelian_g2`, under its own hypotheses, from `papl_harvestBetti_hdg_le_span_abelian_g2`. -/
example : type_of% @HodgeLean.Adapters.harvestBetti_hdg_le_span_abelian_g2 := by
  intros
  apply @papl_harvestBetti_hdg_le_span_abelian_g2 <;> assumption

/--
info: 'HodgeLean.Papers.papl_harvestBetti_hdg_le_span_abelian_g2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_harvestBetti_hdg_le_span_abelian_g2

/-- **`harvestBetti_hdg_le_span_abelian_g3` without `h11`.** The binders and conclusion of `harvestBetti_hdg_le_span_abelian_g3` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: a restatement of the Blocks theorem `HodgeBlocks.hodgeConjecture_g3` through the transfer
`hdg_le_span_of_hodgeConjectureFor` (F-1689), as for `hdg_le_span_abelian_g3`; finite Betti
numbers by Hatcher, *Algebraic Topology*, Appendix, Corollary A.8, through `finbetti_finiteBetti`;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_harvestBetti_hdg_le_span_abelian_g3 (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hC : CupFiltered X μ)
    (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact papl_hdg_le_span_abelian_g3 (finbetti_finiteBetti X) hB hD hT hM hH hA hL hC hg

/-- The conclusion of `harvestBetti_hdg_le_span_abelian_g3`, under its own hypotheses, from `papl_harvestBetti_hdg_le_span_abelian_g3`. -/
example : type_of% @HodgeLean.Adapters.harvestBetti_hdg_le_span_abelian_g3 := by
  intros
  apply @papl_harvestBetti_hdg_le_span_abelian_g3 <;> assumption

/--
info: 'HodgeLean.Papers.papl_harvestBetti_hdg_le_span_abelian_g3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_harvestBetti_hdg_le_span_abelian_g3

/-- **`harvestBetti_hdg_le_span_of_weilClassesAlgebraic` without `h11`.** The binders and conclusion of `harvestBetti_hdg_le_span_of_weilClassesAlgebraic` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: Fulton, *Intersection Theory*, 2nd ed., Corollary 19.2 (through
`CycleClassMultiplicative`) and Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2
(through `chowG_lefschetzOneOne_abelian`, handoff 215), as for `hdg_le_span_of_weilClassesAlgebraic`; finite Betti
numbers by Hatcher, *Algebraic Topology*, Appendix, Corollary A.8, through `finbetti_finiteBetti`. -/
theorem papl_harvestBetti_hdg_le_span_of_weilClassesAlgebraic
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        d)
    (hW : letI := hT.finite; A.IsWeilType)
    (hWA : WeilClassesAlgebraic (finbetti_finiteBetti X) hB hD hT A hW)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil (finbetti_finiteBetti X) hB hD hT A hW)
    (hM : CycleClassMultiplicative μ) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact papl_hdg_le_span_of_weilClassesAlgebraic (finbetti_finiteBetti X) hB hD hT A hW hWA hGen hM

/-- The conclusion of `harvestBetti_hdg_le_span_of_weilClassesAlgebraic`, under its own hypotheses, from `papl_harvestBetti_hdg_le_span_of_weilClassesAlgebraic`. -/
example : type_of% @HodgeLean.Adapters.harvestBetti_hdg_le_span_of_weilClassesAlgebraic := by
  intros
  apply @papl_harvestBetti_hdg_le_span_of_weilClassesAlgebraic <;> assumption

/--
info: 'HodgeLean.Papers.papl_harvestBetti_hdg_le_span_of_weilClassesAlgebraic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms papl_harvestBetti_hdg_le_span_of_weilClassesAlgebraic

/-- **`harvestBetti_hdg_le_span_of_f1569Statement` without `h11`.** The binders and conclusion of `harvestBetti_hdg_le_span_of_f1569Statement` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: the reduction `hdg_le_span_of_weilClassesAlgebraic` and van Geemen, LNM 1594 (through
`HodgeRingGeneratedByDivisorsAndWeil`), as for `hdg_le_span_of_f1569Statement`; finite Betti
numbers by Hatcher, *Algebraic Topology*, Appendix, Corollary A.8, through `finbetti_finiteBetti`;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_harvestBetti_hdg_le_span_of_f1569Statement
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementForBetti cup)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        3)
    {η : HQ X 2} (hM : IsMemberOfM (finbetti_finiteBetti X) hB hD hT A η)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil (finbetti_finiteBetti X) hB hD hT A
      hM.isWeilType)
    (hC9 : CycleClassMultiplicative (cup X)) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  papl_hdg_le_span_of_f1569Statement cup
    ((harvestBetti_f1569StatementForBetti_iff_aux cup).mp hF1569)
    (finbetti_finiteBetti X) hB hD hT A hM hGen hC9

/-- The conclusion of `harvestBetti_hdg_le_span_of_f1569Statement`, under its own hypotheses, from `papl_harvestBetti_hdg_le_span_of_f1569Statement`. -/
example : type_of% @HodgeLean.Adapters.harvestBetti_hdg_le_span_of_f1569Statement := by
  intros
  apply @papl_harvestBetti_hdg_le_span_of_f1569Statement <;> assumption

/--
info: 'HodgeLean.Papers.papl_harvestBetti_hdg_le_span_of_f1569Statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms papl_harvestBetti_hdg_le_span_of_f1569Statement

/-- **`harvestBetti_hdg_le_span_of_f1569Statement_of_hSU` without `h11`.** The binders and conclusion of `harvestBetti_hdg_le_span_of_f1569Statement_of_hSU` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: as for `hdg_le_span_of_f1569Statement_of_hSU` (F-1575, through
`hodgeRingGeneratedByDivisorsAndWeil_of_hSU`); finite Betti numbers by Hatcher, *Algebraic
Topology*, Appendix, Corollary A.8, through `finbetti_finiteBetti`;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_harvestBetti_hdg_le_span_of_f1569Statement_of_hSU
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementForBetti cup)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT).weight1
        3)
    {η : HQ X 2} (hM : IsMemberOfM (finbetti_finiteBetti X) hB hD hT A η)
    (hC : CupFiltered X (cup X))
    (hSU : F1575MemberHodgeGroupIsSU (finbetti_finiteBetti X) hB hD hT A hM)
    (hC9 : CycleClassMultiplicative (cup X)) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  papl_hdg_le_span_of_f1569Statement_of_hSU cup
    ((harvestBetti_f1569StatementForBetti_iff_aux cup).mp hF1569)
    (finbetti_finiteBetti X) hB hD hT A hM hC hSU hC9

/-- The conclusion of `harvestBetti_hdg_le_span_of_f1569Statement_of_hSU`, under its own hypotheses, from `papl_harvestBetti_hdg_le_span_of_f1569Statement_of_hSU`. -/
example : type_of% @HodgeLean.Adapters.harvestBetti_hdg_le_span_of_f1569Statement_of_hSU := by
  intros
  apply @papl_harvestBetti_hdg_le_span_of_f1569Statement_of_hSU <;> assumption

/--
info: 'HodgeLean.Papers.papl_harvestBetti_hdg_le_span_of_f1569Statement_of_hSU' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms papl_harvestBetti_hdg_le_span_of_f1569Statement_of_hSU

/-- **`harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf` without `h11`.** The binders and conclusion of `harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf` except
`h11`; Lefschetz (1,1) is used only at the abelian variety in scope, where
`chowG_lefschetzOneOne_abelian` supplies it.
Source: as for `lefschetzOneOne_abelianVarietyCohomologyOf` (Griffiths–Harris, *Principles of
Algebraic Geometry*, Ch. 1 §2, through `chowG_lefschetzOneOne_abelian`, handoff 215); finite Betti numbers by Hatcher,
*Algebraic Topology*, Appendix, Corollary A.8, through `finbetti_finiteBetti`. -/
theorem papl_harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) :
    letI := hT.finite
    HodgeBlocks.LefschetzOneOne (abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) :=
  papl_lefschetzOneOne_abelianVarietyCohomologyOf (finbetti_finiteBetti X) hB hD hT

/-- The conclusion of `harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf`, under its own hypotheses, from `papl_harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf`. -/
example : type_of% @HodgeLean.Adapters.harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf := by
  intros
  apply @papl_harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf

/--
info: 'HodgeLean.Papers.papl_harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms papl_harvestBetti_lefschetzOneOne_abelianVarietyCohomologyOf

end HodgeLean.Papers
