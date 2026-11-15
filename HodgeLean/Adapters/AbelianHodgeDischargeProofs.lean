import HodgeLean.Adapters.AbelianHodgeDischargeDefs

/-! # Proof obligations for the abelian discharge of `HodgeDecomposition` and `CupFiltered` -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

theorem hodgeDecomposition_of_abelian_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    HodgeDecomposition X := by
  exact spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
    (spec_cupLeft_cupProductOf X)

theorem cupFiltered_cupProductOf_of_abelian_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    CupFiltered X (cupProductOf X) := by
  exact spec_cupFiltered_of_cupLeft_alone X (torusCohomology_cupProductOf X)
    (spec_cupLeft_cupProductOf X)

theorem f1569StatementForAbelian_iff_aux
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) :
    F1569StatementForAbelian cup ↔ F1569StatementFor cup := by
  exact ⟨fun h X _ _ _ _ _ _ _ hT A hW η hM => h X hT A hW η hM,
    fun h X _ _ _ _ hT A hW η hM => h X _ _ _ hT A hW η hM⟩

section Restatements

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X}

theorem abelian_isExteriorOfWeightOne_aux :
    letI := (torusCohomology_cupProductOf X).finite
    AbelianVarietyCohomology.IsExteriorOfWeightOne
      (abelianVarietyCohomologyOf (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X)) := by
  exact isExteriorOfWeightOne_of_cupFiltered _ _ _ _ (cupFiltered_cupProductOf_of_abelian_aux X)

theorem abelian_weilClassOf_le_hdg_aux {d : ℚ}
    (A : letI := (torusCohomology_cupProductOf X).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X)).weight1 d)
    (hW : letI := (torusCohomology_cupProductOf X).finite; A.IsWeilType) :
    letI := (torusCohomology_cupProductOf X).finite
    weilClassOf (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X) A hW ≤
      Hdg^(Module.finrank ℂ ↥(A.Vs ⊓
        (abelianVarietyCohomologyOf (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X)).weight1.H
          (1, 0)))(X; ℚ) := by
  exact weilClassOf_le_hdg _ _ _ _ (cupFiltered_cupProductOf_of_abelian_aux X) A hW

theorem abelian_hdg_le_span_of_hodgeConjectureFor_aux (hT : TorusCohomology μ)
    (h : letI := hT.finite
      HodgeBlocks.HodgeConjectureFor
        (abelianVarietyCohomologyOf (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian_aux X) hT)
        (fun {m} => isAlgebraicOf μ (m := m))) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_of_hodgeConjectureFor _ _ _ hT h

theorem abelian_hdg_le_span_g1_aux (hT : TorusCohomology μ)
    (hH : CycleClassIsHodge X) (h11 : LefschetzOneOneHyp) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_abelian_g1 (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian_aux X) hT hH h11 hg

theorem abelian_hdg_le_span_g2_aux (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (h11 : LefschetzOneOneHyp) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_abelian_g2 (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian_aux X) hT hM hH hA hL h11 hg

theorem abelian_hdg_le_span_g3_aux (hM : CycleClassMultiplicative (cupProductOf X))
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hL : HardLefschetz X (cupProductOf X) η) (h11 : LefschetzOneOneHyp)
    (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g3 (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X) hM hH hA hL
    (cupFiltered_cupProductOf_of_abelian_aux X) h11 hg

theorem abelian_hdg_le_span_of_weilClassesAlgebraic_aux (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian_aux X) hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType)
    (hWA : WeilClassesAlgebraic (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian_aux X) hT A hW)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil (finbetti_finiteBetti X)
      (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian_aux X) hT A hW)
    (hM : CycleClassMultiplicative μ) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_of_weilClassesAlgebraic (finbetti_finiteBetti X)
    (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian_aux X) hT A hW hWA hGen hM h11

theorem abelian_hdg_le_span_of_f1569Statement_aux
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementForAbelian cup)
    (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian_aux X) hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian_aux X) hT A η)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil (finbetti_finiteBetti X)
      (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian_aux X) hT A
      hM.isWeilType)
    (hC9 : CycleClassMultiplicative (cup X)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_of_f1569Statement cup ((f1569StatementForAbelian_iff_aux cup).mp hF1569)
    (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian_aux X) hT A hM hGen
    hC9 h11

theorem abelian_hdg_le_span_of_f1569Statement_of_hSU_aux
    (hF1569 : F1569StatementForAbelian (fun X _ _ _ => cupProductOf X))
    (A : letI := (torusCohomology_cupProductOf X).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X)).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X) A η)
    (hSU : F1575MemberHodgeGroupIsSU (finbetti_finiteBetti X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X) A hM)
    (hC9 : CycleClassMultiplicative (cupProductOf X)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_of_f1569Statement_of_hSU (fun X _ _ _ => cupProductOf X)
    ((f1569StatementForAbelian_iff_aux _).mp hF1569) (finbetti_finiteBetti X)
    (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian_aux X) (torusCohomology_cupProductOf X) A hM
    (cupFiltered_cupProductOf_of_abelian_aux X) hSU hC9 h11

theorem abelian_hdg_le_span_g1_cupProductOf_aux
    (hH : CycleClassIsHodge X)
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g1_cupProductOf X (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian_aux X) hH h11 hg

theorem abelian_hdg_le_span_g2_cupProductOf_aux
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Foundations.Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g2_cupProductOf X (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian_aux X) hM hH hA hη h11 hg

theorem abelian_hdg_le_span_g3_cupProductOf_aux
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Foundations.Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g3_cupProductOf X (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian_aux X) hM hH hA hη (cupFiltered_cupProductOf_of_abelian_aux X) h11 hg

theorem abelian_hdg_le_span_g2_of_cupPow_aux
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 2 ≠ 0)
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g2_of_cupPow X (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian_aux X) hM hH hA hη h11 hg

theorem abelian_hdg_le_span_g3_of_cupPow_aux
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 3 ≠ 0)
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g3_of_cupPow X (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian_aux X) hM hH hA hη (cupFiltered_cupProductOf_of_abelian_aux X) h11 hg

end Restatements

end HodgeLean.Adapters
