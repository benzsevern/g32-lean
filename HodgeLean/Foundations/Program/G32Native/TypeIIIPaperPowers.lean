import HodgeLean.Foundations.Program.G32Native.TypeIIIPaperSteps
noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program.TypeIIIPaper
/-- The Weil-to-powers implication with the powers theorem supplied as `hPowers`.
Source: Abdulali, Hodge structures on abelian varieties of type III,
Annals of Mathematics 155 (2002), 915–928, Remark 4.2 and proof of Theorem 4.1,
p. 924. The 1999 original was not checked. The argument `hPowers` is the exact
former general-member powers statement, not a theorem asserted here. -/
theorem powers_of_weil_algebraic (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2)
    (hMember : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)
    (P : GeneralPELMember A W pol hMember)
    (hPowers : ∀ (P : GeneralPELMember A W pol hMember),
      (∀ x : HQ A (2 * 3), x ∈ quaternionicSpan A (weilSix A W pol hMember) →
        x ∈ algebraicCycleClassSpan A 3) →
      ∀ (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
        [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
        (r : ℕ), 0 < r → AbelianPowerData A Y r →
        ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p) 
    (hWeil : WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hMember.isWeilType)
    (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (r : ℕ) (hr : 0 < r) (power : AbelianPowerData A Y r) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  exact hPowers P (quaternionic_weil_algebraic A W pol hMember hWeil) Y r hr power

#print axioms powers_of_weil_algebraic

end HodgeLean.Foundations.Program.TypeIIIPaper
