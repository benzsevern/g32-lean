import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitRank

noncomputable section
set_option maxHeartbeats 40000
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.TypeIIIPaper

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)

/-- The sixfold specialization of the quaternionic-space and algebraicity transfer results.
The general-member field is not needed for these results, but is retained by this caller.
Source: van Geemen–Verra, Quaternionic Pryms and Hodge Classes, §4.6,
Proposition 4.7, pp. 11–12, and Corollary 4.9, p. 12 (arXiv math/0103111).
The independence from other quadratic subfields is not asserted by this specialization. -/
theorem quaternionic_weil_orbit_aux (P : GeneralPELMember A W pol hM) :
    Module.finrank ℚ (quaternionicSpan A (weilSix A W pol hM)) = 7 ∧
    (∀ x : HQ A (2 * 3), x ∈ quaternionicSpan A (weilSix A W pol hM) → x ∈ Hdg^3(A; ℚ)) ∧
    (WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.isWeilType →
      ∀ x : HQ A (2 * 3), x ∈ quaternionicSpan A (weilSix A W pol hM) →
        x ∈ algebraicCycleClassSpan A 3) := by
  exact ⟨quaternionic_weil_finrank A W pol hM P,
    quaternionic_weil_hodge A W pol hM, quaternionic_weil_algebraic A W pol hM⟩

#print axioms quaternionic_weil_orbit_aux

end HodgeLean.Foundations.Program.TypeIIIPaper
