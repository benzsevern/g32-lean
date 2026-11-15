import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitUnit

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.TypeIIIPaper
variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- Bounds on an indexed subspace transport along an equality of degrees. -/
theorem degree_cast_le {i j : ℕ} (h : i = j)
    (U : Submodule ℚ (HQ A (2*i)))
    (C : ∀ n, Submodule ℚ (HQ A (2*n))) (hU : U ≤ C i) :
    cast (congrArg (fun n => Submodule ℚ (HQ A (2*n))) h) U ≤ C j := by
  subst j
  exact hU

variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)

/-- Any indexed bound on the original Weil space gives the corresponding degree-six bound. -/
theorem weilSix_le (C : ∀ n, Submodule ℚ (HQ A (2*n)))
    (h : weilClassOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hM.isWeilType ≤
        C (Module.finrank ℂ ↥(W.Vs ⊓
          (abelianVarietyCohomologyOf (finiteBetti_abelian A)
            (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
            (torusCohomology_cupProductOf A)).weight1.H (1, 0)))) :
    weilSix A W pol hM ≤ C 3 := by
  exact degree_cast_le A hM.finrank_eq_three _ C h

/-- Hodge containment of the selected quaternionic orbit needs no general-member input. -/
theorem quaternionic_weil_hodge :
    quaternionicSpan A (weilSix A W pol hM) ≤ Hdg^3(A; ℚ) := by
  apply quaternionicSpan_hodge
  exact weilSix_le A W pol hM (fun n => Hdg^n(A; ℚ))
    (abelian_weilClassOf_le_hdg A W hM.isWeilType)

/-- Algebraicity transfers from the selected Weil space to its rational unit orbit span. -/
theorem quaternionic_weil_algebraic
    (h : WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.isWeilType) :
    quaternionicSpan A (weilSix A W pol hM) ≤ algebraicCycleClassSpan A 3 := by
  apply quaternionicSpan_algebraic
  exact weilSix_le A W pol hM (algebraicCycleClassSpan A) h

#print axioms quaternionic_weil_hodge
#print axioms quaternionic_weil_algebraic
end HodgeLean.Foundations.Program.TypeIIIPaper
