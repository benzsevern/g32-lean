import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitTransport
import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitWeil

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
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

/-- The degree-six selected space is the image of the original rational Weil exterior space. -/
theorem weilSix_eq_map_topCast
    (h : let k := Module.finrank ℂ ↥(W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H (1,0)); k+k = 2*3) :
    let k := Module.finrank ℂ ↥(W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H (1,0))
    weilSix A W pol hM =
      (W.weilClasses (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) hM.isWeilType).map
        (((torusCohomology_cupProductOf A).cupWedgeEquiv (k+k)).trans (HQ.castEquiv A h)).toLinearMap := by
  let k := Module.finrank ℂ ↥(W.Vs ⊓
    (abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)).weight1.H (1,0))
  change cast (congrArg (fun n => Submodule ℚ (HQ A (2*n))) hM.finrank_eq_three)
    (weilClassOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hM.isWeilType) = _
  rw [degree_cast_submodule_map A hM.finrank_eq_three]
  unfold weilClassOf
  rw [← Submodule.map_comp]
  apply congrArg (fun f => (W.weilClasses (h10_sup_h01_eq_top (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
    (torusCohomology_cupProductOf A)) hM.isWeilType).map f)
  apply LinearMap.ext
  intro x
  change ((HQ.castEquiv A (two_mul k).symm).trans
    (HQ.castEquiv A (congrArg (2*·) hM.finrank_eq_three)))
      ((cupProductOf A).cupWedgeMap (k+k) x) =
    (HQ.castEquiv A h) ((cupProductOf A).cupWedgeMap (k+k) x)
  rw [cohomology_cast_trans A (two_mul k).symm (congrArg (2*·) hM.finrank_eq_three)]

#print axioms weilSix_eq_map_topCast
end HodgeLean.Foundations.Program.TypeIIIPaper
