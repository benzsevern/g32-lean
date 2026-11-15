import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitWeil
import HodgeLean.Foundations.Program.CompensationEightfold

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.TypeIIIPaper
variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- The identity endomorphism acts as the identity in each exterior degree. -/
theorem rationalPullback_one (n : ℕ) : rationalPullback A 1 n = LinearMap.id := by
  unfold rationalPullback
  simp only [map_one, MulOpposite.unop_one]
  change ((torusCohomology_cupProductOf A).cupWedgeEquiv n).toLinearMap ∘ₗ
    exteriorPower.map n LinearMap.id ∘ₗ
      ((torusCohomology_cupProductOf A).cupWedgeEquiv n).symm.toLinearMap = _
  rw [exteriorPower.map_id]
  ext x
  exact ((torusCohomology_cupProductOf A).cupWedgeEquiv n).apply_symm_apply x

/-- The unit translate retains the original subspace. -/
theorem le_quaternionicSpan (U : Submodule ℚ (HQ A (2*3))) :
    U ≤ quaternionicSpan A U := by
  have h := le_iSup (fun d : (AbelianEnd0 A)ˣ =>
    U.map (rationalPullback A (d : AbelianEnd0 A) (2*3))) 1
  intro x hx
  apply h
  refine ⟨x, hx, ?_⟩
  rw [Units.val_one, rationalPullback_one]
  rfl

/-- Equality of degree indices preserves the rank of a transported subspace. -/
theorem degree_cast_finrank {i j : ℕ} (h : i = j)
    (U : Submodule ℚ (HQ A (2*i))) :
    Module.finrank ℚ ↥(cast (congrArg (fun n => Submodule ℚ (HQ A (2*n))) h) U) =
      Module.finrank ℚ U := by
  subst j
  rfl

variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)

/-- The selected Weil subspace has rational rank two. -/
theorem weilSix_finrank : Module.finrank ℚ (weilSix A W pol hM) = 2 := by
  have h := cq8_weilClassOf_finrank (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
    (by norm_num : (0 : ℚ) < 3) W hM.isWeilType (by rw [hM.dim_eq]; norm_num)
  exact (degree_cast_finrank A hM.finrank_eq_three _).trans h

/-- The quaternionic orbit span retains at least the two original Weil dimensions. -/
theorem quaternionic_weil_rank_lower :
    2 ≤ Module.finrank ℚ (quaternionicSpan A (weilSix A W pol hM)) := by
  letI := (finiteBetti_abelian A).finite (2*3)
  have h := Submodule.finrank_mono (le_quaternionicSpan A (weilSix A W pol hM))
  rw [weilSix_finrank A W pol hM] at h
  exact h

#print axioms weilSix_finrank
#print axioms quaternionic_weil_rank_lower
end HodgeLean.Foundations.Program.TypeIIIPaper
