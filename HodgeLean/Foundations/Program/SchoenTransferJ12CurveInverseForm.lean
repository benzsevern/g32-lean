import HodgeLean.Foundations.Program.SchoenTransferJ12CurveDivisorOperator
import HodgeLean.Adapters.TorusCohomology
import HodgeLean.RealDefs.F1569

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory Module
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- An identity divisor operator identifies its dual alternating form with the negative actual curve pairing. -/
theorem s4_selected_curve_identity_divisor_form
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (q : HQ A 2)
    (hq : s4_selected_curve_divisor_operator A Y f I q = LinearMap.id) :
    ∃ hω : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) q),
      ∀ x y : HQ A 1,
        polarizationForm (torusCohomology_cupProductOf A) hω x y =
          -I ((cupProductOf Y).cup rfl (homPullback f 1 x) (homPullback f 1 y)) := by
  letI := (torusCohomology_cupProductOf A).finite
  let ω := polarizationVec (torusCohomology_cupProductOf A) q
  let P := ((cupProductOf Y).cup (show 1 + 1 = 2 from rfl)).compr₂ I.toLinearMap
  let C : HQ Y 1 →ₗ[ℚ] Module.Dual ℚ (HQ A 1) :=
    (homPullback f 1).dualMap.comp P.flip
  have hformula (v : HQ A 1) : -contract ω (C (homPullback f 1 v)) = v := by
    have h := s4_selected_curve_mixed_action_contract A Y f I ω (homPullback f 1 v)
    rw [cupWedgeMap_polarizationVec] at h
    have hd := LinearMap.congr_fun hq v
    exact h.symm.trans hd
  have hsurj : Function.Surjective (contract ω) := by
    intro v
    exact ⟨-C (homPullback f 1 v), by rw [map_neg]; exact hformula v⟩
  have hω : IsNondegenerate ω :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℚ) (V := HQ A 1))).mpr hsurj, hsurj⟩
  refine ⟨hω, ?_⟩
  have hinv (v : HQ A 1) : (contractEquiv hω).symm v = -C (homPullback f 1 v) := by
    apply (contractEquiv hω).injective
    change contract ω ((contractEquiv hω).symm v) = contract ω (-C (homPullback f 1 v))
    rw [contract_contractEquiv_symm, map_neg]
    exact (hformula v).symm
  intro x y
  change ((contractEquiv hω).symm y) x = _
  rw [hinv]
  rfl

#print axioms s4_selected_curve_identity_divisor_form
end HodgeLean.Foundations.Program
