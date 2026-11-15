import HodgeLean.Foundations.Program.SchoenTransferComplexPullback
import HodgeLean.Foundations.Program.SchoenTransferSuppliers

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- On complex exterior generators the actual sum pullback expands in degree-one coordinate sums.
Source: Schoen (1988), Remark 1.4, p. 6; naturality of cup products. -/
theorem s4_sum_complex_cup_generators
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (v : Fin h → ℂ ⊗[ℚ] HQ A 1) :
    letI := (torusCohomology_cupProductOf A).finite
    ((homPullback (s4_sum f h) h).baseChange ℂ ∘ₗ
      ((cupProductOf A).cupWedgeMap h).baseChange ℂ ∘ₗ
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv
        (V := HQ A 1) h).symm.toLinearMap) (exteriorPower.ιMulti ℂ h v) =
      (cupProductOf (g3_power Y h)).cupMultiC h
        (fun i => ∑ j, (homPullback (g3_proj Y h j) 1).baseChange ℂ
          ((homPullback f 1).baseChange ℂ (v i))) := by
  letI := (torusCohomology_cupProductOf A).finite
  have hc := congrFun (congrArg DFunLike.coe (s4_complex_cup_linearization A h)) v
  simp only [AlternatingMap.coe_multilinearMap, LinearMap.compAlternatingMap_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hc, s4_complex_pullback_cupMulti]
  congr 1
  funext i
  rw [s4_sum_pullback_one A Y f h]
  have hs := map_sum (LinearMap.baseChangeHom ℚ ℂ (HQ A 1) (HQ (g3_power Y h) 1))
    (fun j : Fin h => (homPullback (g3_proj Y h j) 1).comp (homPullback f 1)) Finset.univ
  change (∑ j : Fin h, (homPullback (g3_proj Y h j) 1).comp (homPullback f 1)).baseChange ℂ =
    ∑ j : Fin h, ((homPullback (g3_proj Y h j) 1).comp (homPullback f 1)).baseChange ℂ at hs
  rw [hs, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]

end HodgeLean.Foundations.Program
