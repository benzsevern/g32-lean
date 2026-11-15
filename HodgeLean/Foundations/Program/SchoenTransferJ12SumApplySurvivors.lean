import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerMissingCoordinate
import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerPermutationRetraction
import HodgeLean.Foundations.Program.SchoenTransferJ12SumExpansion
import HodgeLean.Foundations.Program.SchoenTransferJ12PermutationSum

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped TensorProduct BigOperators
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- A linear map annihilating repeated assignments retains precisely the actual geometric permutation terms.
Source: the actual sum cup expansion and finite endomap reindexing. -/
theorem s4_selected_sum_cupMulti_apply
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E : HQ (g3_power Y n) n →ₗ[ℚ] V)
    (hE : ∀ a : Fin n → Fin n, ¬ Function.Surjective a → ∀ w : Fin n → HQ Y 1,
      E ((cupProductOf (g3_power Y n)).cupMulti n
        (fun i => homPullback (g3_proj Y n (a i)) 1 (w i))) = 0)
    (v : Fin n → HQ A 1) :
    E
      (homPullback (s4_sum f n) n ((cupProductOf A).cupMulti n v)) =
    E
      (∑ σ : Equiv.Perm (Fin n), homPullback (s2_permute Y n σ) n
        (s4_e1_oneCup Y n (PiTensorProduct.tprod ℚ (fun i => homPullback f 1 (v i))))) := by
  classical
  let F : (Fin n → Fin n) → HQ (g3_power Y n) n := fun a =>
    (cupProductOf (g3_power Y n)).cupMulti n
      (fun i => homPullback (g3_proj Y n (a i)) 1 (homPullback f 1 (v i)))
  rw [s4_selected_sum_cupMulti_expansion, map_sum, map_sum]
  change (∑ a, E (F a)) = _
  rw [s4_selected_sum_endomaps_on_surjections (fun a => E (F a))
    (fun a ha => hE a ha _)]
  rw [← Equiv.sum_comp (Equiv.symmEquiv (Fin n) (Fin n)) (fun σ => E (F σ))]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  dsimp only [F, Equiv.symmEquiv]
  simp only [s4_e1_oneCup, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  rw [s4_e1_cupMulti_pullback]
  congr 1
  funext i
  symm
  rw [← LinearMap.comp_apply, ← spec_homPullback_comp,
    s2_permute, s4_e1_lift_proj]
  rfl

#print axioms s4_selected_sum_cupMulti_apply
end HodgeLean.Foundations.Program
