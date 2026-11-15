import HodgeLean.Foundations.Program.SchoenTransferSuppliers
import HodgeLean.Foundations.Program.SchoenTransferE1

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Pullback of a degree-one cup by the actual sum expands over coordinate assignments. -/
theorem s4_selected_sum_cupMulti_expansion
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (n r : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom] (v : Fin r → HQ A 1) :
    homPullback (s4_sum f n) r ((cupProductOf A).cupMulti r v) =
      ∑ a : Fin r → Fin n, (cupProductOf (g3_power Y n)).cupMulti r
        (fun i => homPullback (g3_proj Y n (a i)) 1 (homPullback f 1 (v i))) := by
  classical
  rw [s4_e1_cupMulti_pullback]
  have h (i : Fin r) : homPullback (s4_sum f n) 1 (v i) =
      ∑ j : Fin n, homPullback (g3_proj Y n j) 1 (homPullback f 1 (v i)) := by
    rw [s4_sum_pullback_one, LinearMap.sum_apply]
    rfl
  simp only [h]
  exact ((cupProductOf (g3_power Y n)).cupMulti r).map_sum _

#print axioms s4_selected_sum_cupMulti_expansion
end HodgeLean.Foundations.Program
