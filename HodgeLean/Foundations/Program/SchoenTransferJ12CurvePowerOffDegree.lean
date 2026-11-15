import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerExtraction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped DirectSum TensorProduct BigOperators
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Extraction annihilates each actual Künneth summand with a different multidegree. -/
theorem s4_selected_curve_power_extract_off_degree
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (d : {d : Fin n → ℕ // ∑ i, d i = n})
    (hd : d ≠ ⟨fun _ => 1, s4_e1_sum_one n⟩) (v : s4_e1_tensor Y n d.val) :
    s4_selected_curve_power_extract Y hdim n
      (s4_e1_kunneth Y n n
        (DirectSum.lof ℚ {d : Fin n → ℕ // ∑ i, d i = n}
          (fun d => s4_e1_tensor Y n d.val) d v)) = 0 := by
  classical
  let K := LinearEquiv.ofBijective (s4_e1_kunneth Y n n)
    (s4_e1_power_kunneth Y hdim n n)
  change s4_e1_oneTensorEquiv Y n
    ((DirectSum.component ℚ {d : Fin n → ℕ // ∑ i, d i = n}
      (fun d => s4_e1_tensor Y n d.val) ⟨fun _ => 1, s4_e1_sum_one n⟩)
        (K.symm (K (DirectSum.lof ℚ {d : Fin n → ℕ // ∑ i, d i = n}
          (fun d => s4_e1_tensor Y n d.val) d v)))) = 0
  rw [K.symm_apply_apply]
  simp only [DirectSum.component.of, hd, dite_false, map_zero]

#print axioms s4_selected_curve_power_extract_off_degree
end HodgeLean.Foundations.Program
