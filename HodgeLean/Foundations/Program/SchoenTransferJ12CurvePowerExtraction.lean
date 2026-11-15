import HodgeLean.Foundations.Program.SchoenTransferE1

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped DirectSum TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The rational all-degree-one component of the actual curve-power cohomology. -/
def s4_selected_curve_power_extract
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom] :
    HQ (g3_power Y n) n →ₗ[ℚ] (⨂[ℚ] _ : Fin n, HQ Y 1) :=
  (s4_e1_oneTensorEquiv Y n).toLinearMap.comp
    ((DirectSum.component ℚ {d : Fin n → ℕ // ∑ i, d i = n}
      (fun d => s4_e1_tensor Y n d.val) ⟨fun _ => 1, s4_e1_sum_one n⟩).comp
        (LinearEquiv.ofBijective (s4_e1_kunneth Y n n)
          (s4_e1_power_kunneth Y hdim n n)).symm.toLinearMap)

/-- Extracting the all-degree-one cup image recovers the original ordered tensor. -/
theorem s4_selected_curve_power_extract_oneCup
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom] :
    (s4_selected_curve_power_extract Y hdim n).comp (s4_e1_oneCup Y n) = LinearMap.id := by
  let K := LinearEquiv.ofBijective (s4_e1_kunneth Y n n)
    (s4_e1_power_kunneth Y hdim n n)
  rw [s4_e1_oneCup_kunneth_factor]
  apply LinearMap.ext
  intro v
  change s4_e1_oneTensorEquiv Y n
    ((DirectSum.component ℚ {d : Fin n → ℕ // ∑ i, d i = n}
      (fun d => s4_e1_tensor Y n d.val) ⟨fun _ => 1, s4_e1_sum_one n⟩)
        (K.symm (K ((DirectSum.lof ℚ {d : Fin n → ℕ // ∑ i, d i = n}
          (fun d => s4_e1_tensor Y n d.val) ⟨fun _ => 1, s4_e1_sum_one n⟩)
            ((s4_e1_oneTensorEquiv Y n).symm v))))) = v
  rw [K.symm_apply_apply, DirectSum.component.lof_self, LinearEquiv.apply_symm_apply]

#print axioms s4_selected_curve_power_extract_oneCup
end HodgeLean.Foundations.Program
