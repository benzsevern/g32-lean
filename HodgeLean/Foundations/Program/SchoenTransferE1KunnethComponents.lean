import HodgeLean.Foundations.Program.SchoenTransferE1CupComparison

/-! The specified ordered Künneth map on its actual summands. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- The indexed degree-one cup factors through the actual ordered cup map.
Source: Hatcher, Algebraic Topology, §3.2, compatibility of tensor conventions. -/
theorem s4_e1_oneCup_ordered_factor
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    s4_e1_oneCup Y h =
      (HQ.castEquiv (g3_power Y h) (s4_e1_sum_one h)).toLinearMap.comp
        ((s4_e1_orderedCup Y (g3_power Y h) h (fun _ => 1) (g3_proj Y h)).comp
          (s4_e1_oneTensorEquiv Y h).symm.toLinearMap) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [s4_e1_oneCup, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearMap.compMultilinearMap_apply]
  exact (s4_e1_orderedCup_one_pure Y (g3_power Y h) h (g3_proj Y h) v).symm

/-- Each component of the specified Künneth map is the ordered projection cup,
with only the indicated transport of its total degree.
Source: Hatcher, Algebraic Topology, §3.2, the external cup product. -/
theorem s4_e1_kunneth_component
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h n : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (d : {d : Fin h → ℕ // ∑ i, d i = n}) (v : s4_e1_tensor Y h d.val) :
    s4_e1_kunneth Y h n (DirectSum.lof ℚ _ _ d v) =
      HQ.castEquiv (g3_power Y h) d.property
        (s4_e1_orderedCup Y (g3_power Y h) h d.val (g3_proj Y h) v) := by
  rcases d with ⟨d, hd⟩
  subst n
  simp only [s4_e1_kunneth, DirectSum.toModule_lof, HQ.castEquiv_apply_self]
  rfl

/-- The indexed degree-one cup is the literal all-degree-one Künneth component.
Source: Schoen (1988), Lemma 1.2, p. 6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_oneCup_kunneth_factor
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    s4_e1_oneCup Y h = (s4_e1_kunneth Y h h).comp
      ((DirectSum.lof ℚ {d : Fin h → ℕ // ∑ i, d i = h}
        (fun d => s4_e1_tensor Y h d.val) ⟨fun _ => 1, s4_e1_sum_one h⟩).comp
          (s4_e1_oneTensorEquiv Y h).symm.toLinearMap) := by
  rw [s4_e1_oneCup_ordered_factor]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  exact (s4_e1_kunneth_component Y h h ⟨fun _ => 1, s4_e1_sum_one h⟩
    ((s4_e1_oneTensorEquiv Y h).symm v)).symm

/-- The all-degree-one cup image lies in the image of the specified full comparison.
Source: Schoen (1988), Lemma 1.2, p. 6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_oneCup_range_le_kunneth_range
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    LinearMap.range (s4_e1_oneCup Y h) ≤ LinearMap.range (s4_e1_kunneth Y h h) := by
  rw [s4_e1_oneCup_kunneth_factor]
  exact LinearMap.range_comp_le_range _ _

#print axioms s4_e1_oneCup_ordered_factor
#print axioms s4_e1_kunneth_component
#print axioms s4_e1_oneCup_kunneth_factor
#print axioms s4_e1_oneCup_range_le_kunneth_range
end HodgeLean.Foundations.Program
