import HodgeLean.Foundations.Program.SchoenTransferE1ZeroTensor
import HodgeLean.Foundations.Program.SchoenTransferE1KunnethComponents

/-! The full ordered comparison in total degree zero. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The specified Künneth map is bijective in total degree zero for every power.
Source: Hatcher, Algebraic Topology, §3.2, constants and the external cup unit. -/
theorem s4_e1_kunneth_zero_degree
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    Function.Bijective (s4_e1_kunneth Y h 0) := by
  classical
  let I := {d : Fin h → ℕ // ∑ i, d i = 0}
  let d0 : I := ⟨fun _ => 0, s4_e1_sum_zero h⟩
  letI : Unique I :=
    { default := d0
      uniq := fun d => by
        apply Subtype.ext
        funext i
        exact (Finset.sum_eq_zero_iff.mp d.property) i (Finset.mem_univ i) }
  let E := s4_e1_directSumUniqueEquiv ℚ (fun d : I => s4_e1_tensor Y h d.val)
  let z0 := DirectSum.lof ℚ I (fun d => s4_e1_tensor Y h d.val) d0
    (s4_e1_zeroTensorUnit Y h)
  have hspan (z : ⨁ d : I, s4_e1_tensor Y h d.val) : ∃ q : ℚ, q • z0 = z := by
    obtain ⟨q, hq⟩ := s4_e1_zeroTensor_spanned Y h (E z)
    refine ⟨q, E.injective ?_⟩
    rw [map_smul]
    change q • (s4_e1_directSumUniqueEquiv ℚ
      (fun d : I => s4_e1_tensor Y h d.val)
        (DirectSum.lof ℚ I _ d0 (s4_e1_zeroTensorUnit Y h))) = E z
    erw [s4_e1_directSumUniqueEquiv_lof]
    exact hq
  have hunit : s4_e1_kunneth Y h 0 z0 = unitClass (g3_power Y h) := by
    change s4_e1_kunneth Y h 0
      (DirectSum.lof ℚ I _ d0 (s4_e1_zeroTensorUnit Y h)) = _
    erw [s4_e1_kunneth_component]
    dsimp only [d0]
    exact s4_e1_orderedCup_zero_unit Y (g3_power Y h) h (g3_proj Y h)
  constructor
  · intro z w hzw
    obtain ⟨q, hq⟩ := hspan z
    obtain ⟨r, hr⟩ := hspan w
    rw [← hq, ← hr, map_smul, map_smul, hunit] at hzw
    have hqr := (smul_left_injective ℚ (unitClass_ne_zero' (g3_power Y h))) hzw
    rw [← hq, ← hr, hqr]
  · intro x
    obtain ⟨q, hq⟩ := (cupProductOf_zeroEquiv (g3_power Y h)).surjective x
    refine ⟨q • z0, ?_⟩
    rw [map_smul, hunit]
    exact hq

#print axioms s4_e1_kunneth_zero_degree
end HodgeLean.Foundations.Program
