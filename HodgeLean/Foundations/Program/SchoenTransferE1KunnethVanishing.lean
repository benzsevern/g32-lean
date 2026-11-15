import HodgeLean.Foundations.Program.SchoenTransferE1TensorSupport

/-! The ordered comparison in degrees above the dimension bound. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- A multidegree above twice the number of factors contains a degree above two. -/
theorem s4_e1_high_total_degree_factor
    (h : ℕ) (d : Fin h → ℕ) (hn : 2 * h < ∑ i, d i) : ∃ i, 2 < d i := by
  by_contra he
  push_neg at he
  have hs := Finset.sum_le_sum (fun (i : Fin h) (_ : i ∈ Finset.univ) => he i)
  have hb : (∑ i, d i) ≤ 2 * h := by
    calc
      (∑ i, d i) ≤ ∑ _ : Fin h, (2 : ℕ) := hs
      _ = 2 * h := by simp [Nat.mul_comm]
  exact (not_le_of_gt hn) hb

/-- Above twice the power, both sides of the actual comparison vanish.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and §3.2, the degree bound. -/
theorem s4_e1_kunneth_above_top
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h n : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (hn : 2 * h < n) :
    Function.Bijective (s4_e1_kunneth Y h n) := by
  letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdim]; infer_instance
  letI : SmoothOfRelativeDimension h (g3_power Y h).hom := by
    simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power Y 1 h
  letI := j5d_subsingleton_HQ_of_lt (g3_power Y h) h hn
  letI (d : {d : Fin h → ℕ // ∑ i, d i = n}) :
      Subsingleton (s4_e1_tensor Y h d.val) := by
    obtain ⟨i, hi⟩ := s4_e1_high_total_degree_factor h d.val (d.property.symm ▸ hn)
    exact s4_e1_tensor_degree_vanishing Y hdim h d.val i hi
  constructor
  · exact Function.injective_of_subsingleton _
  · intro x
    exact ⟨0, Subsingleton.elim _ _⟩

#print axioms s4_e1_high_total_degree_factor
#print axioms s4_e1_kunneth_above_top
end HodgeLean.Foundations.Program
