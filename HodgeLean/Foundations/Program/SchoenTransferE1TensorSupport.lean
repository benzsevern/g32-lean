import HodgeLean.Foundations.Program.SchoenTransferE1CurveAction

/-! Multidegree support of the ordered curve tensors. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs

namespace HodgeLean.Foundations.Program

/-- A multidegree with a factor above degree two has zero tensor space.
Source: Hatcher, Algebraic Topology, §3.2, tensor products and manifold cohomology vanishing. -/
theorem s4_e1_tensor_degree_vanishing
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (h : ℕ) (d : Fin h → ℕ) (i : Fin h) (hi : 2 < d i) :
    Subsingleton (s4_e1_tensor Y h d) := by
  induction h with
  | zero => exact i.elim0
  | succ h ih =>
      refine Fin.cases ?_ (fun j => ?_) i hi
      · intro h0
        letI := s4_e1_curve_cohomology_vanishing Y hdim h0
        change Subsingleton (HQ Y (d 0) ⊗[ℚ] s4_e1_tensor Y h (Fin.tail d))
        infer_instance
      · intro hj
        letI := ih (Fin.tail d) j hj
        change Subsingleton (HQ Y (d 0) ⊗[ℚ] s4_e1_tensor Y h (Fin.tail d))
        infer_instance

#print axioms s4_e1_tensor_degree_vanishing
end HodgeLean.Foundations.Program
