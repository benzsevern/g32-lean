import HodgeLean.Foundations.Program.SchoenTransferSuppliers
import HodgeLean.Foundations.Program.SchoenTransferJ12SumReflectionProofs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Algebraic classes on the actual curve power reflect through the specified generating sum map.
Source: Schoen (1988), Remark 1.4, p. 6, and Corollary 3.1, p. 25; Lieberman (1968), Theorem 3. -/
theorem s4_selected_sum_reflects_cycles
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (hf : Function.Injective (homPullback f 1)) (k : ℕ)
    [IsIntegral (g3_power Y (2 * k)).left]
    [Smooth (g3_power Y (2 * k)).hom] [IsProjective (g3_power Y (2 * k)).hom]
    (x : HQ A (2 * k))
    (hx : homPullback (s4_sum f (2 * k)) (2 * k) x ∈
      cfd_cycleSpan (g3_power Y (2 * k)) k) :
    x ∈ cfd_cycleSpan A k := by
  by_cases hk0 : k = 0
  · subst k
    change x ∈ AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan A 0
    rw [algebraicCycleClassSpan_zero_eq_top_unconditional]
    trivial
  by_cases htop : k = TopologicalSpace.dim A.left
  · exact s4_top_degree_mem_cycleSpan A k htop.symm x
  by_cases hk : k < TopologicalSpace.dim A.left
  · exact s4_selected_sum_reflection_positive_dimension A Y (by omega) hdim f hf k x hx
  · letI : SmoothOfRelativeDimension (TopologicalSpace.dim A.left) A.hom :=
      SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
    letI := j5d_subsingleton_HQ_of_lt A (TopologicalSpace.dim A.left)
      (m := 2 * k) (by omega)
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _

#print axioms s4_selected_sum_reflects_cycles

end HodgeLean.Foundations.Program
