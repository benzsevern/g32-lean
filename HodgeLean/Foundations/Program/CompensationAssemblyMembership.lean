import HodgeLean.Foundations.Program.CompensationAssemblyDefs

/-! # Proofs for compensation assembly -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations
open HodgeLean.Foundations.HermitianForm HodgeLean.Papers ComplexConjugate
namespace HodgeLean.Foundations.Program

theorem cq_cycleClass_mem_span (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (c : AlgebraicCycle X.left ℚ) :
    ccm3_cycleClass X q c ∈ algebraicCycleClassSpan X q := by
  have hgen (z : {z : X.left // Order.coheight z = q}) :
      cycleComponentSheafClass X z.1 z.2 ∈ algebraicCycleClassSpan X q := by
    have hle : Submodule.span ℚ ({cycleComponentSheafClass X z.1 z.2} : Set (HQ X (2 * q))) ≤
        algebraicCycleClassSpan X q := by
      unfold algebraicCycleClassSpan
      exact le_sSup ⟨z.1, z.2, rfl⟩
    exact hle (Submodule.subset_span (Set.mem_singleton _))
  exact finsum_induction (fun v : HQ X (2 * q) => v ∈ algebraicCycleClassSpan X q)
    (Submodule.zero_mem _) (fun a b ha hb => Submodule.add_mem _ ha hb)
    (fun z => Submodule.smul_mem (algebraicCycleClassSpan X q) (c z.1) (hgen z))

end HodgeLean.Foundations.Program
