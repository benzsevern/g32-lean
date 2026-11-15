import HodgeLean.Foundations.Program.G32ContractionClassMultiply
import HodgeLean.Foundations.Program.G32ContractionScalar
import HodgeLean.Foundations.Program.CycleFoundationsPullbackSpan
import HodgeLean.Adapters.DegreeZeroUnconditional
import HodgeLean.Adapters.KleimanProduct

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf algebraicCycleClassSpan

theorem g32c_cupC_span (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (p q s : ℕ) (h : 2 * p + 2 * q = 2 * s)
    (a : ℂ ⊗[ℚ] HQ Y (2 * p)) (b : ℂ ⊗[ℚ] HQ Y (2 * q))
    (ha : a ∈ (algebraicCycleClassSpan Y p).baseChange ℂ)
    (hb : b ∈ (algebraicCycleClassSpan Y q).baseChange ℂ) :
    (cupProductOf Y).cupC h a b ∈ (algebraicCycleClassSpan Y s).baseChange ℂ := by
  apply g32c_baseChange_bilinear_mem (V := HQ Y (2 * p)) (W := HQ Y (2 * q))
    (T := HQ Y (2 * s)) _ _ _ _ _ a ha b hb
  intro c d v hv w hw
  rw [CupProduct.cupC_tmul (cupProductOf Y) h c d v w]
  exact Submodule.tmul_mem_baseChange_of_mem _
    ((hc9k_cycleClassMultiplicative Y).mem_of_eq h v w hv hw)


end HodgeLean.Foundations.Program
