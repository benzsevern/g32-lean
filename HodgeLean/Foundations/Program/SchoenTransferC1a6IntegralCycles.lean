import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralChains
import HodgeLean.Foundations.Program.CurveJacobianRest2Singular

/-! Actual integral singular cycles associated to smooth periodic loops. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Manifold
open HodgeLean.Adapters
open scoped ContDiff Simplicial
namespace HodgeLean.Foundations.Program
variable (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]

theorem s4_c1a6_pathChain_loop (γ : b3_SmoothLoop ℂ (ComplexPoint Y)) :
    s4_c1a6_pathChain Y γ.val γ.property.2 =
      AlgebraicTopology.Simplicial.chainOfSimplex ℤ (loopSimplex (b3Rest2_circ γ)) := by
  have h : b3Rest2_pathSimplex
      ⟨fun t => γ.val t, γ.property.2.continuous.comp continuous_subtype_val⟩ =
      loopSimplex (b3Rest2_circ γ) := by
    rw [← b3Rest2_pathSimplex_simplexPath (loopSimplex (b3Rest2_circ γ))]
    congr 1
    rw [spec_simplexPath_loopSimplex_aux]
    rfl
  exact congrArg (fun σ => AlgebraicTopology.Simplicial.chainOfSimplex ℤ σ) h

/-- A smooth periodic loop as a cycle in the actual integral singular chain complex. -/
def s4_c1a6_smoothLoopCycle (γ : b3_SmoothLoop ℂ (ComplexPoint Y)) :
    (s4_c1a6_chains Y).cycles 1 :=
  ((s4_c1a6_chains Y).sc 1).moduleCatCyclesIso.inv (loopCycle ℤ (b3Rest2_circ γ))

theorem s4_c1a6_smoothLoopCycle_chain (γ : b3_SmoothLoop ℂ (ComplexPoint Y)) :
    (s4_c1a6_chains Y).iCycles 1 (s4_c1a6_smoothLoopCycle Y γ) =
      s4_c1a6_pathChain Y γ.val γ.property.2 := by
  change (((s4_c1a6_chains Y).sc 1).moduleCatCyclesIso.inv ≫
    ((s4_c1a6_chains Y).sc 1).iCycles) (loopCycle ℤ (b3Rest2_circ γ)) = _
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
  exact (s4_c1a6_pathChain_loop Y γ).symm

end HodgeLean.Foundations.Program
