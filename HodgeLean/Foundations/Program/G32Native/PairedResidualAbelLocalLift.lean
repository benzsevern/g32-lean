import HodgeLean.Foundations.Program.G32Native.PairedResidualTorusChartLift
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelDescent
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusLocalLift
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaForms

/-! # Local analytic lifts of the specified algebraic Abel morphism -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- The actual algebraic morphism to the specified Jacobian is holomorphic after
transport through the original theta equivalence.
Source: Serre, GAGA, §3; Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_algebraic_abel_holomorphic
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (a : B ⟶ model (C := ComplexPoint Z) hOne) :
    letI := b3_periodLattice_finite (C := ComplexPoint Z) hOne
    letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) hOne)
    ContMDiff 𝓘(ℂ, Fin n → ℂ)
      𝓘(ℂ, b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint Z)) ω
      (fun b => (theta (C := ComplexPoint Z) hOne).symm (Point.map a b)) := by
  letI := b3_periodLattice_finite (C := ComplexPoint Z) hOne
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) hOne)
  exact (theta_symm_contMDiff (C := ComplexPoint Z) hOne).comp
    (spec_contMDiff_pointMap B (model (C := ComplexPoint Z) hOne) n _ a)

#print axioms residual_algebraic_abel_holomorphic

/-- The specified algebraic Abel map has actual analytic covering lifts in
its original native source chart.
Source: Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_algebraic_abel_local_lift
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (a : B ⟶ model (C := ComplexPoint Z) hOne) (b : ComplexPoint B) :
    letI := b3_periodLattice_finite (C := ComplexPoint Z) hOne
    letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) hOne)
    ∃ g : (Fin n → ℂ) → b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint Z),
      AnalyticAt ℂ g (localChart B n b b) ∧
      ∀ᶠ w in 𝓝 b, b3Rest2_covHom (g (localChart B n b w)) =
        (theta (C := ComplexPoint Z) hOne).symm (Point.map a w) := by
  letI := b3_periodLattice_finite (C := ComplexPoint Z) hOne
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) hOne)
  exact residual_torus_native_chart_lift B n
    (b3_periodF (Fin 1 → ℂ) (ComplexPoint Z))
    (fun w => (theta (C := ComplexPoint Z) hOne).symm (Point.map a w))
    (residual_algebraic_abel_holomorphic Z B n a) b

#print axioms residual_algebraic_abel_local_lift
end HodgeLean.Foundations.Program.G32Native
