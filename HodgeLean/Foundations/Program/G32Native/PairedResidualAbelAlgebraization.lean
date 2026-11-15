import HodgeLean.Foundations.Program.SchoenCycleGenusTransport
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusOperations
import HodgeLean.Adapters.GagaMaps

/-! # Algebraic ordered Abel sums for the supplied curve -/
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

/-- Every ordered Abel sum is algebraic on the actual supplied curve power. -/
theorem residual_ordered_abel_algebraization (n : ℕ) (p : ComplexPoint Z) :
    ∃ v : g3_power Z n ⟶ model (C := ComplexPoint Z) hOne,
      Point.map v = fun u => theta hOne
        (∑ i, analyticAbel hOne p (Point.map (g3_proj Z n i) u)) := by
  let h := Module.finrank_fin_fun (n := 1) ℂ
  letI := b3_periodLattice_finite (C := ComplexPoint Z) h
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) h)
  let J := model (C := ComplexPoint Z) h
  let X := g3_power Z n
  let a := analyticAbel h p
  let F : ComplexPoint X → ComplexPoint J := fun u => theta h
    (∑ i, a (Point.map (g3_proj Z n i) u))
  have ha := b3_abelJacobi_holomorphic h p a (b3_exists_abelJacobi h p).choose_spec
  have hsum : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ)
      𝓘(ℂ, b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint Z)) ω
      (fun u : ComplexPoint X => ∑ i, a (Point.map (g3_proj Z n i) u)) := by
    intro u
    apply torus_sum_contMDiffAt
    intro i _
    exact (ha.comp (spec_contMDiff_pointMap X Z _ 1 (g3_proj Z n i))) u
  have hF : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim J.left) → ℂ) ω F :=
    (theta_contMDiff (C := ComplexPoint Z) h).comp hsum
  exact gagam_algebraize X J F hF

#print axioms residual_ordered_abel_algebraization
end HodgeLean.Foundations.Program.G32Native
