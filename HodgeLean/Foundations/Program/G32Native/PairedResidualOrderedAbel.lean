import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaForms
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusOperations
import HodgeLean.Adapters.GagaMaps

/-! # Algebraization of the full ordered Abel sum -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The full ordered Abel sum is algebraic for every retained curve power.
Source: Serre, GAGA (1956), §3 Proposition 13; Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_ordered_abel_algebraic
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (p : ComplexPoint Z) :
    letI := AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let h := Module.finrank_fin_fun (n := 1) ℂ
    ∃ v : g3_power Z n ⟶ model (C := ComplexPoint Z) h,
      Point.map v = fun u => theta h
        (∑ i, analyticAbel h p (Point.map (g3_proj Z n i) u)) := by
  letI := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let h := Module.finrank_fin_fun (n := 1) ℂ
  letI := b3_periodLattice_finite (C := ComplexPoint Z) h
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) h)
  obtain ⟨hS, hP, hI, G, hG⟩ := projectiveGroup (C := ComplexPoint Z) h
  let J := model (C := ComplexPoint Z) h
  letI : Smooth J.hom := hS
  letI : IsProjective J.hom := hP
  letI : IsIntegral J.left := hI
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
  exact gagam_algebraize X J F ((theta_contMDiff (C := ComplexPoint Z) h).comp hsum)

#print axioms residual_ordered_abel_algebraic
end HodgeLean.Foundations.Program.G32Native
