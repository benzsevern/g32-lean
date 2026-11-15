import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDescentTopology
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusOperations
import HodgeLean.Adapters.GagaMaps

/-! # Holomorphic descent through the retained algebraic quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The ordered Abel sum is the point map of a morphism to the retained theta model. -/
theorem canonical_ordered_abel_algebraization (G : CanonicalAbelGeometry)
    (p : ComplexPoint G.Z) :
    ∃ v : g3_power G.Z (2 * G.k) ⟶
        model (C := ComplexPoint G.Z) (Module.finrank_fin_fun (n := 1) ℂ),
      Point.map v = fun u => theta (Module.finrank_fin_fun (n := 1) ℂ)
        (canonicalSymmetricAbel G p (Point.map G.γ u)) := by
  let h := Module.finrank_fin_fun (n := 1) ℂ
  letI := b3_periodLattice_finite (C := ComplexPoint G.Z) h
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint G.Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint G.Z) h)
  let J := model (C := ComplexPoint G.Z) h
  let X := g3_power G.Z (2 * G.k)
  let a := analyticAbel h p
  let s := canonicalSymmetricAbel G p
  let F : ComplexPoint X → ComplexPoint J := fun u => theta h (s (Point.map G.γ u))
  have hs (u : ComplexPoint X) : s (Point.map G.γ u) =
      ∑ i, a (Point.map (g3_proj G.Z (2 * G.k) i) u) := by
    have hh := canonicalSymmetricAbel_tuple G p
      (fun i => Point.map (g3_proj G.Z (2 * G.k) i) u)
    change s (Point.map G.γ (s2_lift (2 * G.k)
      (fun i => u ≫ g3_proj G.Z (2 * G.k) i))) = _ at hh
    rwa [s2e_lift_coordinates] at hh
  have ha := b3_abelJacobi_holomorphic h p a (b3_exists_abelJacobi h p).choose_spec
  have hsum : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ)
      𝓘(ℂ, b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint G.Z)) ω
      (fun u : ComplexPoint X => ∑ i, a (Point.map (g3_proj G.Z (2 * G.k) i) u)) := by
    intro u
    apply torus_sum_contMDiffAt
    intro i _
    exact (ha.comp (spec_contMDiff_pointMap X G.Z _ 1 (g3_proj G.Z (2 * G.k) i))) u
  have hF : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim J.left) → ℂ) ω F := by
    have hh := (theta_contMDiff (C := ComplexPoint G.Z) h).comp hsum
    convert hh using 1
    funext u
    exact congrArg (theta h) (hs u)
  exact gagam_algebraize X J F hF

#print axioms canonical_ordered_abel_algebraization
end HodgeLean.Foundations.Program.G32Native
