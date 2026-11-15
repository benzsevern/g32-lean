import HodgeLean.Foundations.Program.SchoenCycleU1SectionJets

/-! # Stationary scheme jets detected on regular sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Zero first derivatives on all regular sections give equality of the actual
scheme-valued curve jet with the constant curve jet.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, affine tangent vectors. -/
theorem s2e_u1_curveJet_stationary_of_regular_derivatives
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hUa : IsAffineOpen U)
    (c : ℂ → ComplexPoint X)
    (hU : ∀ᶠ t in 𝓝 (0 : ℂ), (c t).underlying ∈ U)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun t => Point.evaluate U s (c t)) 0)
    (h0 : (c 0).underlying ∈ U)
    (hder : ∀ s : Γ(X.left, U), deriv (fun t => Point.evaluate U s (c t)) 0 = 0) :
    s2e_u1_curveJet X U hUa c hU hc =
      s2e_u1_curveJet X U hUa (fun _ => c 0)
        (Filter.Eventually.of_forall (fun _ => h0)) (fun _ => analyticAt_const) := by
  letI := s2e_step1_sectionAlgebra X U
  have he : s2e_u1_sectionJetAlong X U c hU hc =
      s2e_u1_sectionJetAlong X U (fun _ => c 0)
        (Filter.Eventually.of_forall (fun _ => h0)) (fun _ => analyticAt_const) := by
    apply AlgHom.ext
    intro s
    change s2e_u1_analyticGermJet (s2e_u1_analyticGerm _ (hc s)) =
      s2e_u1_analyticGermJet (s2e_u1_analyticGerm _ analyticAt_const)
    rw [s2e_u1_analyticGermJet_representative, s2e_u1_analyticGermJet_representative,
      hder, deriv_const]
  unfold s2e_u1_curveJet
  rw [he]

end HodgeLean.Foundations.Program
