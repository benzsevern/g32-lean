import HodgeLean.Foundations.Program.SchoenCycleU1SectionJets

/-! # Divisor coefficient jets on actual affine charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Equal actual curve jets give equal dual-number polynomials for every
polynomial of regular sections on their common affine chart.
Source: Hartshorne, Algebraic Geometry, II.8, functoriality of tangent vectors. -/
theorem s2e_u1_curveJet_polynomial
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hUa : IsAffineOpen U)
    (c d : ℂ → ComplexPoint X)
    (hU : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ U)
    (hV : ∀ᶠ z in 𝓝 (0 : ℂ), (d z).underlying ∈ U)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun z => Point.evaluate U s (c z)) 0)
    (hd : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun z => Point.evaluate U s (d z)) 0)
    (he : s2e_u1_curveJet X U hUa c hU hc = s2e_u1_curveJet X U hUa d hV hd)
    (Q : Polynomial Γ(X.left, U)) :
    letI := s2e_step1_sectionAlgebra X U
    Q.map (s2e_u1_sectionJetAlong X U c hU hc).toRingHom =
      Q.map (s2e_u1_sectionJetAlong X U d hV hd).toRingHom := by
  letI := s2e_step1_sectionAlgebra X U
  rw [s2e_u1_curveJet_sections X U hUa c d hU hV hc hd he]

/-- A curve jet equal to the constant curve jet has zero first variation on
every regular polynomial coefficient, including coefficients at repeated roots.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors as derivations. -/
theorem s2e_u1_curveJet_stationary_coefficients
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hUa : IsAffineOpen U)
    (c : ℂ → ComplexPoint X)
    (hU : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ U)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun z => Point.evaluate U s (c z)) 0)
    (h0 : (c 0).underlying ∈ U)
    (he : s2e_u1_curveJet X U hUa c hU hc =
      s2e_u1_curveJet X U hUa (fun _ => c 0)
        (Filter.Eventually.of_forall (fun _ => h0)) (fun _ => analyticAt_const))
    (Q : Polynomial Γ(X.left, U)) (j : ℕ) :
    deriv (fun z => Point.evaluate U (Q.coeff j) (c z)) 0 = 0 := by
  letI := s2e_step1_sectionAlgebra X U
  have hh := s2e_u1_curveJet_sections X U hUa c (fun _ => c 0) hU
    (Filter.Eventually.of_forall (fun _ => h0)) hc (fun _ => analyticAt_const) he
  have hs := congrArg (fun φ : Γ(X.left, U) →ₐ[ℂ] DualNumber ℂ =>
    TrivSqZeroExt.snd (φ (Q.coeff j))) hh
  change TrivSqZeroExt.snd (s2e_u1_analyticGermJet
      (s2e_u1_analyticGerm (fun z => Point.evaluate U (Q.coeff j) (c z)) (hc _))) =
    TrivSqZeroExt.snd (s2e_u1_analyticGermJet
      (s2e_u1_analyticGerm (fun _ : ℂ => Point.evaluate U (Q.coeff j) (c 0))
        analyticAt_const)) at hs
  simpa only [s2e_u1_analyticGermJet_representative,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    zero_add, deriv_const] using hs

end HodgeLean.Foundations.Program
