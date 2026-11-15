import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialSectionJet

/-! # Actual scheme-valued polynomial curves and their section jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Restriction of an actual polynomial scheme curve to dual numbers lies
in every target open containing its actual base point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, pullback of neighbourhoods. -/
theorem s2e_u1_polynomialCurve_dual_open
    (X : Over (Spec ↧ℂ)) (f : s2e_u1_specOver (Polynomial ℂ) ⟶ X)
    (U : X.left.Opens)
    (h0 : (Point.map f (s2e_u1_polynomialParameterPoint 0)).underlying ∈ U) :
    ⊤ ≤ (s2e_u1_polynomialDualParameter ≫ f).left ⁻¹ᵁ U := by
  have h0' : (s2e_u1_polynomialParameterPoint 0).underlying ∈ f.left ⁻¹ᵁ U := h0
  have hpre := s2e_u1_polynomialDualParameter_open (f.left ⁻¹ᵁ U) h0'
  intro z hz
  exact hpre hz

/-- Taylor evaluation of a polynomial scheme curve agrees with its actual
restriction to the specified dual-number parameter.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_u1_polynomialCurve_sectionJet
    (X : Over (Spec ↧ℂ)) (f : s2e_u1_specOver (Polynomial ℂ) ⟶ X)
    (U : X.left.Opens)
    (h0 : (Point.map f (s2e_u1_polynomialParameterPoint 0)).underlying ∈ U) :
    letI := s2e_step1_sectionAlgebra X U
    (s2e_u1_sectionJetAlong X U
      (fun t => Point.map f (s2e_u1_polynomialParameterPoint t))
      (s2e_u1_polynomialCurve_regular_sections X f U h0).1
      (s2e_u1_polynomialCurve_regular_sections X f U h0).2).toRingHom =
      s2e_u1_specSectionEvaluation X.left
        (s2e_u1_polynomialDualParameter ≫ f).left U
        (s2e_u1_polynomialCurve_dual_open X f U h0) := by
  let Y := s2e_u1_specOver (Polynomial ℂ)
  let W := f.left ⁻¹ᵁ U
  have hW : (s2e_u1_polynomialParameterPoint 0).underlying ∈ W := h0
  letI := s2e_step1_sectionAlgebra Y W
  letI := s2e_step1_sectionAlgebra X U
  have hm := s2e_u1_sectionJetAlong_map Y X f U
    s2e_u1_polynomialParameterPoint
    (s2e_u1_polynomialParameterPoint_regular_sections W hW).1
    (s2e_u1_polynomialCurve_regular_sections X f U h0).1
    (s2e_u1_polynomialParameterPoint_regular_sections W hW).2
    (s2e_u1_polynomialCurve_regular_sections X f U h0).2
  have hr := congrArg AlgHom.toRingHom hm
  change (s2e_u1_sectionJetAlong Y W s2e_u1_polynomialParameterPoint
    (s2e_u1_polynomialParameterPoint_regular_sections W hW).1
    (s2e_u1_polynomialParameterPoint_regular_sections W hW).2).toRingHom.comp
    (f.left.appLE U W le_rfl).hom = _ at hr
  rw [← hr, s2e_u1_polynomialParameterPoint_sectionJet_open W hW]
  exact s2e_u1_specSectionEvaluation_comp Y.left X.left
    s2e_u1_polynomialDualParameter.left f.left U W le_rfl _ _

/-- Derivatives of actual section evaluations are the variation components
of the actual polynomial curve's dual-number restriction.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors and derivations. -/
theorem s2e_u1_polynomialCurve_section_derivative
    (X : Over (Spec ↧ℂ)) (f : s2e_u1_specOver (Polynomial ℂ) ⟶ X)
    (U : X.left.Opens)
    (h0 : (Point.map f (s2e_u1_polynomialParameterPoint 0)).underlying ∈ U)
    (a : Γ(X.left, U)) :
    deriv (fun t => Point.evaluate U a
      (Point.map f (s2e_u1_polynomialParameterPoint t))) 0 =
      (s2e_u1_specSectionEvaluation X.left
        (s2e_u1_polynomialDualParameter ≫ f).left U
        (s2e_u1_polynomialCurve_dual_open X f U h0) a).snd := by
  letI := s2e_step1_sectionAlgebra X U
  have h := congrArg (fun σ : Γ(X.left, U) →+* DualNumber ℂ => (σ a).snd)
    (s2e_u1_polynomialCurve_sectionJet X f U h0)
  change (s2e_u1_analyticGermJet (s2e_u1_analyticGerm
    (fun t => Point.evaluate U a (Point.map f (s2e_u1_polynomialParameterPoint t)))
    ((s2e_u1_polynomialCurve_regular_sections X f U h0).2 a))).snd = _ at h
  simpa only [s2e_u1_analyticGermJet_representative, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] using h

end HodgeLean.Foundations.Program
