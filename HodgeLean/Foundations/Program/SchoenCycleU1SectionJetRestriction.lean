import HodgeLean.Foundations.Program.SchoenCycleU1SectionJets

/-! # Restriction compatibility of actual regular-section Taylor jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Actual section Taylor jets commute with restriction to a smaller open
containing the parameter curve near zero.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8;
HodgeConjecture, `Point.evaluate_res`. -/
theorem s2e_u1_sectionJetAlong_restrict
    (X : Over (Spec ↧ℂ)) (U V : X.left.Opens) (hUV : U ≤ V)
    (c : ℂ → ComplexPoint X)
    (hU : ∀ᶠ t in 𝓝 (0 : ℂ), (c t).underlying ∈ U)
    (hV : ∀ᶠ t in 𝓝 (0 : ℂ), (c t).underlying ∈ V)
    (ha : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun t => Point.evaluate U s (c t)) 0)
    (hb : ∀ s : Γ(X.left, V), AnalyticAt ℂ (fun t => Point.evaluate V s (c t)) 0) :
    letI := s2e_step1_sectionAlgebra X U
    letI := s2e_step1_sectionAlgebra X V
    (s2e_u1_sectionJetAlong X U c hU ha).toRingHom.comp
      (X.left.presheaf.map (homOfLE hUV).op).hom =
        (s2e_u1_sectionJetAlong X V c hV hb).toRingHom := by
  letI := s2e_step1_sectionAlgebra X U
  letI := s2e_step1_sectionAlgebra X V
  apply RingHom.ext
  intro s
  change s2e_u1_analyticGermJet (s2e_u1_analyticGerm _ (ha _)) =
    s2e_u1_analyticGermJet (s2e_u1_analyticGerm _ (hb s))
  congr 1
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards [hU] with t ht
  exact (Point.evaluate_res hUV s (c t) ht).symm

end HodgeLean.Foundations.Program
