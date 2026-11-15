import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialDualParameter
import HodgeLean.Foundations.Program.SchoenCycleU1SectionJetRestriction

/-! # Actual polynomial curve section jets and algebraic infinitesimal evaluation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- On global parameter sections, the actual regular-section Taylor jet
is exactly evaluation by the specified dual-number parameter scheme map.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8;
Mathlib, `Scheme.ΓSpecIso_naturality`. -/
theorem s2e_u1_polynomialParameterPoint_sectionJet_top :
    let X := s2e_u1_specOver (Polynomial ℂ)
    letI := s2e_step1_sectionAlgebra X ⊤
    (s2e_u1_sectionJetAlong X ⊤ s2e_u1_polynomialParameterPoint
      (Filter.Eventually.of_forall (fun _ => by trivial))
      s2e_u1_polynomialParameterPoint_top_analytic).toRingHom =
        s2e_u1_specSectionEvaluation X.left s2e_u1_polynomialDualParameter.left ⊤ (by simp) := by
  let X := s2e_u1_specOver (Polynomial ℂ)
  letI := s2e_step1_sectionAlgebra X ⊤
  apply RingHom.ext
  intro a
  let p := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom.hom a
  have hg : s2e_u1_analyticGerm
      (fun t => Point.evaluate ⊤ a (s2e_u1_polynomialParameterPoint t))
      (s2e_u1_polynomialParameterPoint_top_analytic a) =
      s2e_u1_analyticGerm (fun t => p.eval t) (s2e_u1_polynomialFunction p).property := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun t => s2e_u1_polynomialParameterPoint_evaluate_top a t)
  change s2e_u1_analyticGermJet (s2e_u1_analyticGerm _
    (s2e_u1_polynomialParameterPoint_top_analytic a)) = _
  rw [hg]
  have hj := DFunLike.congr_fun s2e_u1_polynomialFunction_jet p
  change s2e_u1_analyticGermJet (s2e_u1_analyticGerm (fun t => p.eval t)
    (s2e_u1_polynomialFunction p).property) =
      s2e_u1_specSectionEvaluation (Spec (CommRingCat.of (Polynomial ℂ)))
        (Spec.map (CommRingCat.ofHom
          (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom)) ⊤ (by simp) a
  rw [s2e_u1_specSectionEvaluation_specMap_top]
  change s2e_u1_analyticGermJet (s2e_u1_analyticGerm (fun t => p.eval t)
    (s2e_u1_polynomialFunction p).property) =
      (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom p
  exact hj

/-- On every principal neighbourhood of the parameter origin, the actual
regular-section Taylor jet equals algebraic evaluation at ε.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, localization of tangent vectors. -/
theorem s2e_u1_polynomialParameterPoint_sectionJet_basicOpen
    (r : Γ((s2e_u1_specOver (Polynomial ℂ)).left, ⊤))
    (h0 : (s2e_u1_polynomialParameterPoint 0).underlying ∈
      (s2e_u1_specOver (Polynomial ℂ)).left.basicOpen r) :
    let X := s2e_u1_specOver (Polynomial ℂ)
    let W := X.left.basicOpen r
    letI := s2e_step1_sectionAlgebra X W
    (s2e_u1_sectionJetAlong X W s2e_u1_polynomialParameterPoint
      (s2e_u1_polynomialParameterPoint_regular_sections W h0).1
      (s2e_u1_polynomialParameterPoint_regular_sections W h0).2).toRingHom =
        s2e_u1_specSectionEvaluation X.left s2e_u1_polynomialDualParameter.left W
          (s2e_u1_polynomialDualParameter_basicOpen r h0) := by
  let X := s2e_u1_specOver (Polynomial ℂ)
  let W := X.left.basicOpen r
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAlgebra X ⊤
  have hXa : IsAffineOpen (⊤ : X.left.Opens) := by
    change IsAffineOpen (⊤ : (Spec (CommRingCat.of (Polynomial ℂ))).Opens)
    exact isAffineOpen_top _
  letI := hXa.isLocalization_basicOpen r
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  change (s2e_u1_sectionJetAlong X W s2e_u1_polynomialParameterPoint
      (s2e_u1_polynomialParameterPoint_regular_sections W h0).1
      (s2e_u1_polynomialParameterPoint_regular_sections W h0).2).toRingHom.comp
        (X.left.presheaf.map (homOfLE (X.left.basicOpen_le r)).op).hom =
    (s2e_u1_specSectionEvaluation X.left s2e_u1_polynomialDualParameter.left W
      (s2e_u1_polynomialDualParameter_basicOpen r h0)).comp
        (X.left.presheaf.map (homOfLE (X.left.basicOpen_le r)).op).hom
  rw [s2e_u1_sectionJetAlong_restrict X W ⊤ (X.left.basicOpen_le r)
    s2e_u1_polynomialParameterPoint _ _ _ s2e_u1_polynomialParameterPoint_top_analytic,
    s2e_u1_specSectionEvaluation_restrict X.left s2e_u1_polynomialDualParameter.left
      W ⊤ (X.left.basicOpen_le r) _ (by simp)]
  exact s2e_u1_polynomialParameterPoint_sectionJet_top

/-- On every actual parameter open containing the origin, Taylor evaluation
of all regular sections agrees with the specified algebraic dual-number map.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, affine localization. -/
theorem s2e_u1_polynomialParameterPoint_sectionJet_open
    (U : (s2e_u1_specOver (Polynomial ℂ)).left.Opens)
    (h0 : (s2e_u1_polynomialParameterPoint 0).underlying ∈ U) :
    let X := s2e_u1_specOver (Polynomial ℂ)
    letI := s2e_step1_sectionAlgebra X U
    (s2e_u1_sectionJetAlong X U s2e_u1_polynomialParameterPoint
      (s2e_u1_polynomialParameterPoint_regular_sections U h0).1
      (s2e_u1_polynomialParameterPoint_regular_sections U h0).2).toRingHom =
        s2e_u1_specSectionEvaluation X.left s2e_u1_polynomialDualParameter.left U
          (s2e_u1_polynomialDualParameter_open U h0) := by
  let X := s2e_u1_specOver (Polynomial ℂ)
  letI := s2e_step1_sectionAlgebra X U
  have hXa : IsAffineOpen (⊤ : X.left.Opens) := by
    change IsAffineOpen (⊤ : (Spec (CommRingCat.of (Polynomial ℂ))).Opens)
    exact isAffineOpen_top _
  obtain ⟨r, hrU, hr0⟩ := hXa.exists_basicOpen_le
    (⟨(s2e_u1_polynomialParameterPoint 0).underlying, h0⟩ : U) (by trivial)
  let W := X.left.basicOpen r
  letI := s2e_step1_sectionAlgebra X W
  have ha := s2e_u1_sectionJetAlong_restrict X W U hrU s2e_u1_polynomialParameterPoint
    (s2e_u1_polynomialParameterPoint_regular_sections W hr0).1
    (s2e_u1_polynomialParameterPoint_regular_sections U h0).1
    (s2e_u1_polynomialParameterPoint_regular_sections W hr0).2
    (s2e_u1_polynomialParameterPoint_regular_sections U h0).2
  have hb := s2e_u1_specSectionEvaluation_restrict X.left s2e_u1_polynomialDualParameter.left
    W U hrU (s2e_u1_polynomialDualParameter_basicOpen r hr0)
      (s2e_u1_polynomialDualParameter_open U h0)
  calc
    _ = (s2e_u1_sectionJetAlong X W s2e_u1_polynomialParameterPoint
      (s2e_u1_polynomialParameterPoint_regular_sections W hr0).1
      (s2e_u1_polynomialParameterPoint_regular_sections W hr0).2).toRingHom.comp
        (X.left.presheaf.map (homOfLE hrU).op).hom := ha.symm
    _ = (s2e_u1_specSectionEvaluation X.left s2e_u1_polynomialDualParameter.left W
      (s2e_u1_polynomialDualParameter_basicOpen r hr0)).comp
        (X.left.presheaf.map (homOfLE hrU).op).hom := by
      rw [s2e_u1_polynomialParameterPoint_sectionJet_basicOpen r hr0]
    _ = _ := hb

end HodgeLean.Foundations.Program
