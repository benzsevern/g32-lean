import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialParameterPoint

/-! # Regular sections along the actual polynomial parameter curve -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Every regular section near the parameter origin evaluates analytically
along the actual polynomial parameter points, using affine localization.
Source: Hartshorne, Algebraic Geometry, II.2, principal affine opens;
HodgeConjecture, `Point.exists_evaluate_basicOpen_eq_div`. -/
theorem s2e_u1_polynomialParameterPoint_regular_sections
    (U : (s2e_u1_specOver (Polynomial ℂ)).left.Opens)
    (h0 : (s2e_u1_polynomialParameterPoint 0).underlying ∈ U) :
    (∀ᶠ t in 𝓝 (0 : ℂ), (s2e_u1_polynomialParameterPoint t).underlying ∈ U) ∧
      ∀ a : Γ((s2e_u1_specOver (Polynomial ℂ)).left, U),
        AnalyticAt ℂ (fun t => Point.evaluate U a (s2e_u1_polynomialParameterPoint t)) 0 := by
  let X := s2e_u1_specOver (Polynomial ℂ)
  have hXa : IsAffineOpen (⊤ : X.left.Opens) := by
    change IsAffineOpen (⊤ : (Spec (CommRingCat.of (Polynomial ℂ))).Opens)
    exact isAffineOpen_top _
  obtain ⟨r, hrU, hr0⟩ := hXa.exists_basicOpen_le
    (⟨(s2e_u1_polynomialParameterPoint 0).underlying, h0⟩ : U) (by trivial)
  have hrne : Point.evaluate ⊤ r (s2e_u1_polynomialParameterPoint 0) ≠ 0 :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r
      (s2e_u1_polynomialParameterPoint 0) (by trivial)).mp hr0
  have hn := (s2e_u1_polynomialParameterPoint_top_analytic r).continuousAt.eventually_ne hrne
  have hbasic : ∀ᶠ t in 𝓝 (0 : ℂ),
      (s2e_u1_polynomialParameterPoint t).underlying ∈ X.left.basicOpen r := by
    filter_upwards [hn] with t ht
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r
      (s2e_u1_polynomialParameterPoint t) (by trivial)).mpr ht
  refine ⟨hbasic.mono (fun _ ht => hrU ht), ?_⟩
  intro a
  let ar := (X.left.presheaf.map (homOfLE hrU).op).hom a
  obtain ⟨k, p, hp⟩ := Point.exists_evaluate_basicOpen_eq_div (X := X) hXa r ar
  have ha : AnalyticAt ℂ (fun t =>
      Point.evaluate ⊤ p (s2e_u1_polynomialParameterPoint t) /
        Point.evaluate ⊤ r (s2e_u1_polynomialParameterPoint t) ^ k) 0 :=
    (s2e_u1_polynomialParameterPoint_top_analytic p).div
      ((s2e_u1_polynomialParameterPoint_top_analytic r).pow k) (pow_ne_zero k hrne)
  apply ha.congr
  filter_upwards [hbasic] with t ht
  rw [Point.evaluate_res hrU a (s2e_u1_polynomialParameterPoint t) ht]
  exact (hp (s2e_u1_polynomialParameterPoint t) ht).symm

/-- Every actual morphism from the polynomial parameter scheme has analytic
regular-section evaluations near its base point, on arbitrary target opens.
Source: Hartshorne, Algebraic Geometry, II.2, pullback of regular sections;
HodgeConjecture, `Point.evaluate_map`. -/
theorem s2e_u1_polynomialCurve_regular_sections
    (X : Over (Spec ↧ℂ)) (f : s2e_u1_specOver (Polynomial ℂ) ⟶ X)
    (U : X.left.Opens)
    (h0 : (Point.map f (s2e_u1_polynomialParameterPoint 0)).underlying ∈ U) :
    (∀ᶠ t in 𝓝 (0 : ℂ),
      (Point.map f (s2e_u1_polynomialParameterPoint t)).underlying ∈ U) ∧
      ∀ a : Γ(X.left, U), AnalyticAt ℂ
        (fun t => Point.evaluate U a (Point.map f (s2e_u1_polynomialParameterPoint t))) 0 := by
  have h0' : (s2e_u1_polynomialParameterPoint 0).underlying ∈ f.left ⁻¹ᵁ U := h0
  obtain ⟨hU, hA⟩ := s2e_u1_polynomialParameterPoint_regular_sections (f.left ⁻¹ᵁ U) h0'
  refine ⟨hU, ?_⟩
  intro a
  have he : (fun t => Point.evaluate U a (Point.map f (s2e_u1_polynomialParameterPoint t))) =
      (fun t => Point.evaluate (f.left ⁻¹ᵁ U) ((f.left.app U).hom a)
        (s2e_u1_polynomialParameterPoint t)) := by
    funext t
    exact Point.evaluate_map f U a (s2e_u1_polynomialParameterPoint t)
  rw [he]
  exact hA _

end HodgeLean.Foundations.Program
