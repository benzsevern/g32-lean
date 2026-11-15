import HodgeLean.Foundations.Program.SchoenCycleAffineCoefficientChartDescent
import HodgeLean.Foundations.Program.SchoenCycleComplexOpenRestrictionMap
import HodgeLean.Foundations.Program.SchoenCycleOpenPointEventually

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Exact coefficient sections descend near a marked point of an etale comparison, using their actual affine open and the original ambient comparison space.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_etale_open_coefficient_chart_descent
    (S B T : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (V : S.left.Opens) (hV : IsAffineOpen V) :
    letI := s2e_step1_sectionAlgebra S V
    ∀ (G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(S.left, V)) (hG : G.toRingHom.Etale)
      (a : T ⟶ S) (f : T ⟶ B), Etale a.left → Etale f.left →
      ∀ (x : ComplexPoint T), Point.map a x ∈ Point.overOpen V →
      (∀ i, Point.evaluate V (G (MvPolynomial.X i)) (Point.map a x) = 0) →
      ∃ e : OpenPartialHomeomorph (ComplexPoint B) (Fin n → ℂ),
        Point.map f x ∈ e.source ∧ e (Point.map f x) = 0 ∧
        AnalyticAt ℂ (fun z => e ((ComplexPoint.localChart B n (Point.map f x)).symm
          (ComplexPoint.localChart B n (Point.map f x) (Point.map f x) + z))) 0 ∧
        AnalyticAt ℂ (fun z => ComplexPoint.localChart B n (Point.map f x) (e.symm z)) 0 ∧
        (∀ᶠ q in 𝓝 x, ∀ i, e (Point.map f q) i =
          Point.evaluate V (G (MvPolynomial.X i)) (Point.map a q)) := by
  letI := s2e_step1_sectionAlgebra S V
  intro G hG a f ha hf x hx hz
  let W := a.left ⁻¹ᵁ V
  let X := ComplexPoint.openScheme T W
  let j := ComplexPoint.openInclusion T W
  obtain ⟨r, hr, hfac⟩ := s2e_complex_open_restriction_map T S a V W le_rfl
  letI : Etale a.left := ha
  letI : Etale f.left := hf
  haveI : Etale j.left := by change Etale W.ι; infer_instance
  haveI : Etale r.left := by rw [hr]; infer_instance
  let f' := j ≫ f
  haveI : Etale f'.left := by change Etale (j.left ≫ f.left); infer_instance
  let x' := (ComplexPoint.openHomeomorph T W).symm ⟨x, hx⟩
  have hx' : Point.map j x' = x :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph T W).apply_symm_apply ⟨x, hx⟩)
  have hfpoint : Point.map f' x' = Point.map f x := by
    change (x' ≫ j) ≫ f = x ≫ f
    rw [show x' ≫ j = x from hx']
  have hapoint (q : ComplexPoint X) :
      Point.map (r ≫ ComplexPoint.openInclusion S V) q = Point.map a (Point.map j q) := by
    rw [hfac]
    exact (Category.assoc q j a).symm
  have hz' (i : Fin n) : Point.evaluate V (G (MvPolynomial.X i))
      (Point.map (r ≫ ComplexPoint.openInclusion S V) x') = 0 := by
    rw [hapoint, hx']
    exact hz i
  obtain ⟨e, he, hez, hef, hei, hev⟩ :=
    s2e_affine_coefficient_chart_etale_descent S B X n V hV G hG r f'
      inferInstance inferInstance x' hz'
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hfpoint] at he
  · rwa [hfpoint] at hez
  · rwa [hfpoint] at hef
  · rwa [hfpoint] at hei
  · have hev' : ∀ᶠ q in 𝓝 x', ∀ i, e (Point.map f (Point.map j q)) i =
        Point.evaluate V (G (MvPolynomial.X i)) (Point.map a (Point.map j q)) := by
      filter_upwards [hev] with q hq
      intro i
      rw [← hapoint q]
      exact hq i
    have hh := s2e_open_point_eventually T W x'
      (fun q => ∀ i, e (Point.map f q) i = Point.evaluate V (G (MvPolynomial.X i)) (Point.map a q)) hev'
    rwa [hx'] at hh

#print axioms s2e_etale_open_coefficient_chart_descent
end HodgeLean.Foundations.Program
