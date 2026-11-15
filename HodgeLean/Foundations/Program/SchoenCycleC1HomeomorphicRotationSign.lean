import HodgeLean.Foundations.Program.SchoenTowerL1bActionConjugateLiftScalar
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeSignedLift
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeGerm
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeIntertwining
import HodgeLean.Foundations.Program.SchoenTowerL1bActionConjugatePeriod
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeIdentity
import HodgeLean.Foundations.Program.SchoenTowerL1bActionLocalSign
import HodgeLean.Foundations.Program.SchoenTowerL1bActionRotationDerivative
import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourcePrimitive

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- A topological conjugacy of a finite rotation action with a native curve
action identifies the native derivative using its integral local sign.
Source: Schoen (1988), Lemma 2.5, printed p. 15; Miranda, Algebraic Curves and
Riemann Surfaces, III.3, Proposition 3.1. -/
theorem s2e_c1_homeomorphic_local_rotation_sign
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [SmoothOfRelativeDimension 1 Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (M G : Type) [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] [Group G] [Finite G] [MulAction G M]
    (eY : M ≃ₜ ComplexPoint Y) (f : Y ⟶ Y) (g : G)
    (hequiv : ∀ y, Point.map f (eY y) = eY (g • y))
    (x : M) (hrot : b4_IsRotGen ℂ x g)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (horient : relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨eY, eY.continuous⟩) eY.injective x)
      (b6m_surfaceLocalClass ℤ x) =
        ε • s2v_l1b_action_curveLocalClass Y hdimY (eY x)) :
    deriv (fun z => ComplexPoint.localChart Y 1 (eY x)
      (Point.map f (s2e_u1_nativeCurve Y (eY x) z)) 0 -
        ComplexPoint.localChart Y 1 (eY x) (eY x) 0) 0 =
      Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (orderOf g : ℂ)) := by
  classical
  by_cases hg : g = 1
  · have hf (q : ComplexPoint Y) : Point.map f q = q := by
      obtain ⟨y, rfl⟩ := eY.surjective q
      simpa only [hg, one_smul] using hequiv y
    simp_rw [hf]
    rw [s2v_l1b_action_centered_native_identity_derivative, hg, orderOf_one,
      Nat.cast_one, div_one, Complex.exp_int_mul_two_pi_mul_I]
  · have hd := s2v_l1b_action_rotgen_mdifferentiableAt x g hrot
    have hprimitive := s2v_l1b_action_rotgen_primitive_lift x g hrot
    let p := eY x
    let FS := s2v_l1b_action_sourceCoordinate x g
    let FT := s2v_l1b_action_nativeCoordinate Y p f
    let a := 2 * Real.pi * Complex.I / (orderOf g : ℂ)
    have hfixed : Point.map f p = p := by
      change Point.map f (eY x) = eY x
      rw [hequiv x, hrot.1]
    have hperiod := s2v_l1b_action_conjugate_period Y eY f g hequiv
      (orderOf g) (pow_orderOf_eq_one g)
    have hnonzero : deriv FT 0 ≠ 0 :=
      s2v_l1b_action_nativeCoordinate_derivative_ne_zero Y p f hfixed
        (orderOf g) (orderOf_pos g) hperiod
    let b := Complex.log (deriv FT 0)
    have hbexp : Complex.exp b = deriv FT 0 := Complex.exp_log hnonzero
    have hnative : HasDerivAt FT (Complex.exp b) 0 := by
      rw [hbexp]
      exact (s2v_l1b_action_nativeCoordinate_analytic Y p f hfixed).differentiableAt.hasDerivAt
    have hsc : ∀ᶠ z : ℂ in nhds 0, ContinuousAt FS z :=
      s2v_l1b_action_sourceCoordinate_eventually_continuousAt Y eY f g hequiv x hrot.1
    have hgc : ∀ᶠ z : ℂ in nhds 0, ContinuousAt FT z :=
      (s2v_l1b_action_nativeCoordinate_analytic Y p f hfixed).eventually_continuousAt
    obtain ⟨r, hr, hball, L, hL, heL, hdeck⟩ :=
      s2v_l1b_action_nativeConjugacy_signed_lift Y hdimY eY x ε horient
    let H := s2v_l1b_action_nativeConjugacy Y eY x
    have hH0 : H 0 = 0 :=
      s2v_l1b_action_centeredConjugacy_zero _ _ eY x (mem_chart_source ℂ x)
    have hHsource : 0 ∈ H.source :=
      s2v_l1b_action_centeredConjugacy_source _ _ eY x (mem_chart_source ℂ x)
        (s2v_l1b_action_nativePlaneChart_source Y (eY x))
    have hconj : ∀ᶠ z : ℂ in nhds 0, H (FS z) = FT (H z) :=
      s2v_l1b_action_nativeConjugacy_intertwines_coordinate Y eY f g hequiv x hrot
    have hs := s2v_l1b_action_conjugate_lift_scalar FS FT H L a b
      (s2v_l1b_action_sourceCoordinate_zero x g hrot.1)
      (s2v_l1b_action_nativeCoordinate_zero Y p f hfixed) hH0
      (s2v_l1b_action_sourceCoordinate_derivative x g hrot) hnative hsc hgc
      (H.continuousAt hHsource) hconj (Real.log r) hL heL ε hdeck
      (orderOf g) (orderOf_pos g) hprimitive
    change deriv FT 0 = _
    rw [← hbexp]
    exact hs

end HodgeLean.Foundations.Program
