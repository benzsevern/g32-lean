import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeChartSign
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeConjugacyLift

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The actual centered native homeomorphism has a logarithmic lift whose
deck coefficient is the supplied integral local sign. -/
theorem s2v_l1b_action_nativeConjugacy_signed_lift
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [SmoothOfRelativeDimension 1 Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    (E : M ≃ₜ ComplexPoint Y) (x : M) (ε : ℤ)
    (horient : relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨E, E.continuous⟩) E.injective x)
      (b6m_surfaceLocalClass ℤ x) = ε • s2v_l1b_action_curveLocalClass Y hdimY (E x)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆
      (s2v_l1b_action_nativeConjugacy Y E x).source ∧
      ∃ L : ℂ → ℂ, ContinuousOn L {z : ℂ | z.re < Real.log r} ∧
        (∀ z, z.re < Real.log r → Complex.exp (L z) =
          s2v_l1b_action_nativeConjugacy Y E x (Complex.exp z)) ∧
        (∀ z, z.re < Real.log r →
          L (z + 2 * Real.pi * Complex.I) = L z + (ε : ℂ) * (2 * Real.pi * Complex.I)) := by
  obtain ⟨r, hr, hb, L, k, hL, he, hk⟩ := s2v_l1b_action_nativeConjugacy_log_lift Y E x
  have h0 : 0 ∈ (s2v_l1b_action_nativeConjugacy Y E x).source :=
    s2v_l1b_action_centeredConjugacy_source _ _ E x (mem_chart_source ℂ x)
      (s2v_l1b_action_nativePlaneChart_source Y (E x))
  have hz : s2v_l1b_action_nativeConjugacy Y E x 0 = 0 :=
    s2v_l1b_action_centeredConjugacy_zero _ _ E x (mem_chart_source ℂ x)
  have hc := (s2v_l1b_action_nativeConjugacy Y E x).continuousOn.mono hb
  have hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → s2v_l1b_action_nativeConjugacy Y E x z ≠ 0 := by
    intro z hzb hzne hezero
    apply hzne
    exact (s2v_l1b_action_nativeConjugacy Y E x).injOn (hb hzb) h0 (hezero.trans hz.symm)
  have hsign := s2v_l1b_action_nativeConjugacy_deck_sign Y hdimY E x ε horient
    r hr hb hc hn L hL he k hk
  subst k
  exact ⟨r, hr, hb, L, hL, he, hk⟩

end HodgeLean.Foundations.Program
