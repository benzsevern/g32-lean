import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartDeckSign
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeConjugacy
import HodgeLean.Foundations.Program.SchoenTowerL1bActionLocalSign

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Scalar conversion cancels the one-coordinate expansion of the
preferred surface chart as an actual partial homeomorphism. -/
theorem s2v_l1b_action_surfaceChart_scalar
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] (x : M) :
    s2v_l1b_action_vectorChart_scalar (b6m_surfaceChart x) = chartAt ℂ x := by
  apply OpenPartialHomeomorph.ext
  · intro y
    rfl
  · intro z
    rfl
  · simp only [s2v_l1b_action_vectorChart_scalar, b6m_surfaceChart,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.preimage_univ, Set.inter_univ]

/-- The vector-chart representative specializes to the actual native
coordinate representative, including its genuine source and target. -/
theorem s2v_l1b_action_vectorConjugacy_native
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    (E : M ≃ₜ ComplexPoint Y) (x : M) :
    s2v_l1b_action_vectorConjugacy (b6m_surfaceChart x)
      (ComplexPoint.localChart Y 1 (E x)) E x = s2v_l1b_action_nativeConjugacy Y E x := by
  unfold s2v_l1b_action_vectorConjugacy s2v_l1b_action_nativeConjugacy
  rw [s2v_l1b_action_surfaceChart_scalar]
  rfl

/-- Dimension transport identifies the specified native curve class with
its one-dimensional native chart class. -/
theorem s2v_l1b_action_curve_class_native_chart
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [SmoothOfRelativeDimension 1 Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1) (p : ComplexPoint Y) :
    s2v_l1b_action_curveLocalClass Y hdimY p =
      b6m_localClassOfChart ℤ 1 (ComplexPoint.localChart Y 1 p) p
        (ComplexPoint.mem_localChart_source Y 1 p) := by
  have h (d : ℕ) [SmoothOfRelativeDimension d Y.hom] (hd : d = 1) :
      (show RelativeHomology ℤ (pointComplementPair p) 2 from by
        simpa only [hd, mul_one] using b6m_manifoldLocalClass ℤ d p) =
      b6m_localClassOfChart ℤ 1 (ComplexPoint.localChart Y 1 p) p
        (ComplexPoint.mem_localChart_source Y 1 p) := by
    subst d
    rfl
  exact h (TopologicalSpace.dim Y.left) hdimY

/-- The supplied integral orientation equation identifies the actual
native coordinate lift's deck coefficient, through disk excision. -/
theorem s2v_l1b_action_nativeConjugacy_deck_sign
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [SmoothOfRelativeDimension 1 Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    (E : M ≃ₜ ComplexPoint Y) (x : M) (ε : ℤ)
    (horient : relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨E, E.continuous⟩) E.injective x)
      (b6m_surfaceLocalClass ℤ x) = ε • s2v_l1b_action_curveLocalClass Y hdimY (E x))
    (r : ℝ) (hr : 0 < r)
    (hb : Metric.ball (0 : ℂ) r ⊆ (s2v_l1b_action_nativeConjugacy Y E x).source)
    (hc : ContinuousOn (s2v_l1b_action_nativeConjugacy Y E x) (Metric.ball 0 r))
    (hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → s2v_l1b_action_nativeConjugacy Y E x z ≠ 0)
    (L : ℂ → ℂ) (hL : ContinuousOn L {z : ℂ | z.re < Real.log r})
    (he : ∀ z, z.re < Real.log r → Complex.exp (L z) =
      s2v_l1b_action_nativeConjugacy Y E x (Complex.exp z))
    (k : ℤ) (hk : ∀ z, z.re < Real.log r →
      L (z + 2 * Real.pi * Complex.I) = L z + (k : ℂ) * (2 * Real.pi * Complex.I)) :
    k = ε := by
  have ho : relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨E, E.continuous⟩) E.injective x)
      (b6m_localClassOfChart ℤ 1 (b6m_surfaceChart x) x
        (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ x)) =
      ε • b6m_localClassOfChart ℤ 1 (ComplexPoint.localChart Y 1 (E x)) (E x)
        (ComplexPoint.mem_localChart_source Y 1 (E x)) :=
    horient.trans (congrArg (fun c => ε • c) (s2v_l1b_action_curve_class_native_chart Y hdimY (E x)))
  have hid := s2v_l1b_action_vectorConjugacy_native Y E x
  rw [← hid] at hb hc hn he
  exact s2v_l1b_action_chart_deck_sign (b6m_surfaceChart x)
    (ComplexPoint.localChart Y 1 (E x)) E x _ _ ε ho r hr hb hc hn L hL he k hk

end HodgeLean.Foundations.Program
