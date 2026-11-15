import HodgeLean.Foundations.Program.SchoenTowerL1bActionStalkEvaluation

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The pulled-back native parameter jet is the derivative of the actual
curve action written in centered native coordinates. -/
theorem s2v_l1b_action_native_jet_coordinate_derivative
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hp : f.left p.underlying = p.underlying)
    (hfixed : Point.map f p = p) :
    (s2e_u1_nativeStalkJet Y p (s2e_fixed_point_stalkPullback Y.left f.left
      p.underlying hp (s2e_native_curve_parameter Y p))).snd =
      deriv (fun z => ComplexPoint.localChart Y 1 p
        (Point.map f (s2e_u1_nativeCurve Y p z)) 0 -
          ComplexPoint.localChart Y 1 p p 0) 0 := by
  obtain ⟨U, hU, s, hs, he⟩ := s2e_native_curve_parameter_regular_chart Y p
  rw [← hs, s2v_l1b_action_pullback_jet_derivative]
  apply Filter.EventuallyEq.deriv_eq
  have hc := ContinuousAt.comp (f := s2e_u1_nativeCurve Y p) (x := (0 : ℂ))
    (Point.continuous_map f).continuousAt (s2v_l1b_action_native_curve_continuousAt Y p)
  have ht : Tendsto (fun z => Point.map f (s2e_u1_nativeCurve Y p z)) (𝓝 0) (𝓝 p) := by
    convert hc.tendsto using 1 <;>
      (try simp only [Function.comp_apply, s2e_u1_nativeCurve_zero, hfixed]) <;> rfl
  have hn := ht ((ComplexPoint.localChart Y 1 p).open_source.mem_nhds
    (ComplexPoint.mem_localChart_source Y 1 p))
  filter_upwards [hn] with z hz
  exact he _ hz

/-- Any supplied normalized intertwining expansion has rescaling scalar
equal to the derivative of the actual action in native curve coordinates. -/
theorem s2v_l1b_action_scalar_coordinate_derivative
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    [SmoothOfRelativeDimension 1 Y.hom] [IsProjective Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hp : f.left p.underlying = p.underlying)
    (hfixed : Point.map f p = p)
    (ι : Y.left.presheaf.stalk p.underlying →+* PowerSeries ℂ)
    (hX : ∃ u, ι u = PowerSeries.X)
    (hC : ∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p.underlying c) =
      PowerSeries.C c)
    (ζ : ℂ)
    (hact : ∀ r, ι (s2e_fixed_point_stalkPullback Y.left f.left p.underlying hp r) =
      PowerSeries.rescale ζ (ι r)) :
    ζ = deriv (fun z => ComplexPoint.localChart Y 1 p
      (Point.map f (s2e_u1_nativeCurve Y p z)) 0 -
        ComplexPoint.localChart Y 1 p p 0) 0 :=
  (s2v_l1b_action_scalar_native_jet Y p f hp ι hX hC ζ hact).trans
    (s2v_l1b_action_native_jet_coordinate_derivative Y p f hp hfixed)

/-- The centered native coordinate curve has identity derivative in the
centered native chart. -/
theorem s2v_l1b_action_native_identity_coordinate_derivative
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) :
    deriv (fun z => ComplexPoint.localChart Y 1 p (s2e_u1_nativeCurve Y p z) 0 -
      ComplexPoint.localChart Y 1 p p 0) 0 = 1 := by
  have he := s2e_centered_chart_evaluation (ComplexPoint.localChart Y 1 p) p
    (ComplexPoint.mem_localChart_source Y 1 p)
    (fun q => ComplexPoint.localChart Y 1 p q 0 - ComplexPoint.localChart Y 1 p p 0)
    (fun _ _ => rfl)
  change (fun z => ComplexPoint.localChart Y 1 p (s2e_u1_nativeCurve Y p z) 0 -
    ComplexPoint.localChart Y 1 p p 0) =ᶠ[𝓝 0] (fun z => z) at he
  rw [he.deriv_eq]
  exact (hasDerivAt_id (0 : ℂ)).deriv

end HodgeLean.Foundations.Program
