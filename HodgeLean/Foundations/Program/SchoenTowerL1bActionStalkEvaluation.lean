import HodgeLean.Foundations.Program.SchoenTowerL1bActionAnalyticCharacter

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The transported fixed-point pullback of a germ is the germ of the
pulled-back section on its actual inverse-image neighbourhood. -/
theorem s2v_l1b_action_stalk_pullback_germ
    (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (U : X.Opens) (hU : p ∈ U) (s : Γ(X, U)) :
    s2e_fixed_point_stalkPullback X f p hp (X.presheaf.germ U p hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) p (by change f p ∈ U; rwa [hp]) (f.app U s) := by
  have he : (X.presheaf.stalkCongr (.of_eq hp)).inv =
      (X.presheaf.stalkCongr (.of_eq hp.symm)).hom := by
    simp only [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkCongr_hom]
  have ht := s2e_germ_stalk_transport X U p (f p) hU (by change f p ∈ U; rwa [hp]) hp.symm
  have h := congrArg (fun k : Γ(X, U) ⟶ X.presheaf.stalk p => k.hom s)
    ((congrArg (fun k => k ≫ f.stalkMap p) ht).trans (f.germ_stalkMap U p (by change f p ∈ U; rwa [hp])))
  simpa only [s2e_fixed_point_stalkPullback, Scheme.FixedPointStalk.pullback, he,
    CommRingCat.comp_apply] using h

/-- The native derivative of the actual stalk pullback is differentiation
of section evaluation along the mapped native coordinate curve. -/
theorem s2v_l1b_action_pullback_jet_derivative
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hp : f.left p.underlying = p.underlying)
    (U : Y.left.Opens) (hU : p.underlying ∈ U) (s : Γ(Y.left, U)) :
    (s2e_u1_nativeStalkJet Y p
      (s2e_fixed_point_stalkPullback Y.left f.left p.underlying hp
        (Y.left.presheaf.germ U p.underlying hU s))).snd =
      deriv (fun z => Point.evaluate U s (Point.map f (s2e_u1_nativeCurve Y p z))) 0 := by
  rw [s2v_l1b_action_stalk_pullback_germ, s2e_u1_nativeStalkJet_germ,
    s2e_u1_nativeSectionJet_snd]
  apply Filter.EventuallyEq.deriv_eq
  exact Filter.Eventually.of_forall (fun z =>
    (Point.evaluate_map f U s (s2e_u1_nativeCurve Y p z)).symm)

/-- The centered native inverse-chart curve is continuous at its base point. -/
theorem s2v_l1b_action_native_curve_continuousAt
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) : ContinuousAt (s2e_u1_nativeCurve Y p) 0 := by
  let e := ComplexPoint.localChart Y 1 p
  have hc : Continuous (fun z : ℂ => e p + fun _ : Fin 1 => z) :=
    continuous_const.add (continuous_pi fun _ => continuous_id)
  have hzero : e p + (fun _ : Fin 1 => (0 : ℂ)) = e p := by
    funext i
    exact add_zero _
  have he : ContinuousAt e.symm (e p) :=
    e.continuousAt_symm (e.map_source (ComplexPoint.mem_localChart_source Y 1 p))
  have he' : ContinuousAt e.symm (e p + fun _ : Fin 1 => (0 : ℂ)) := by
    rw [hzero]
    exact he
  exact ContinuousAt.comp (f := fun z : ℂ => e p + fun _ : Fin 1 => z)
    (x := (0 : ℂ)) he' hc.continuousAt

end HodgeLean.Foundations.Program
