import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeParameter
import HodgeLean.Foundations.Program.SchoenCycleNativeParameterEvaluation
import HodgeLean.Foundations.Program.SchoenCycleU1NativeAffineDifferentials

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
attribute [local instance] overSpecAlgebra
namespace HodgeLean.Foundations.Program

/-- The actual native stalk jet evaluates the native regular parameter with
unit infinitesimal coefficient. -/
theorem s2v_l1b_action_native_parameter_jet_snd
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) :
    (s2e_u1_nativeStalkJet Y p (s2e_native_curve_parameter Y p)).snd = 1 := by
  obtain ⟨U, hp, s, hs, he⟩ := s2e_native_curve_parameter_centered_chart Y p
  rw [← hs, s2e_u1_nativeStalkJet_germ, s2e_u1_nativeSectionJet_snd]
  change (fun z => Point.evaluate U s (s2e_u1_nativeCurve Y p z)) =ᶠ[𝓝 0]
    (fun z => z) at he
  rw [he.deriv_eq]
  exact (hasDerivAt_id (0 : ℂ)).deriv

/-- The residue component of the native stalk jet is the actual point's
stalk evaluation. -/
theorem s2v_l1b_action_native_jet_fst
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (r : Y.left.presheaf.stalk p.underlying) :
    (s2e_u1_nativeStalkJet Y p r).fst = p.stalkHom r := by
  obtain ⟨U, hp, s, rfl⟩ := Y.left.presheaf.exists_germ_eq r
  rw [s2e_u1_nativeStalkJet_germ]
  change (s2e_u1_analyticGermJet (s2e_u1_analyticGerm _
    ((s2e_u1_nativeCurve_regular_sections Y p U hp).2 s))).fst = _
  rw [s2e_u1_analyticGermJet_representative]
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.fst_inr, add_zero, s2e_u1_nativeCurve_zero]
  rw [Point.evaluate, dif_pos hp]

/-- Native analytic first jets preserve the complex scalars of the actual
scheme stalk. -/
theorem s2v_l1b_action_native_jet_scalars
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (c : ℂ) :
    s2e_u1_nativeStalkJet Y p (HodgeLean.Foundations.Curves.stalkC p.underlying c) =
      TrivSqZeroExt.inl c := by
  unfold HodgeLean.Foundations.Curves.stalkC
  rw [RingHom.comp_apply, s2e_u1_nativeStalkJet_germ]
  exact (s2e_u1_sectionJetAlong Y ⊤ (s2e_u1_nativeCurve Y p)
    (s2e_u1_nativeCurve_regular_sections Y p ⊤ trivial).1
    (s2e_u1_nativeCurve_regular_sections Y p ⊤ trivial).2).commutes c

end HodgeLean.Foundations.Program
