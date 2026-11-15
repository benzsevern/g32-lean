import HodgeLean.Foundations.Program.SchoenTowerL1bActionJetComparison

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual native derivative is a nonzero scalar multiple of the linear
coefficient in any normalized scalar-preserving stalk expansion. -/
theorem s2v_l1b_action_native_jet_coefficient
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    [SmoothOfRelativeDimension 1 Y.hom] [IsProjective Y.hom]
    (p : ComplexPoint Y)
    (ι : Y.left.presheaf.stalk p.underlying →+* PowerSeries ℂ)
    (hX : ∃ u, ι u = PowerSeries.X)
    (hC : ∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p.underlying c) =
      PowerSeries.C c) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ r,
      (s2e_u1_nativeStalkJet Y p r).snd = PowerSeries.coeff 1 (ι r) * d := by
  let R := Y.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  letI : IsDiscreteValuationRing R := s2e_smooth_curve_point_stalk_dvr Y p
  let φ : R →ₐ[ℂ] PowerSeries ℂ := { toRingHom := ι, commutes' := hC }
  let ψ : R →ₐ[ℂ] DualNumber ℂ :=
    { toRingHom := s2e_u1_nativeStalkJet Y p
      commutes' := s2v_l1b_action_native_jet_scalars Y p }
  obtain ⟨u, hu⟩ := hX
  obtain ⟨hl, hk⟩ := s2v_l1b_rotation_expansion_residue_kernel φ u hu
  have hnu : ¬ IsUnit u := by
    intro h
    have hm : IsUnit (ι u) := h.map ι
    rw [hu] at hm
    exact PowerSeries.X_irreducible.not_isUnit hm
  have hzero : (ψ u).fst = 0 := by
    change (s2e_u1_nativeStalkJet Y p u).fst = 0
    rw [s2v_l1b_action_native_jet_fst]
    by_contra hn
    exact hnu (isUnit_of_map_unit p.stalkHom.hom u (isUnit_iff_ne_zero.mpr hn))
  have he (r : R) := s2v_l1b_action_jet_linear_coefficient φ ψ u hu hk hzero r
  refine ⟨(ψ u).snd, ?_, he⟩
  intro hz
  have ht := he (s2e_native_curve_parameter Y p)
  change (s2e_u1_nativeStalkJet Y p (s2e_native_curve_parameter Y p)).snd = _ at ht
  rw [s2v_l1b_action_native_parameter_jet_snd, hz, mul_zero] at ht
  exact one_ne_zero ht

/-- The supplied formal rescaling is the native analytic first-order
coefficient of the pulled-back native regular parameter. -/
theorem s2v_l1b_action_scalar_native_jet
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    [SmoothOfRelativeDimension 1 Y.hom] [IsProjective Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hp : f.left p.underlying = p.underlying)
    (ι : Y.left.presheaf.stalk p.underlying →+* PowerSeries ℂ)
    (hX : ∃ u, ι u = PowerSeries.X)
    (hC : ∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p.underlying c) =
      PowerSeries.C c)
    (ζ : ℂ)
    (hact : ∀ r, ι (s2e_fixed_point_stalkPullback Y.left f.left p.underlying hp r) =
      PowerSeries.rescale ζ (ι r)) :
    ζ = (s2e_u1_nativeStalkJet Y p (s2e_fixed_point_stalkPullback Y.left f.left
      p.underlying hp (s2e_native_curve_parameter Y p))).snd := by
  obtain ⟨d, hd, he⟩ := s2v_l1b_action_native_jet_coefficient Y p ι hX hC
  have ht : PowerSeries.coeff 1 (ι (s2e_native_curve_parameter Y p)) * d = 1 :=
    (he _).symm.trans (s2v_l1b_action_native_parameter_jet_snd Y p)
  rw [he, hact, PowerSeries.coeff_rescale, pow_one, mul_assoc, ht, mul_one]

end HodgeLean.Foundations.Program
