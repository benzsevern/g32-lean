import HodgeLean.Foundations.Program.SchoenTowerL1bActionCurveCharacter
import HodgeLean.Foundations.Program.SchoenCycleNativeCurveParameter

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every normalized expansion detects the native chart's regular parameter
in degree one. -/
theorem s2v_l1b_action_native_parameter_linear_ne_zero
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    [SmoothOfRelativeDimension 1 Y.hom] [IsProjective Y.hom]
    (p : ComplexPoint Y)
    (ι : Y.left.presheaf.stalk p.underlying →+* PowerSeries ℂ)
    (hX : ∃ u, ι u = PowerSeries.X)
    (hC : ∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p.underlying c) =
      PowerSeries.C c) :
    PowerSeries.coeff 1 (ι (s2e_native_curve_parameter Y p)) ≠ 0 := by
  let R := Y.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  letI : IsDiscreteValuationRing R := s2e_smooth_curve_point_stalk_dvr Y p
  let φ : R →ₐ[ℂ] PowerSeries ℂ := { toRingHom := ι, commutes' := hC }
  obtain ⟨u, hu⟩ := hX
  obtain ⟨hl, hk⟩ := s2v_l1b_rotation_expansion_residue_kernel φ u hu
  haveI := hl
  haveI : IsLocalHom φ.toRingHom := isLocalHom_of_comp φ.toRingHom PowerSeries.constantCoeff
  have hirr : Irreducible u := Irreducible.of_map (f := φ.toRingHom)
    (by change Irreducible (ι u); rw [hu]; exact PowerSeries.X_irreducible)
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {u} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer u).mp hirr
  let t := s2e_native_curve_parameter Y p
  have hnative : IsLocalRing.maximalIdeal R = Ideal.span {t} :=
    s2e_native_curve_parameter_maximalIdeal Y p
  have htmem : t ∈ Ideal.span ({u} : Set R) := by
    rw [← hmax, hnative]
    exact Ideal.subset_span (Set.mem_singleton t)
  have humem : u ∈ Ideal.span ({t} : Set R) := by
    rw [← hnative, hmax]
    exact Ideal.subset_span (Set.mem_singleton u)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp htmem
  have hz : PowerSeries.constantCoeff (ι t) = 0 := by
    rw [hw, map_mul, hu, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp humem
  have he := congrArg (fun r => PowerSeries.coeff 1 (ι r)) hv
  rw [hu, PowerSeries.coeff_one_X, map_mul, PowerSeries.coeff_one_mul,
    hz, mul_zero, add_zero] at he
  intro hn
  rw [hn, zero_mul] at he
  exact one_ne_zero he

/-- The supplied rescaling scalar is the ratio of linear coefficients for
the native regular parameter and its actual fixed-point pullback. -/
theorem s2v_l1b_action_native_parameter_character
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
    ζ = PowerSeries.coeff 1 (ι (s2e_fixed_point_stalkPullback Y.left f.left
        p.underlying hp (s2e_native_curve_parameter Y p))) /
      PowerSeries.coeff 1 (ι (s2e_native_curve_parameter Y p)) := by
  apply (eq_div_iff (s2v_l1b_action_native_parameter_linear_ne_zero Y p ι hX hC)).mpr
  rw [hact, PowerSeries.coeff_rescale, pow_one]

end HodgeLean.Foundations.Program
