import HodgeLean.Foundations.Program.SchoenCycleU1CanonicalLocalDivisibility
import HodgeLean.Foundations.Program.SchoenCycleU1CanonicalLineTuples
import HodgeLean.Foundations.Program.SchoenCycleU1StationaryCurveJets
import HodgeLean.Foundations.Program.SchoenCycleU1SupportDivisorChart
import HodgeLean.Foundations.Program.SchoenCycleU1Variation

/-! # Scalar variations from stationary actual canonical line curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Manifold Filter Topology
open HodgeLean.Adapters
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Program

/-- A canonical differential line whose actual quotient curve is analytic on
regular sections and stationary on all those sections has scalar variation.
All local divisor comparisons and support coordinates are constructed here.
Source: ACGH, Geometry of Algebraic Curves I, Chapters I and IV, the differential
of the Abel map; Forster, Lectures on Riemann Surfaces, section 13. -/
theorem s2e_u1_canonical_line_kernel
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (θ δ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) (hθ : θ ≠ 0)
    (b : ℂ → ComplexPoint B)
    (hline : ∀ᶠ t in 𝓝 (0 : ℂ), ∃ h : θ + t • δ ≠ 0,
      b t = s2e_canonicalQuotientPoint Z B N γ hg
        (Projectivization.mk ℂ (θ + t • δ) h))
    (hregular : ∀ V : B.left.Opens, (b 0).underlying ∈ V →
      (∀ᶠ t in 𝓝 (0 : ℂ), (b t).underlying ∈ V) ∧
        ∀ a : Γ(B.left, V), AnalyticAt ℂ (fun t => Point.evaluate V a (b t)) 0)
    (hstationary : ∀ V : B.left.Opens, (b 0).underlying ∈ V →
      ∀ a : Γ(B.left, V), deriv (fun t => Point.evaluate V a (b t)) 0 = 0) :
    (∃ a : ℂ, δ = a • θ) ∧
      Submodule.Quotient.mk (p := Submodule.span ℂ {θ}) δ = 0 := by
  classical
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  have hfamily := s2e_u1_canonical_line_divisor_tuples Z B N γ hγ hg θ δ b hline
  obtain ⟨x0, _, hdiv0, hbtuple⟩ := hfamily.self_of_nhds
  simp only [zero_smul, add_zero] at hdiv0
  let S : Finset (ComplexPoint Z) := Finset.univ.image x0
  have hxS (i : Fin N) : x0 i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨U, hUa, hU⟩ := s2e_u1_exists_affine_open_containing_support Z
    (S.image Point.underlying)
  have hS : ∀ p ∈ S, p.underlying ∈ U := by
    intro p hp
    exact hU _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  obtain ⟨s, hsep, hs⟩ := s2e_u1_affine_support_regular_coordinate Z U hUa S hS
  have hpow : Point.underlying (s2_lift N x0) ∈ s2e_u1_powerOpen Z N U := by
    apply (s2e_u1_mem_powerOpen Z N U _).mpr
    intro i
    have he : Point.map (g3_proj Z N i) (s2_lift N x0) = x0 i := by
      simp only [Point.map, s2_check_lift_proj]
    simpa only [← Point.underlying_map, he] using hS _ (hxS i)
  obtain ⟨V, hVa, hVbase, hVU⟩ := s2e_u1_quotient_affine_chart_inside_invariant_open
    Z B N γ hsurj hγ hquot (s2e_u1_powerOpen Z N U)
    (s2e_u1_powerOpen_permute Z N U) (s2_lift N x0) hpow
  have hb0 : (b 0).underlying ∈ V := by rwa [hbtuple]
  obtain ⟨Q, hQ, _⟩ := s2e_u1_retained_divisor_coordinate_polynomial
    Z B N γ hsurj hγ hquot U V hVa hVU s
  obtain ⟨hb, hba⟩ := hregular V hb0
  have hjet := s2e_u1_curveJet_stationary_of_regular_derivatives B V hVa b hb hba hb0
    (hstationary V hb0)
  apply s2e_u1_locally_divisible_variation (Module.finrank_fin_fun (n := 1) ℂ) θ δ hθ
  intro p
  by_cases hp : p ∈ S
  · have hsep' (i : Fin N) : Point.evaluate U s (x0 i) = Point.evaluate U s p ↔ x0 i = p :=
      ⟨fun h => hsep (hxS i) hp h, fun h => congrArg (Point.evaluate U s) h⟩
    obtain ⟨g, hga, he⟩ := s2e_u1_canonical_local_divisibility_of_retained_jet
      Z B N γ U V hVa hVU s Q hQ θ δ hθ p (hS p hp) (hs p hp)
      b hb hba hb0 hjet x0 hdiv0 hbtuple hsep' hfamily
    exact ⟨g, hga, he.filter_mono nhdsWithin_le_nhds⟩
  · have hnp (i : Fin N) : x0 i ≠ p := by
      intro h
      exact hp (h ▸ hxS i)
    have hD0 : b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ) θ p = 0 := by
      rw [hdiv0]
      simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, hnp, ite_false, Finset.sum_const_zero]
    obtain ⟨d, hd, hD⟩ := s2e_holomorphic_divisor_analytic_order
      (Module.finrank_fin_fun (n := 1) ℂ) θ hθ p
    have hd0 : d = 0 := by exact_mod_cast hD.trans hD0
    have hθa := RiemannRochEichler_loc_analytic (Module.finrank_fin_fun (n := 1) ℂ) θ p
    have hδa := RiemannRochEichler_loc_analytic (Module.finrank_fin_fun (n := 1) ℂ) δ p
    have hθ0 : HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p 0 ≠ 0 :=
      hθa.analyticOrderAt_eq_zero.mp (by simpa only [hd0, Nat.cast_zero] using hd)
    refine ⟨fun z => HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) δ p z /
      HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p z, hδa.div hθa hθ0, ?_⟩
    have hn : ∀ᶠ z : ℂ in 𝓝[≠] 0,
        HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p z ≠ 0 :=
      (hθa.continuousAt.eventually_ne hθ0).filter_mono nhdsWithin_le_nhds
    filter_upwards [hn] with z hz
    exact (div_mul_cancel₀ _ hz).symm

end HodgeLean.Foundations.Program
