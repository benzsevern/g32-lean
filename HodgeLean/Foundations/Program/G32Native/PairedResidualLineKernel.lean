import HodgeLean.Foundations.Program.G32Native.PairedResidualExactPreparedCoefficients
import HodgeLean.Foundations.Program.G32Native.PairedResidualOffDivisorVariation
import HodgeLean.Foundations.Program.G32Native.PairedResidualPreparedDivisibility
import HodgeLean.Foundations.Program.SchoenCycleS1j2
import HodgeLean.Foundations.Program.SchoenCycleStationaryAnalyticCoordinates
import HodgeLean.Foundations.Program.SchoenCyclePairedOffDivisorVariation
import HodgeLean.Foundations.Program.SchoenCycleFiniteBlockPartition

/-! # Scalar kernel for paired projective parameter curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology Manifold
open HodgeLean.Adapters
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A full-system parameter line stationary on regular sections has scalar variation. -/
theorem residual_system_parameter_line_scalar_kernel
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r d : ℕ)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm (Module.finrank_fin_fun (n := 1) ℂ) q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    [FiniteDimensional ℂ W]
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ W = d + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
      Point.map ℓ = fun R => residualProjectiveSystemPoint
        (Module.finrank_fin_fun (n := 1) ℂ) y hy W hW hgenus γ id (ep.symm R))
    (b : Module.Basis (Fin (d + 1)) ℂ
      W)
    (a : Fin (d + 1) → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    (A : (Fin (d + 1) → ℂ) →
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))))
    (hA :
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := W) d hd
      ∀ᶠ t in 𝓝 0, ∃ ht : (∑ i, (a + t) i • b i) ≠ 0,
        A t = ep (Projectivization.mk ℂ (∑ i, (a + t) i • b i) ht))
    (δ : Fin (d + 1) → ℂ) (β : ℂ → ComplexPoint B)
    (hβ : ContinuousAt β 0)
    (hline : ∀ᶠ t in 𝓝 (0 : ℂ), β t = Point.map ℓ (A (t • δ)))
    (hregular : ∀ U : B.left.Opens, (β 0).underlying ∈ U →
      ∀ c : Γ(B.left, U), AnalyticAt ℂ (fun t => Point.evaluate U c (β t)) 0)
    (hstationary : ∀ U : B.left.Opens, (β 0).underlying ∈ U →
      ∀ c : Γ(B.left, U), deriv (fun t => Point.evaluate U c (β t)) 0 = 0) :
    ∃ α : ℂ, (∑ i, δ i • b i) = α • (∑ i, a i • b i) := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  letI : Surjective γ.left := s2e_step1_surjective_of_complexPoint_surjective _ _ γ hsurj
  letI : SmoothOfRelativeDimension (2 * k) B.hom :=
    s2e_retained_quotient_relative_dimension Z B (2 * k) γ hγ hquot
  obtain ⟨x, hx⟩ := hsurj (Point.map ℓ (A 0))
  obtain ⟨s, m, hm, ι, p, hp, hxp⟩ := s2e_finite_tuple_block_partition (2 * k)
    (fun i => Point.map (g3_proj Z (2 * k) i) x)
  obtain ⟨e, hex, he0, hea, _, he⟩ := s2e_mixed_coefficient_neighbourhood
    Z B (2 * k) γ hγ hquot x s m hm ι p hp hxp
  have hbase : β 0 = Point.map γ x := by
    have h := hline.self_of_nhds
    simp only [zero_smul] at h
    exact h.trans hx.symm
  have hD := residual_system_divisor_of_retained_lift Z B k r y hy W hW hgenus γ hγ hsurj hquot (∑ i, a i • b i) ha x (by
      obtain ⟨ha0, hAt0⟩ := hA.self_of_nhds
      simp only [add_zero] at hAt0
      dsimp only at hℓ
      rw [hx, hℓ, hAt0]
      dsimp only
      rw [Equiv.symm_apply_apply])
  apply residual_normalized_divisible_proportional
    (Module.finrank_fin_fun (n := 1) ℂ) (Set.range y) W (fun q => ⟨(hW q).1, (hW q).2.2⟩) _ _ ha
  intro q
  by_cases hq : ∃ l, p l = q
  · obtain ⟨l, rfl⟩ := hq
    obtain ⟨g, u, c, hg, heG, hu, hu0, hc, hprep, hcoeff⟩ :=
      residual_system_exact_prepared_coefficients Z B k r d y hy W hW hgenus hd γ hγ hsurj hquot ℓ hℓ b a ha A hA x hx s m hm ι p hp hxp e he l
    apply residual_system_prepared_local_divisibility
      (Module.finrank_fin_fun (n := 1) ℂ) y W (fun i => b i) a δ (p l) g u c
      (hg a) heG hu hu0 (fun j => (hc j).1) _ hprep
    intro j
    have hE : AnalyticAt ℂ (fun z : Fin (2 * k) → ℂ =>
        e ((localChart B (2 * k) (β 0)).symm
          (localChart B (2 * k) (β 0) (β 0) + z)) (ι ⟨l, j⟩)) 0 := by
      rw [hbase]
      exact ((ContinuousLinearMap.proj (ι ⟨l, j⟩) :
        (Fin (2 * k) → ℂ) →L[ℂ] ℂ).analyticAt _).comp hea
    have hstat := s2e_stationary_regular_curve_analytic_coordinate B (2 * k) β hβ
      hregular hstationary (fun v => e v (ι ⟨l, j⟩)) hE
    have htd : HasDerivAt (fun t : ℂ => t • δ) δ 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℂ)).smul_const δ
    have ht : Tendsto (fun t : ℂ => t • δ) (𝓝 0) (𝓝 0) := by
      simpa only [zero_smul] using htd.continuousAt.tendsto
    have hce : (fun t : ℂ => c j (t • δ)) =ᶠ[𝓝 0]
        (fun t => e (β t) (ι ⟨l, j⟩)) := by
      filter_upwards [ht.eventually hcoeff, hline] with t hct hlt
      rw [hlt]
      exact hct j
    have hcj : HasFDerivAt (c j) (fderiv ℂ (c j) 0) ((0 : ℂ) • δ) := by
      simpa only [zero_smul] using (hc j).1.differentiableAt.hasFDerivAt
    have hdj := hcj.comp_hasDerivAt 0 htd
    simp only [id_eq, zero_smul, one_smul, Function.comp_def] at hdj
    exact hdj.unique (hstat.congr_of_eventuallyEq hce)
  · have hzero : (b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ) (∑ i, a i • b i : W).val + s2e_markedPoleDivisor y) q = 0 := by
      rw [hD, Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero
      intro i _
      obtain ⟨⟨l, j⟩, rfl⟩ := ι.surjective i
      rw [hxp, Finsupp.single_eq_of_ne]
      exact fun h => hq ⟨l, h.symm⟩
    exact residual_system_variation_divisible_off_divisor
      (Module.finrank_fin_fun (n := 1) ℂ) y hy W hW
      (fun i => b i) q a ha δ hzero

#print axioms residual_system_parameter_line_scalar_kernel
end HodgeLean.Foundations.Program.G32Native
