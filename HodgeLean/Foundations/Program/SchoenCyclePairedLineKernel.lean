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
namespace HodgeLean.Foundations.Program

/-- A paired parameter line stationary on regular sections has scalar variation.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, tangent spaces to Abel fibres;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_paired_parameter_line_scalar_kernel
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) :=
        AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
      Point.map ℓ = fun R => s2e_projectiveDifferentialQuotientPoint
        (Module.finrank_fin_fun (n := 1) ℂ) w
        (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
        (ep.symm R))
    (b : Module.Basis (Fin (k + 1)) ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)))
    (a : Fin (k + 1) → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    (A : (Fin (k + 1) → ℂ) →
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
    (hA :
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
      ∀ᶠ t in 𝓝 0, ∃ ht : (∑ i, (a + t) i • b i) ≠ 0,
        A t = ep (Projectivization.mk ℂ (∑ i, (a + t) i • b i) ht))
    (δ : Fin (k + 1) → ℂ) (β : ℂ → ComplexPoint B)
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
  have hD := s2e_paired_divisor_of_retained_lift Z B k r w
    (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus
    γ hsurj hγ hquot (∑ i, a i • b i) ha x (by
      obtain ⟨ha0, hAt0⟩ := hA.self_of_nhds
      simp only [add_zero] at hAt0
      dsimp only at hℓ
      rw [hx, hℓ, hAt0]
      dsimp only
      rw [Equiv.symm_apply_apply])
  apply s2e_divisible_paired_parameters_proportional
    (Module.finrank_fin_fun (n := 1) ℂ) w
    (fun j => y ⟨2 * j.val + 1, by omega⟩) hres _ _ ha
  intro q
  by_cases hq : ∃ l, p l = q
  · obtain ⟨l, rfl⟩ := hq
    obtain ⟨g, u, c, hg, heG, hu, hu0, hc, hprep, hcoeff⟩ :=
      s2e_exact_paired_prepared_coefficients Z B k r hr y hy w hres horder hout hgenus
        hd γ hγ hsurj hquot ℓ hℓ b a ha A hA x hx s m hm ι p hp hxp e he l
    apply s2e_paired_prepared_local_divisibility
      (Module.finrank_fin_fun (n := 1) ℂ) w y (fun i => b i) a δ (p l) g u c
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
  · have hzero : s2e_adjustedDifferentialDivisor
        (Module.finrank_fin_fun (n := 1) ℂ) w y (∑ i, a i • b i) q = 0 := by
      rw [hD, Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero
      intro i _
      obtain ⟨⟨l, j⟩, rfl⟩ := ι.surjective i
      rw [hxp, Finsupp.single_eq_of_ne]
      exact fun h => hq ⟨l, h.symm⟩
    exact s2e_paired_variation_divisible_off_divisor
      (Module.finrank_fin_fun (n := 1) ℂ) w
      (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout
      (fun i => b i) q a ha δ hzero

end HodgeLean.Foundations.Program
