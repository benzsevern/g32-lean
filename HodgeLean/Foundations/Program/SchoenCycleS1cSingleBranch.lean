import HodgeLean.Foundations.Program.SchoenCycleS1j4
import HodgeLean.Foundations.Program.SchoenCycleS1j2
import HodgeLean.Foundations.Program.SchoenCycleS1cParameterLift
import HodgeLean.Foundations.Program.SchoenCyclePulledPrincipalComparison
import HodgeLean.Foundations.Program.SchoenCycleGivenPreparationResidues
import HodgeLean.Foundations.Program.SchoenCycleMorphismNativeCoordinates
import HodgeLean.Foundations.Program.SchoenCycleFiniteBlockPartition

/-! # Restriction of one marked branch ideal to the paired slice -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters Filter Topology Manifold
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program

theorem s2e_paired_single_branch_ideal
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
    (hpair : ∀ i j,
      b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
        (w i) (y ⟨2 * j.val, by omega⟩) = if i = j then -1 else 0)
    (n : ℕ) (hn : 2 * k = n + 1) (j : Fin r) (side : Bool) :
    let : ConnectedSpace (ComplexPoint Z) :=
      AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
    let γn : g3_power Z (n + 1) ⟶ B :=
      eqToHom (congrArg (g3_power Z) hn.symm) ≫ γ
    let H : PP.left.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Point.underlying ''
        {R : ComplexPoint PP | ∃ (v : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) ×
          (Fin r → ℂ)) (hv : v ≠ 0),
          ep.symm R = Projectivization.mk ℂ v hv ∧ v.2 j = 0}))
    (s2c_branchIdeal Z B n γn
      (if side then y ⟨2 * j.val + 1, by omega⟩ else y ⟨2 * j.val, by omega⟩)).comap ℓ.left = H := by
  classical
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)
  let b := Module.finBasisOfFinrankEq ℂ V hd
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd
  let γn : g3_power Z (n + 1) ⟶ B := eqToHom (congrArg (g3_power Z) hn.symm) ≫ γ
  let q : ComplexPoint Z := if side then y ⟨2 * j.val + 1, by omega⟩
    else y ⟨2 * j.val, by omega⟩
  let L : V →ₗ[ℂ] ℂ := (LinearMap.proj j).comp (LinearMap.snd ℂ _ _)
  let H : PP.left.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure (Point.underlying ''
      {R : ComplexPoint PP | ∃ (v : V) (hv : v ≠ 0),
        ep.symm R = Projectivization.mk ℂ v hv ∧ L v = 0}))
  change (s2c_branchIdeal Z B n γn q).comap ℓ.left = H
  letI : IsIntegral PP.left := IntersectionProductScaf_projective_integral k
  letI : Smooth PP.hom := IntersectionProductScaf_projective_smooth k
  let d := TopologicalSpace.dim PP.left
  letI : SmoothOfRelativeDimension d PP.hom := SmoothOfRelativeDimension.of_isIntegral PP.hom
  letI : Surjective γ.left := s2e_step1_surjective_of_complexPoint_surjective _ _ γ hsurj
  letI : SmoothOfRelativeDimension (2 * k) B.hom :=
    s2e_retained_quotient_relative_dimension Z B (2 * k) γ hγ hquot
  have hL : L ≠ 0 := by
    intro h
    have hh := congrArg (fun f : V →ₗ[ℂ] ℂ => f (0, Pi.single j 1)) h
    change (Pi.single j (1 : ℂ) : Fin r → ℂ) j = 0 at hh
    simp only [Pi.single_eq_same] at hh
    exact one_ne_zero hh
  apply s2e_ideal_sheaf_eq_on_complex_neighbourhoods PP _ H
  intro P
  let C := localChart PP d P
  let R := fun z : Fin d → ℂ => C.symm (C P + z)
  have hR0 : R 0 = P := by
    dsimp only [R]
    rw [add_zero, C.left_inv (mem_localChart_source PP d P)]
  obtain ⟨a, ha, hlift⟩ := s2e_projective_native_analytic_homogeneous_lift V k d hd P
  obtain ⟨ha0, A, hA, hRA⟩ := s2e_projective_lift_parameter_family V k d hd P R a hlift
  have hA0 : A 0 = P := by
    have hh := hRA.self_of_nhds
    rw [sub_self, hR0] at hh
    exact hh.symm
  let t := fun z : Fin d → ℂ => a z - a 0
  have ht : AnalyticAt ℂ t 0 := ha.sub analyticAt_const
  have ht0 : t 0 = 0 := sub_self _
  have htn : Tendsto t (𝓝 0) (𝓝 0) := ht0 ▸ ht.continuousAt.tendsto
  obtain ⟨U, hPU, cH, ηH, hH, hηH, hηH0, heH⟩ :=
    s2e_projective_linear_hyperplane_local_generator V k d hd L hL P a ha hlift
  change ∀ᶠ z in 𝓝 0, Point.evaluate U.1 cH (R z) =
    ηH z * L (∑ i, a z i • b i) at heH
  obtain ⟨x, hx⟩ := hsurj (Point.map ℓ (A 0))
  have hxP : Point.map γ x = Point.map ℓ P := by simpa only [hA0] using hx
  obtain ⟨s, m, hm, ι, p, hp, hxp⟩ := s2e_finite_tuple_block_partition (2 * k)
    (fun i => Point.map (g3_proj Z (2 * k) i) x)
  obtain ⟨e, hex, he0, hea, _, he⟩ := s2e_mixed_coefficient_neighbourhood
    Z B (2 * k) γ hγ hquot x s m hm ι p hp hxp
  have hD := s2e_paired_divisor_of_retained_lift Z B k r w
    (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus
    γ hsurj hγ hquot (∑ i, a 0 i • b i) ha0 x (by
      obtain ⟨ha', hh⟩ := hA.self_of_nhds
      simp only [add_zero] at hh
      dsimp only at hℓ
      rw [hx, hℓ, hh]
      dsimp only
      rw [Equiv.symm_apply_apply])
  by_cases hq : ∃ l, p l = q
  · obtain ⟨l, hl⟩ := hq
    obtain ⟨g, u, c, hg, heG, hu, hu0, hc, hprep, hcoeff⟩ :=
      s2e_exact_paired_prepared_coefficients Z B k r hr y hy w hres horder hout hgenus
        hd γ hγ hsurj hquot ℓ hℓ b (a 0) ha0 A hA x hx s m hm ι p hp hxp e he l
    have hqy : q ∈ Set.range y := by
      dsimp only [q]
      split_ifs <;> exact ⟨_, rfl⟩
    have heG' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ v,
        z * HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ)
          (s2e_pairedDifferentialLinear (Module.finrank_fin_fun (n := 1) ℂ) w
            (∑ i, v i • b i)) q z = g (v, z) := by
      simpa only [hl, if_pos hqy] using heG
    obtain ⟨ηc, hηc, hηc0, hec⟩ := s2e_given_preparation_signed_constant_term
      (Module.finrank_fin_fun (n := 1) ℂ) w y hres hpair (fun i => b i)
      (a 0) j side g u c hg heG' hu hu0 hprep
    obtain ⟨W, hxW, cB, ηB, hB, hηB, hηB0, heB⟩ :=
      s2e_mixed_branch_generator Z B (2 * k) γ hγ hquot x s m hm ι p hp hxp
        e he n hn l
    have hPW : (Point.map ℓ P).underlying ∈ W.1 := by
      rw [← hxP, Point.underlying_map]
      exact hxW
    have hB' : (s2c_branchIdeal Z B n γn q).ideal W = Ideal.span {cB} := by
      simpa only [hl] using hB
    let F := fun z : Fin d → ℂ =>
      localChart B (2 * k) (Point.map ℓ P) (Point.map ℓ (R z)) -
        localChart B (2 * k) (Point.map ℓ P) (Point.map ℓ P)
    obtain ⟨hF, hF0, hFR⟩ := s2e_morphism_native_centered_coordinates PP B d (2 * k) ℓ P
    change AnalyticAt ℂ F 0 at hF
    change F 0 = 0 at hF0
    change ∀ᶠ z in 𝓝 0, (localChart B (2 * k) (Point.map ℓ P)).symm
      (localChart B (2 * k) (Point.map ℓ P) (Point.map ℓ P) + F z) =
        Point.map ℓ (R z) at hFR
    have hηBF : AnalyticAt ℂ (fun z => ηB (F z)) 0 := hηB.comp_of_eq hF hF0
    have hηct : AnalyticAt ℂ (fun z => ηc (t z)) 0 := hηc.comp_of_eq ht ht0
    let sign : ℂ := if side then 1 else -1
    have hsign : sign ≠ 0 := by cases side <;> simp [sign]
    let η := fun z => ηB (F z) * ηc (t z) * sign / ηH z
    have hη : AnalyticAt ℂ η 0 :=
      ((hηBF.mul hηct).mul analyticAt_const).div hηH hηH0
    have hη0 : η 0 ≠ 0 := by
      dsimp only [η]
      rw [hF0, ht0]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero hηB0 hηc0) hsign) hηH0
    apply s2e_pulled_principal_analytic_unit_stalk PP B d ℓ
      (s2c_branchIdeal Z B n γn q) H P W hPW
      cB hB' U hPU cH hH η hη hη0
    have hFn : Tendsto F (𝓝 0) (𝓝 0) := hF0 ▸ hF.continuousAt.tendsto
    have heB' := hFn.eventually heB
    have hcoeff' := htn.eventually hcoeff
    have hec' := htn.eventually hec
    filter_upwards [heB', hcoeff', hec', hRA, hFR, heH,
      hηH.continuousAt.eventually_ne hηH0] with z hzB hzc hzr hzA hzF hzH hzHne
    have hBz : Point.evaluate W.1 cB (Point.map ℓ (R z)) =
        ηB (F z) * e (Point.map ℓ (R z)) (ι ⟨l, ⟨0, hm l⟩⟩) := by
      simpa only [hxP, hzF] using hzB
    have hcz : c ⟨0, hm l⟩ (t z) = e (Point.map ℓ (R z)) (ι ⟨l, ⟨0, hm l⟩⟩) := by
      rw [hzA]
      exact hzc ⟨0, hm l⟩
    have hsum : a 0 + t z = a z := by dsimp only [t]; abel
    have hcoeff0 : (monicPoly c (t z)).coeff 0 = c ⟨0, hm l⟩ (t z) := by
      simp only [monicPoly, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow]
      rw [if_neg (ne_of_lt (hm l)), zero_add]
      rw [Finset.sum_eq_single ⟨0, hm l⟩]
      · simp only [Fin.val_mk, if_true]
      · intro i _ hi
        apply if_neg
        intro hh
        apply hi
        exact Fin.ext hh.symm
      · intro hn
        exact (hn (Finset.mem_univ _)).elim
    rw [hBz, ← hcz, ← hcoeff0, hzr, hsum, hzH]
    change ηB (F z) * (ηc (t z) * (L (∑ i, a z i • b i) * sign)) =
      (ηB (F z) * ηc (t z) * sign / ηH z) * (ηH z * L (∑ i, a z i • b i))
    field_simp <;> ring
  · obtain ⟨W, hxW, hB⟩ := s2e_branch_equation_off_support Z B (2 * k) γ hγ hquot x q
      (by
        intro i hi
        obtain ⟨⟨l, v⟩, rfl⟩ := ι.surjective i
        exact hq ⟨l, (hxp l v).symm.trans hi⟩) n hn
    have hPW : (Point.map ℓ P).underlying ∈ W.1 := by
      rw [← hxP, Point.underlying_map]
      exact hxW
    have hzero : s2e_adjustedDifferentialDivisor
        (Module.finrank_fin_fun (n := 1) ℂ) w y (∑ i, a 0 i • b i) q = 0 := by
      rw [hD, Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero
      intro i _
      obtain ⟨⟨l, v⟩, rfl⟩ := ι.surjective i
      rw [hxp, Finsupp.single_eq_of_ne]
      exact fun h => hq ⟨l, h.symm⟩
    have hres0 : L (∑ i, a 0 i • b i) ≠ 0 := by
      intro hz
      have hinc := s2e_adjustedDifferentialDivisor_paired_incidence
        (Module.finrank_fin_fun (n := 1) ℂ) w y hy (fun i j => ⟨hpair i j, hres i j⟩)
        horder (∑ i, a 0 i • b i).1 (∑ i, a 0 i • b i).2 ha0 j
      have hh : 0 < s2e_adjustedDifferentialDivisor
          (Module.finrank_fin_fun (n := 1) ℂ) w y (∑ i, a 0 i • b i) q := by
        cases side
        · exact hinc.1.mpr hz
        · exact hinc.2.mpr hz
      rw [hzero] at hh
      exact (lt_irrefl _ hh)
    have hcH0 : Point.evaluate U.1 cH P ≠ 0 := by
      have hh := heH.self_of_nhds
      rw [hR0] at hh
      rw [hh]
      exact mul_ne_zero hηH0 hres0
    have hcHa : AnalyticAt ℂ (fun z => Point.evaluate U.1 cH (R z)) 0 :=
      s2e_native_section_analytic PP d P U.1 hPU cH
    have hcH00 : Point.evaluate U.1 cH (R 0) ≠ 0 := by rw [hR0]; exact hcH0
    let η := fun z : Fin d → ℂ => (Point.evaluate U.1 cH (R z))⁻¹
    have hη : AnalyticAt ℂ η 0 := hcHa.inv hcH00
    have hη0 : η 0 ≠ 0 := by simpa only [η, hR0] using inv_ne_zero hcH0
    apply s2e_pulled_principal_analytic_unit_stalk PP B d ℓ
      (s2c_branchIdeal Z B n γn q) H P W hPW
      1 (by simpa only [Ideal.span_singleton_one] using hB) U hPU cH hH η hη hη0
    have hWn : ∀ᶠ z in 𝓝 (0 : Fin d → ℂ), (Point.map ℓ (R z)).underlying ∈ W.1 :=
      ((Point.continuous_map ℓ).continuousAt.tendsto.comp
        (s2e_centered_native_chart_tendsto PP d P))
        ((Point.isOpen_overOpen W.1).mem_nhds hPW)
    filter_upwards [hcHa.continuousAt.eventually_ne hcH00, hWn]
      with z hz hzW
    change Point.evaluate W.1 1 (Point.map ℓ (R z)) = _
    have h1 : Point.evaluate W.1 1 (Point.map ℓ (R z)) = 1 := by
      simp only [Point.evaluate, dif_pos hzW, map_one]
    rw [h1]
    exact (inv_mul_cancel₀ hz).symm

end HodgeLean.Foundations.Program
