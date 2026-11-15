import HodgeLean.Foundations.Program.CoverDictionaryMeromorphic
import HodgeLean.Foundations.Program.CoverDictionaryDescend

/-! Meromorphic solution germs for rational coefficient descent. -/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

local notation "𝔼" => (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)

/-- Products of matrices of meromorphic germs have meromorphic entries. -/
theorem caf_meromorphic_matrix_mul (A B : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (z₀ : ℂ)
    (hA : ∀ i j, MeromorphicAt (fun z ↦ A z i j) z₀)
    (hB : ∀ i j, MeromorphicAt (fun z ↦ B z i j) z₀) (i j : Fin 4) :
    MeromorphicAt (fun z ↦ (A z * B z) i j) z₀ := by
  simp only [Matrix.mul_apply]
  exact MeromorphicAt.fun_sum fun k _ ↦ (hA i k).mul (hB k j)

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)

/-- A local pole factorization gives meromorphic entries of the solution. -/
theorem b65g_Y_pole_meromorphic (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
      (Subset.refl _) t x ≠ ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) :
        OnePoint ℂ))
    (G : ℂ → 𝔼) (Λ P : 𝔼) (hP : IsUnit P) (d : Fin 4 → ℂ)
    (hΛ : Λ * P = P * b65r_operator (diagonal d))
    (hGa : ∀ i j, AnalyticAt ℂ (fun s ↦ b65q_mat (G s) i j)
      (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x))
    (hGu : ∀ᶠ σ in 𝓝 (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x),
      IsUnit (G σ))
    (hGd : ∀ᶠ σ in 𝓝[≠] (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x),
      HasDerivAt G (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G σ -
        (σ - b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x)⁻¹ • (G σ * Λ)) σ)
    (i j : Fin 4) :
    MeromorphicAt (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) i j)
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
  obtain ⟨e, he, l, hl, hl0, hs, m, hm, K, hK, hY⟩ :=
    b65g_local_pole S θ hθ t ht x hx G Λ P hP d hΛ hGu hGd
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hba := sub_ne_zero.mpr (Ne.symm hab)
  have hsa := b65g_sFun_chart_analytic D t hba x hx
  set z₀ := extChartAt 𝓘(ℂ, ℂ) x x
  set s := fun z ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
    ((extChartAt 𝓘(ℂ, ℂ) x).symm z)
  have hGa' : ∀ i j, MeromorphicAt (fun z ↦ b65q_mat (G (s z)) i j) z₀ := by
    intro i j
    apply AnalyticAt.meromorphicAt
    exact (hGa i j).comp_of_eq hsa (by simp only [s, z₀, extChartAt_to_inv])
  have hκ : MeromorphicAt (fun z ↦ (z - z₀) * l z) z₀ :=
    ((analyticAt_id.sub analyticAt_const).mul hl).meromorphicAt
  have hdiag : ∀ i j : Fin 4, MeromorphicAt
      (fun z ↦ (diagonal fun k ↦ ((z - z₀) * l z) ^ m k) i j) z₀ := by
    intro i j
    by_cases hij : i = j
    · subst j
      convert hκ.zpow (m i) using 1
      funext z
      simp only [Matrix.diagonal_apply_eq]
      rfl
    · simpa [Matrix.diagonal_apply, hij] using (MeromorphicAt.const z₀ (0 : ℂ))
  have hprod := caf_meromorphic_matrix_mul _ (fun _ ↦ b65q_mat K) z₀
    (caf_meromorphic_matrix_mul _ _ z₀
      (caf_meromorphic_matrix_mul _ (fun _ ↦ b65q_mat P) z₀ hGa'
        (fun _ _ ↦ MeromorphicAt.const _ _)) hdiag)
    (fun _ _ ↦ MeromorphicAt.const _ _) i j
  refine hprod.congr ?_
  filter_upwards [hY] with z hz
  simp only [b65g_Y, hz, caf_mat_mul, b65q_mat_operator, s]

/-- At a point over infinity the entries of the solution are meromorphic. -/
theorem b65g_Y_infty_meromorphic (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
      (Subset.refl _) t x = ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) :
        OnePoint ℂ)) (i j : Fin 4) :
    MeromorphicAt (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) i j)
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
  obtain ⟨e, he, l, hl, hl0, hs, Φ, hΦ, hΦ1, K, hK, hY⟩ :=
    b65g_local_infty S θ hθ t ht x hx
  have hprod := caf_meromorphic_matrix_mul (fun z ↦ b65q_mat (Φ z)) (fun _ ↦ b65q_mat K)
    (extChartAt 𝓘(ℂ, ℂ) x x)
    (fun i j ↦ (caf_analyticAt_clm (b65q_entryCLM i j) hΦ).meromorphicAt)
    (fun _ _ ↦ MeromorphicAt.const _ _) i j
  refine hprod.congr ?_
  filter_upwards [hY] with z hz
  simp only [b65g_Y, hz, caf_mat_mul]

/-- Fixed-pole gauges and the local factorizations give meromorphic solution entries everywhere. -/
theorem b65g_Y_meromorphic_of_gauges (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) (G : Fin 4 → ℂ → 𝔼)
    (hGm : ∀ k s, b65q_mat (G k s) = b65q_basis O.residue θ k * H k s)
    (hHa : ∀ k i j, AnalyticAt ℂ (fun s ↦ H k s i j) (b65p_fixedPole k))
    (hGu : ∀ k, ∀ᶠ σ in 𝓝 (b65p_fixedPole k), IsUnit (G k σ))
    (hGd : ∀ k, ∀ᶠ σ in 𝓝[≠] (b65p_fixedPole k), HasDerivAt (G k)
      (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G k σ -
        (σ - b65p_fixedPole k)⁻¹ • (G k σ * b65p_exponent k)) σ)
    (x : b65z_fibre (b65z_centre p) D.C t) (i j : Fin 4) :
    MeromorphicAt (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) i j)
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hba := sub_ne_zero.mpr (Ne.symm hab)
  by_cases hxg : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
  · exact (b65g_Y_entries_analytic S θ hθ t ht x hxg i j).2.meromorphicAt
  by_cases hxi : b63d_projection (b65z_centre p) D.C D.atlas.f
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) t x =
      ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) : OnePoint ℂ)
  · exact b65g_Y_infty_meromorphic S θ hθ t ht x hxi i j
  obtain ⟨q, hq⟩ := b65g_nongood_pole D t hba (b65p_poles p θ) rfl x hxg hxi
  cases q with
  | inl k =>
    have hxs : b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x =
        b65p_fixedPole k := hq.symm
    exact b65g_Y_pole_meromorphic S θ hθ t ht x hxi (G k) (b65p_exponent k) 1
      isUnit_one (b65p_exponents k) (by rw [mul_one, one_mul]; rfl)
      (by rw [hxs]; exact b65g_fixed_mat_analytic θ k (H k) (G k) (hGm k) (hHa k))
      (by rw [hxs]; exact hGu k) (by rw [hxs]; exact hGd k) i j
  | inr k =>
    obtain ⟨q, hq', Pm, hPm, hPme, hΛ, Gm, hGma, hGm1, hGmu, hGmd⟩ :=
      b65g_moving_data θ hθO k
    exact b65g_Y_pole_meromorphic S θ hθ t ht x hxi Gm (O.residue θ (Sum.inr k))
      (b65r_operator Pm) (caf_operator_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hPm)) _ hΛ
      (by rw [← hq]; exact hGma) (by rw [← hq]; exact hGmu)
      (by rw [← hq]; exact hGmd) i j

/-- A common parameter disc on which all solution entries are meromorphic in fibre charts. -/
theorem b65g_Y_meromorphic_near :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∀ (x : b65z_fibre (b65z_centre p) D.C t) (i j : Fin 4),
        MeromorphicAt (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) i j)
          (extChartAt 𝓘(ℂ, ℂ) x x) := by
  obtain ⟨ε, hε, hεO, hg⟩ := b65g_fixed_gauge O
  refine ⟨min ε S.radius, lt_min hε S.radius_pos, min_le_right _ _, fun θ hθ t ht ↦ ?_⟩
  have hθε : θ ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_left _ _) hθ
  have hθS : θ ∈ ball (0 : ℂ) S.radius := ball_subset_ball (min_le_right _ _) hθ
  choose H hH G hGm hGu hGd using hg θ hθε
  have hHa : ∀ k i j, AnalyticAt ℂ (fun s ↦ H k s i j) (b65p_fixedPole k) := by
    intro k i j
    obtain ⟨δ, hδ, ha, -, -⟩ := hH k
    exact ha i j _ (mem_ball_self hδ)
  exact b65g_Y_meromorphic_of_gauges S θ hθS t ht H G hGm hHa hGu hGd

end HodgeLean.Foundations.Program
