import HodgeLean.Foundations.Program.CoverDictionaryCharts
import HodgeLean.Foundations.Program.CoverDictionaryCriteria
import HodgeLean.Foundations.Program.CoverDictionaryForms

/-! # B6-5 stage 5d, stage four: local forms of the pulled-back solutions

For a record `S : b65g_Solutions p O D` and a fibre over `b65p_curve p θ`, in the chart at a
point `x` of the fibre: the solution solves the system in the chart coordinate at every regular
point (`b65g_chart_ode`); at a point over a pole `t₀`, for any gauge `G` near `t₀` with
`G' = A G − (σ − t₀)⁻¹ G Λ`, the solution is `G(s) · P · diag(κ^{mᵢ}) · K` with `mᵢ = e dᵢ`
(`b65g_local_pole`); at a point over `s = ∞` it is `Φ K` with `Φ` analytic and `Φ(x) = 1`
(`b65g_local_infty`).
HC no distance; AV milestone no distance.
-/

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

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)

/-- **The system in a chart** at a regular point. -/
theorem b65g_chart_ode (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t) (z : ℂ)
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target)
    (hg : (extChartAt 𝓘(ℂ, ℂ) x).symm z ∈
      b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)) :
    HasDerivAt (fun w ↦ S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm w).val)
      (deriv (fun w ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          ((extChartAt 𝓘(ℂ, ℂ) x).symm w)) z •
        (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ)
          (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
            ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) *
          S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm z).val)) z ∧
    IsUnit (S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm z).val) ∧
    HasDerivAt (fun w ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
        ((extChartAt 𝓘(ℂ, ℂ) x).symm w))
      (b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11)
        ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
          mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩) z := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  set a := b65p_moving p θ 10
  set b := b65p_moving p θ 11
  have hab' : a * b ≠ 0 := mul_ne_zero ha hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set y := (extChartAt 𝓘(ℂ, ℂ) x).symm z
  obtain ⟨hYd, hYode⟩ := S.ode θ hθ t ht y hg
  have hs : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) y := by
    obtain ⟨w, hw, hw', -⟩ := hg
    exact (b65g_sFun_hasMFDerivAt D t hab' hba y w hw hw').mdifferentiableAt
  have hsd := b65g_ds_chart D t a b x z hz hs
  refine ⟨?_, S.unit θ hθ t ht y hg, hsd⟩
  have h := caf_hasDerivAt_chart x (fun y : b65z_fibre (b65z_centre p) D.C t ↦ S.Y θ y.val) z hz
    _ hYd.hasMFDerivAt
  refine h.congr_deriv ?_
  rw [hsd.deriv]
  exact hYode _

/-- The system in a chart on a punctured neighbourhood of any point. -/
theorem b65g_chart_ode_punctured (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t) :
    ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      HasDerivAt (fun w ↦ S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm w).val)
        (deriv (fun w ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
            ((extChartAt 𝓘(ℂ, ℂ) x).symm w)) z •
          (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ)
            (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
              ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) *
            S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm z).val)) z ∧
      IsUnit (S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm z).val) := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  filter_upwards [b65g_chart_punctured_good D t hab' hba (b65p_poles p θ) x] with z ⟨hz, hg⟩
  obtain ⟨h1, h2, -⟩ := b65g_chart_ode S θ hθ t ht x z hz hg
  exact ⟨h1, h2⟩

/-- **The local form at a point over a pole.** -/
theorem b65g_local_pole (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
      (Subset.refl _) t x ≠ ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) :
        OnePoint ℂ))
    (G : ℂ → 𝔼) (Λ P : 𝔼) (hP : IsUnit P) (d : Fin 4 → ℂ)
    (hΛ : Λ * P = P * b65r_operator (diagonal d))
    (hGu : ∀ᶠ σ in 𝓝 (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x),
      IsUnit (G σ))
    (hG : ∀ᶠ σ in 𝓝[≠] (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x),
      HasDerivAt G (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G σ -
        (σ - b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x)⁻¹ • (G σ * Λ)) σ) :
    ∃ e : ℕ, 0 < e ∧ ∃ l : ℂ → ℂ, AnalyticAt ℂ l (extChartAt 𝓘(ℂ, ℂ) x x) ∧
      l (extChartAt 𝓘(ℂ, ℂ) x x) ≠ 0 ∧
      (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x),
        b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) ((extChartAt 𝓘(ℂ, ℂ) x).symm z) =
          b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x +
            ((z - extChartAt 𝓘(ℂ, ℂ) x x) * l z) ^ e) ∧
      ∃ m : Fin 4 → ℤ, (∀ i, (e : ℂ) * d i = m i) ∧ ∃ K : 𝔼, IsUnit K ∧
        ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
          S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm z).val =
            G (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
              ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) * P *
              b65r_operator (diagonal fun i ↦
                ((z - extChartAt 𝓘(ℂ, ℂ) x x) * l z) ^ (m i)) * K := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  obtain ⟨e, he, l, hl, hl0, hs⟩ := b65g_sFun_root D t hab' hba x hx
  refine ⟨e, he, l, hl, hl0, hs, ?_⟩
  exact caf_gauge_euler _ _ G _ l _ _ e he hl hl0 hs (b65g_chart_ode_punctured S θ hθ t ht x)
    Λ P hP d hΛ hGu hG

/-- **The local form at a point over `s = ∞`.** -/
theorem b65g_local_infty (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
      (Subset.refl _) t x = ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) :
        OnePoint ℂ)) :
    ∃ e : ℕ, 0 < e ∧ ∃ l : ℂ → ℂ, AnalyticAt ℂ l (extChartAt 𝓘(ℂ, ℂ) x x) ∧
      l (extChartAt 𝓘(ℂ, ℂ) x x) ≠ 0 ∧
      (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x),
        (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          ((extChartAt 𝓘(ℂ, ℂ) x).symm z))⁻¹ = ((z - extChartAt 𝓘(ℂ, ℂ) x x) * l z) ^ e) ∧
      ∃ Φ : ℂ → 𝔼, AnalyticAt ℂ Φ (extChartAt 𝓘(ℂ, ℂ) x x) ∧
        Φ (extChartAt 𝓘(ℂ, ℂ) x x) = 1 ∧ ∃ K : 𝔼, IsUnit K ∧
        ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
          S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm z).val = Φ z * K := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  obtain ⟨e, he, l, hl, hl0, hs⟩ := b65g_sFun_root_infty D t hab' hba x hx
  refine ⟨e, he, l, hl, hl0, hs, ?_⟩
  set z₀ := extChartAt 𝓘(ℂ, ℂ) x x
  have hw : AnalyticAt ℂ (fun z ↦ ((z - z₀) * l z) ^ e) z₀ :=
    ((analyticAt_id.sub analyticAt_const).mul hl).pow e
  have hsw : ∀ᶠ z in 𝓝[≠] z₀, ((z - z₀) * l z) ^ e ≠ 0 ∧
      b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) ((extChartAt 𝓘(ℂ, ℂ) x).symm z) =
        (((z - z₀) * l z) ^ e)⁻¹ := by
    filter_upwards [caf_deriv_infty _ l z₀ e hl hl0 hs] with z hz
    exact ⟨pow_ne_zero e hz.1, hz.2.1⟩
  exact caf_infty_regular (b65p_poles p θ) (O.residue θ) (O.residue_sum θ hθO) _ _ _ z₀ hw
    (by simp [z₀, zero_pow he.ne']) hsw (b65g_chart_ode_punctured S θ hθ t ht x)

end HodgeLean.Foundations.Program
