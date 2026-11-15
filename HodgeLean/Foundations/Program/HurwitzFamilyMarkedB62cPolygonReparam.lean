import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cAnalyticPaths
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cGeneric

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold Filter Topology Set Metric
open scoped Manifold ContDiff

theorem b6m_reparam_polygon_transverse {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (K : b3Rest_Poly ℂ C)
    (γ δ : b3_SmoothLoop ℂ C) (σ : ℤ → ℝ → ℝ)
    (hσ : ∀ j, ContDiff ℝ 1 (σ j)) (hr : ∀ j u, σ j u ∈ Icc 0 1)
    (h0 : ∀ j, σ j 0 = 0)
    (hδ : ∀ t, δ.1 t = (chartAt ℂ (K.x ⌊(K.N : ℝ) * t⌋)).symm
      (K.A ⌊(K.N : ℝ) * t⌋ + σ ⌊(K.N : ℝ) * t⌋ (Int.fract ((K.N : ℝ) * t)) •
        (K.B ⌊(K.N : ℝ) * t⌋ - K.A ⌊(K.N : ℝ) * t⌋)))
    (hV : ∀ j s, γ.1 s ≠ K.w j)
    (hS : ∀ (j : ℤ) (s l : ℝ), l ∈ Ioo (0 : ℝ) 1 →
      γ.1 s ∈ (chartAt ℂ (K.x j)).source →
      chartAt ℂ (K.x j) (γ.1 s) = K.A j + l • (K.B j - K.A j) →
      ∀ a b : ℝ, a • fderiv ℝ (chartAt ℂ (K.x j) ∘ γ.1) s 1 +
        b • (K.B j - K.A j) = 0 → a = 0 ∧ b = 0)
    (hpos : ∀ s t, γ.1 s = δ.1 t →
      0 < deriv (σ ⌊(K.N : ℝ) * t⌋) (Int.fract ((K.N : ℝ) * t))) :
    b3_Transverse ℂ γ δ := by
  intro s t hst
  have hN : (0 : ℝ) < K.N := Nat.cast_pos.mpr K.pos
  set j := ⌊(K.N : ℝ) * t⌋
  set u := Int.fract ((K.N : ℝ) * t)
  let φ := chartAt ℂ (K.x j)
  have hpt (v : ℝ) : K.A j + σ j v • (K.B j - K.A j) ∈
      ball (φ (K.x j)) (K.r j) :=
    Convex.add_smul_sub_mem (convex_ball _ _) (K.mem_w j).2 (K.mem_w' j).2 (hr j v)
  have hδt : δ.1 t = φ.symm (K.A j + σ j u • (K.B j - K.A j)) := hδ t
  have hz : σ j u ≠ 0 := by
    intro hz
    apply hV j s
    rw [hst, hδt, hz, zero_smul, add_zero]
    exact φ.left_inv (K.mem_w j).1
  have ho : σ j u ≠ 1 := by
    intro ho
    apply hV (j + 1) s
    rw [hst, hδt, ho, one_smul, add_sub_cancel]
    exact φ.left_inv (K.mem_w' j).1
  have hu : 0 < u := by
    apply lt_of_le_of_ne (Int.fract_nonneg _)
    intro heq
    change 0 = u at heq
    exact hz (by rw [← heq, h0])
  have hlt : (j : ℝ) < K.N * t := by
    have := Int.floor_add_fract ((K.N : ℝ) * t)
    linarith
  have hlt' : (K.N : ℝ) * t < j + 1 := Int.lt_floor_add_one _
  let g : ℝ → ℂ := fun v ↦ K.A j + σ j ((K.N : ℝ) * v - j) • (K.B j - K.A j)
  have hev : φ ∘ δ.1 =ᶠ[𝓝 t] g := by
    have hU : {v : ℝ | (j : ℝ) < K.N * v ∧ (K.N : ℝ) * v < j + 1} ∈ 𝓝 t :=
      ((isOpen_lt continuous_const (continuous_const.mul continuous_id)).inter
        (isOpen_lt (continuous_const.mul continuous_id) continuous_const)).mem_nhds ⟨hlt, hlt'⟩
    filter_upwards [hU] with v hv
    have hfl : ⌊(K.N : ℝ) * v⌋ = j := Int.floor_eq_iff.mpr ⟨hv.1.le, hv.2⟩
    change φ (δ.1 v) = g v
    rw [hδ v, hfl]
    simp only [Int.fract, hfl]
    exact φ.right_inv (K.ball_sub j (hpt _))
  have hder : HasDerivAt g ((deriv (σ j) u * K.N) • (K.B j - K.A j)) t := by
    have hA := ((hasDerivAt_id t).const_mul (K.N : ℝ)).sub_const (j : ℝ)
    have H := ((hσ j).differentiable one_ne_zero u).hasDerivAt.comp t hA
    simpa only [g, Function.comp_def, id_eq, mul_one] using
      (H.smul_const (K.B j - K.A j)).const_add (K.A j)
  have hfd : fderiv ℝ (φ ∘ δ.1) t 1 =
      (deriv (σ j) u * K.N) • (K.B j - K.A j) := by
    rw [hev.fderiv_eq, hder.hasFDerivAt.fderiv]
    simp
  have hs : γ.1 s ∈ φ.source := by
    rw [hst, hδt]
    exact φ.map_target (K.ball_sub j (hpt u))
  apply b3Rest_orient_ne_zero_of_chart (by simp) γ.1 δ.1 s t (γ.2.2 s) (δ.2.2 t)
    hst (K.x j) hs
  intro a b hab
  rw [hfd, smul_smul] at hab
  have hcross : φ (γ.1 s) = K.A j + σ j u • (K.B j - K.A j) := by
    rw [hst, hδt, φ.right_inv (K.ball_sub j (hpt u))]
  obtain ⟨ha, hb⟩ := hS j s (σ j u)
    ⟨lt_of_le_of_ne (hr j u).1 (Ne.symm hz), lt_of_le_of_ne (hr j u).2 ho⟩ hs hcross a _ hab
  refine ⟨ha, (mul_eq_zero.mp hb).resolve_right ?_⟩
  exact (mul_pos (hpos s t hst) hN).ne'

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_polygon_matched_parameters {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (L : b3Rest_Poly ℂ C)
    (hfin : ∀ j z, z ∈ segment ℝ (L.A j) (L.B j) →
      f ((chartAt ℂ (L.x j)).symm z) ≠ OnePoint.infty)
    (hkd : ∀ j z, z ∈ segment ℝ (L.A j) (L.B j) →
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e ((chartAt ℂ (L.x j)).symm z)) ≠ 0) :
    ∃ σ : ℤ → ℝ → ℝ, (∀ j, σ (j + L.N) = σ j) ∧ ∀ j,
      ContDiff ℝ 1 (σ j) ∧ (∀ s, σ j s ∈ Icc 0 1) ∧ σ j 0 = 0 ∧ σ j 1 = 1 ∧
      b3A_IsGoodPath (E := ℂ)
        (fun s ↦ (chartAt ℂ (L.x j)).symm (L.A j + σ j s • (L.B j - L.A j)))
        (L.w j) (L.w (j + 1)) ∧
      b3A_IsGoodPath (E := ℂ)
        (fun s ↦ e ((chartAt ℂ (L.x j)).symm (L.A j + σ j s • (L.B j - L.A j))))
        (e (L.w j)) (e (L.w (j + 1))) ∧
      (∀ s, σ j s ∈ Ioo 0 1 →
        (∀ i, b4cov_chart0 (f ((chartAt ℂ (L.x j)).symm
            (L.A j + σ j s • (L.B j - L.A j)))) ≠ b i ∧
          dist (b4cov_chart0 (f ((chartAt ℂ (L.x j)).symm
            (L.A j + σ j s • (L.B j - L.A j))))) (b i) ≠ b6t_radius b) →
        0 < deriv (σ j) s) := by
  have hw1 (j : ℤ) : L.w (j + L.N + 1) = L.w (j + 1) := by
    rw [show j + L.N + 1 = (j + 1) + L.N by ring, L.w_add]
  have hA (j : ℤ) : L.A (j + L.N) = L.A j := by
    simp only [b3Rest_Poly.A, L.x_add, L.w_add]
  have hB (j : ℤ) : L.B (j + L.N) = L.B j := by
    simp only [b3Rest_Poly.B, L.x_add, hw1]
  refine b3Rest_exists_periodic_choice L.N (fun j σ ↦
    ContDiff ℝ 1 σ ∧ (∀ s, σ s ∈ Icc 0 1) ∧ σ 0 = 0 ∧ σ 1 = 1 ∧
      b3A_IsGoodPath (E := ℂ)
        (fun s ↦ (chartAt ℂ (L.x j)).symm (L.A j + σ s • (L.B j - L.A j)))
        (L.w j) (L.w (j + 1)) ∧
      b3A_IsGoodPath (E := ℂ)
        (fun s ↦ e ((chartAt ℂ (L.x j)).symm (L.A j + σ s • (L.B j - L.A j))))
        (e (L.w j)) (e (L.w (j + 1))) ∧
      (∀ s, σ s ∈ Ioo 0 1 →
        (∀ i, b4cov_chart0 (f ((chartAt ℂ (L.x j)).symm
            (L.A j + σ s • (L.B j - L.A j)))) ≠ b i ∧
          dist (b4cov_chart0 (f ((chartAt ℂ (L.x j)).symm
            (L.A j + σ s • (L.B j - L.A j))))) (b i) ≠ b6t_radius b) →
        0 < deriv σ s))
    (fun j σ ↦ by simp only [L.x_add, L.w_add, hw1, hA, hB]) ?_
  intro j
  let φ := chartAt ℂ (L.x j)
  have hsub : segment ℝ (L.A j) (L.B j) ⊆ φ.target :=
    ((convex_ball _ _).segment_subset (L.mem_w j).2 (L.mem_w' j).2).trans (L.ball_sub j)
  have hi : ∀ z ∈ segment ℝ (L.A j) (L.A j + (L.B j - L.A j)),
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω φ.symm z := by
    intro z hz
    have ht := hsub (by simpa only [add_sub_cancel] using hz)
    exact (contMDiffOn_chart_symm (n := ω) _ ht).contMDiffAt (φ.open_target.mem_nhds ht)
  obtain ⟨σ, hd, hr, h0, h1, hg, hge, hpos⟩ := b6m_filling_holomorphic_segment b t hb f k hf hk
    e he (L.A j) (L.B j - L.A j) φ.symm hi
    (by simpa only [add_sub_cancel] using hfin j)
    (by simpa only [add_sub_cancel] using hkd j)
  have ha : φ.symm (L.A j) = L.w j := φ.left_inv (L.mem_w j).1
  have hb' : φ.symm (L.B j) = L.w (j + 1) := φ.left_inv (L.mem_w' j).1
  refine ⟨σ, hd, hr, h0, h1, ?_, ?_, hpos⟩
  · simpa only [add_sub_cancel, ha, hb'] using hg
  · simpa only [add_sub_cancel, ha, hb'] using hge

attribute [local instance] b3Forms_isManifold_real in
theorem b6m_period_eq_reparam_polygon {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (L : b3Rest_Poly ℂ C)
    (δ : b3_SmoothLoop ℂ C) (σ : ℤ → ℝ → ℝ) (hr : ∀ j s, σ j s ∈ Icc 0 1)
    (hgood : ∀ j, b3A_IsGoodPath (E := ℂ)
      (fun s ↦ (chartAt ℂ (L.x j)).symm (L.A j + σ j s • (L.B j - L.A j)))
      (L.w j) (L.w (j + 1)))
    (hδ : ∀ t, δ.1 t = (chartAt ℂ (L.x ⌊(L.N : ℝ) * t⌋)).symm
      (L.A ⌊(L.N : ℝ) * t⌋ + σ ⌊(L.N : ℝ) * t⌋ (Int.fract ((L.N : ℝ) * t)) •
        (L.B ⌊(L.N : ℝ) * t⌋ - L.A ⌊(L.N : ℝ) * t⌋))) :
    b3_period ℂ C δ = b3_period ℂ C L.smoothLoop := by
  let paths : ℤ → ℝ → C := fun j s ↦
    (chartAt ℂ (L.x j)).symm (L.A j + σ j s • (L.B j - L.A j))
  have hmem (j : ℤ) (s : ℝ) : paths j s ∈ (chartAt ℂ (L.x j)).source ∧
      chartAt ℂ (L.x j) (paths j s) ∈ ball (chartAt ℂ (L.x j) (L.x j)) (L.r j) := by
    have hpt : L.A j + σ j s • (L.B j - L.A j) ∈
        ball (chartAt ℂ (L.x j) (L.x j)) (L.r j) :=
      Convex.add_smul_sub_mem (convex_ball _ _) (L.mem_w j).2 (L.mem_w' j).2 (hr j s)
    have ht := L.ball_sub j hpt
    exact ⟨(chartAt ℂ (L.x j)).map_target ht,
      by change chartAt ℂ (L.x j) ((chartAt ℂ (L.x j)).symm _) ∈ _
         rw [(chartAt ℂ (L.x j)).right_inv ht]; exact hpt⟩
  obtain ⟨hat, hb⟩ := b6m_glued_path_chart_control L paths hgood hmem δ.1 hδ
  funext θ
  have him : b3Forms_d (b3Forms_imForm θ) = 0 := by
    rw [b3Forms_imForm_eq]
    exact b3Forms_d_reForm (by simp : Module.finrank ℂ ℂ = 1) _
  rw [b3Forms_period_eq, b3Forms_period_eq]
  rw [b6m_lineIntegral_eq_polygon L δ.1 δ.2.2 hat hb (b3Forms_isSmooth_reForm θ)
    (b3Forms_d_reForm (by simp) θ),
    b6m_lineIntegral_eq_polygon L δ.1 δ.2.2 hat hb (b3Forms_isSmooth_imForm θ) him]
  rfl

end HodgeLean.Foundations.Program
