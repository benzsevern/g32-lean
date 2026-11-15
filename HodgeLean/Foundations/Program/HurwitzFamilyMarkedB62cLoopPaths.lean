import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalCharts

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold Filter Topology Set Metric
open scoped Manifold ContDiff

theorem b6m_exists_junction_off_finite {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {P : ℝ → C} (K : b3Rest_Cover ℂ P)
    (S : Set C) (hS : S.Finite) (k : ℤ) :
    ∃ w : C, (w ∈ (chartAt ℂ (K.x k)).source ∧
        chartAt ℂ (K.x k) w ∈ ball (chartAt ℂ (K.x k) (K.x k)) (K.r k)) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1,
        (chartAt ℂ (K.x k)).symm (chartAt ℂ (K.x k) (P (k / K.N)) +
          τ • (chartAt ℂ (K.x k) w - chartAt ℂ (K.x k) (P (k / K.N)))) ∈
            (chartAt ℂ (K.x (k - 1))).source ∧
        chartAt ℂ (K.x (k - 1)) ((chartAt ℂ (K.x k)).symm
          (chartAt ℂ (K.x k) (P (k / K.N)) +
          τ • (chartAt ℂ (K.x k) w - chartAt ℂ (K.x k) (P (k / K.N))))) ∈
            ball (chartAt ℂ (K.x (k - 1)) (K.x (k - 1))) (K.r (k - 1))) ∧ w ∉ S := by
  let φ := chartAt ℂ (K.x k)
  let ψ := chartAt ℂ (K.x (k - 1))
  let c := φ (P (k / K.N))
  obtain ⟨hPs, hc⟩ := K.mem_zero k
  have hP' : P (k / K.N) ∈ ψ.source ∧
      ψ (P (k / K.N)) ∈ ball (ψ (K.x (k - 1))) (K.r (k - 1)) := by
    have := K.mem (k - 1) 1 ⟨zero_le_one, le_rfl⟩
    rwa [show ((k - 1 : ℤ) : ℝ) + 1 = k by push_cast; ring] at this
  let W : Set ℂ := ball (φ (K.x k)) (K.r k) ∩ (φ.target ∩
    φ.symm ⁻¹' {y | y ∈ ψ.source ∧ ψ y ∈ ball (ψ (K.x (k - 1))) (K.r (k - 1))})
  have hWo : IsOpen W := isOpen_ball.inter (φ.continuousOn_symm.isOpen_inter_preimage
    φ.open_target (ψ.continuousOn.isOpen_inter_preimage ψ.open_source isOpen_ball))
  have hcW : c ∈ W := by
    refine ⟨hc, K.ball_sub k hc, ?_⟩
    change φ.symm c ∈ {y | y ∈ ψ.source ∧ ψ y ∈ ball (ψ (K.x (k - 1))) (K.r (k - 1))}
    rw [show φ.symm c = P (k / K.N) from φ.left_inv hPs]
    exact hP'
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWo c hcW
  obtain ⟨v, hv, hvS⟩ :=
    (infinite_of_mem_nhds c (ball_mem_nhds c hε)).exists_notMem_finite (hS.image φ)
  have hvW := hεW hv
  have hvt : v ∈ φ.target := hvW.2.1
  refine ⟨φ.symm v, ⟨φ.map_target hvt, by rw [φ.right_inv hvt]; exact hvW.1⟩,
    ?_, ?_⟩
  · intro τ hτ
    rw [φ.right_inv hvt]
    exact (hεW (Convex.add_smul_sub_mem (convex_ball c ε) (mem_ball_self hε) hv hτ)).2.2
  · intro hwS
    exact hvS ⟨φ.symm v, hwS, φ.right_inv hvt⟩

theorem b6m_exists_polygon_vertices_off_finite {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {P : ℝ → C} (hper : Function.Periodic P 1) (K : b3Rest_Cover ℂ P)
    (S : Set C) (hS : S.Finite) :
    ∃ L : b3Rest_Poly ℂ C, L.Follows P ∧ (∀ k, L.w k ∉ S) ∧
      (∀ k, L.r (k + L.N) = L.r k) := by
  have hPk : ∀ k : ℤ, P (((k + K.N : ℤ) : ℝ) / K.N) = P (k / K.N) := by
    intro k
    have := K.P_add hper k 0
    simpa only [add_zero] using this
  have hx1 : ∀ k : ℤ, K.x (k + K.N - 1) = K.x (k - 1) := fun k ↦ by
    rw [show k + K.N - 1 = (k - 1) + K.N by ring, K.x_add]
  have hr1 : ∀ k : ℤ, K.r (k + K.N - 1) = K.r (k - 1) := fun k ↦ by
    rw [show k + K.N - 1 = (k - 1) + K.N by ring, K.r_add]
  obtain ⟨w, hw_add, hw⟩ := b3Rest_exists_periodic_choice K.N _ (fun k a ↦ by
    simp only [K.x_add, K.r_add, hPk, hx1, hr1]) (b6m_exists_junction_off_finite K S hS)
  have hw' (k : ℤ) : w (k + 1) ∈ (chartAt ℂ (K.x k)).source ∧
      chartAt ℂ (K.x k) (w (k + 1)) ∈ ball (chartAt ℂ (K.x k) (K.x k)) (K.r k) := by
    have h := (hw (k + 1)).2.1 1 ⟨zero_le_one, le_rfl⟩
    rw [one_smul, add_sub_cancel,
      (chartAt ℂ (K.x (k + 1))).left_inv (hw (k + 1)).1.1, add_sub_cancel_right] at h
    exact h
  let L : b3Rest_Poly ℂ C :=
    ⟨K.N, K.pos, K.x, K.r, w, K.x_add, hw_add, K.ball_sub, fun k ↦ (hw k).1, hw'⟩
  exact ⟨L, ⟨K.mem, fun k ↦ (hw k).2.1⟩, (fun k ↦ (hw k).2.2), K.r_add⟩

theorem b6m_chart_ball_open_preconnected {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    (x : C) (r : ℝ)
    (hball : ball (chartAt ℂ x x) r ⊆ (chartAt ℂ x).target) :
    IsOpen {y | y ∈ (chartAt ℂ x).source ∧ chartAt ℂ x y ∈ ball (chartAt ℂ x x) r} ∧
      IsPreconnected {y | y ∈ (chartAt ℂ x).source ∧
        chartAt ℂ x y ∈ ball (chartAt ℂ x x) r} := by
  let φ := chartAt ℂ x
  refine ⟨φ.continuousOn.isOpen_inter_preimage φ.open_source isOpen_ball, ?_⟩
  have heq : {y | y ∈ φ.source ∧ φ y ∈ ball (φ x) r} = φ.symm '' ball (φ x) r := by
    ext y
    constructor
    · intro hy
      exact ⟨φ y, hy.2, φ.left_inv hy.1⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨φ.map_target (hball hz), by rw [φ.right_inv (hball hz)]; exact hz⟩
  change IsPreconnected {y | y ∈ φ.source ∧ φ y ∈ ball (φ x) r}
  rw [heq]
  exact (convex_ball (φ x) r).isPreconnected.image φ.symm (φ.continuousOn_symm.mono hball)

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_exists_matched_polygon_paths {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hfn : ∃ x y, f x ≠ f y) (hkn : ∃ x y, k x ≠ k y)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    {P : ℝ → C} (hper : Function.Periodic P 1) (K : b3Rest_Cover ℂ P) :
    ∃ L : b3Rest_Poly ℂ C, L.Follows P ∧ ∃ γ : ℤ → ℝ → C,
      (∀ j, γ (j + L.N) = γ j) ∧ ∀ j,
      b3A_IsGoodPath (E := ℂ) (γ j) (L.w j) (L.w (j + 1)) ∧
      b3A_IsGoodPath (E := ℂ) (e ∘ γ j) (e (L.w j)) (e (L.w (j + 1))) ∧
      (∀ s, γ j s ∈ (chartAt ℂ (L.x j)).source ∧
        chartAt ℂ (L.x j) (γ j s) ∈ ball (chartAt ℂ (L.x j) (L.x j)) (L.r j)) ∧
      (Set.range (γ j) \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
        ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}).Finite := by
  obtain ⟨S, hS, hpaths⟩ := b6m_filling_good_paths_off_finite b t hb f k hf hk hfn hkn e he
  obtain ⟨L, hLf, hLavoid, hLr⟩ := b6m_exists_polygon_vertices_off_finite hper K S hS
  have hex (j : ℤ) : ∃ γ : ℝ → C,
      b3A_IsGoodPath (E := ℂ) γ (L.w j) (L.w (j + 1)) ∧
      b3A_IsGoodPath (E := ℂ) (e ∘ γ) (e (L.w j)) (e (L.w (j + 1))) ∧
      (∀ s, γ s ∈ (chartAt ℂ (L.x j)).source ∧
        chartAt ℂ (L.x j) (γ s) ∈ ball (chartAt ℂ (L.x j) (L.x j)) (L.r j)) ∧
      (Set.range γ \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
        ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}).Finite := by
    obtain ⟨ho, hc⟩ := b6m_chart_ball_open_preconnected (L.x j) (L.r j) (L.ball_sub j)
    obtain ⟨γ, hγ, hγt, hγr, hbad⟩ := hpaths _ ho hc (L.w j) ⟨L.mem_w j, hLavoid j⟩
      (L.w (j + 1)) ⟨L.mem_w' j, hLavoid (j + 1)⟩
    exact ⟨γ, hγ, hγt, (fun s ↦ (hγr s).1), hbad⟩
  have hw1 (j : ℤ) : L.w (j + L.N + 1) = L.w (j + 1) := by
    rw [show j + L.N + 1 = (j + 1) + L.N by ring, L.w_add]
  refine ⟨L, hLf, ?_⟩
  exact b3Rest_exists_periodic_choice L.N _
    (fun j γ ↦ by simp only [L.w_add, hw1, L.x_add, hLr]) hex

theorem b6m_glue_matched_paths {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    (e : C → D) (N : ℕ) (w : ℤ → C) (γ : ℤ → ℝ → C)
    (hper : ∀ j, γ (j + N) = γ j)
    (hγ : ∀ j, b3A_IsGoodPath (E := ℂ) (γ j) (w j) (w (j + 1)))
    (hγt : ∀ j, b3A_IsGoodPath (E := ℂ) (e ∘ γ j) (e (w j)) (e (w (j + 1)))) :
    ∃ P : b3_SmoothLoop ℂ C, ∃ Q : b3_SmoothLoop ℂ D,
      (∀ s, P.1 s = γ ⌊(N : ℝ) * s⌋ (Int.fract ((N : ℝ) * s))) ∧
      ∀ s, Q.1 s = e (P.1 s) := by
  let p : ℝ → C := fun s ↦ γ ⌊(N : ℝ) * s⌋ (Int.fract ((N : ℝ) * s))
  have hp : Function.Periodic p 1 := by
    intro s
    simp only [p, mul_add, mul_one]
    rw [Int.floor_add_natCast, Int.fract_add_natCast, hper]
  have hd : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 p :=
    (b3Rest_floorPath_contMDiff γ w hγ).comp ((contDiff_const.mul contDiff_id).contMDiff)
  have hdt : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (e ∘ p) :=
    (b3Rest_floorPath_contMDiff (fun j ↦ e ∘ γ j) (e ∘ w) hγt).comp
      ((contDiff_const.mul contDiff_id).contMDiff)
  exact ⟨⟨p, hp, hd⟩, ⟨e ∘ p, fun s ↦ congrArg e (hp s), hdt⟩,
    (fun _ ↦ rfl), fun _ ↦ rfl⟩

theorem b6m_glued_path_chart_control {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C]
    (L : b3Rest_Poly ℂ C) (γ : ℤ → ℝ → C)
    (hγ : ∀ j, b3A_IsGoodPath (E := ℂ) (γ j) (L.w j) (L.w (j + 1)))
    (hmem : ∀ j s, γ j s ∈ (chartAt ℂ (L.x j)).source ∧
      chartAt ℂ (L.x j) (γ j s) ∈ ball (chartAt ℂ (L.x j) (L.x j)) (L.r j))
    (p : ℝ → C)
    (hp : ∀ s, p s = γ ⌊(L.N : ℝ) * s⌋ (Int.fract ((L.N : ℝ) * s))) :
    (∀ j : ℤ, p (j / L.N) = L.w j) ∧
      ∀ j : ℤ, ∀ s ∈ Icc ((j : ℝ) / L.N) ((j + 1) / L.N),
        p s ∈ (chartAt ℂ (L.x j)).source ∧
        chartAt ℂ (L.x j) (p s) ∈ ball (chartAt ℂ (L.x j) (L.x j)) (L.r j) := by
  have hN : (0 : ℝ) < L.N := Nat.cast_pos.mpr L.pos
  have hat (j : ℤ) : p (j / L.N) = L.w j := by
    rw [hp, show (L.N : ℝ) * (j / L.N) = j by field_simp,
      Int.floor_intCast, Int.fract_intCast]
    exact (hγ j).apply_zero
  refine ⟨hat, ?_⟩
  intro j s hs
  have h1 : (j : ℝ) ≤ L.N * s := by
    have := hs.1
    rw [div_le_iff₀ hN] at this
    linarith
  have h2 : (L.N : ℝ) * s ≤ j + 1 := by
    have := hs.2
    rw [le_div_iff₀ hN] at this
    linarith
  rcases h2.lt_or_eq with hlt | heq
  · have hfl : ⌊(L.N : ℝ) * s⌋ = j := Int.floor_eq_iff.mpr ⟨h1, hlt⟩
    rw [hp, hfl]
    exact hmem j _
  · have hs' : s = ((j + 1 : ℤ) : ℝ) / L.N := by
      push_cast
      apply (eq_div_iff hN.ne').mpr
      nlinarith [heq]
    rw [hs', hat]
    exact L.mem_w' j

theorem b6m_periodic_gluing_exceptional_finite {X : Type*}
    (N : ℕ) (hN : 0 < N) (γ : ℤ → ℝ → X) (hper : ∀ j, γ (j + N) = γ j)
    (U : Set X) (hfin : ∀ j, (Set.range (γ j) \ U).Finite)
    (p : ℝ → X) (hp : ∀ s, p s = γ ⌊(N : ℝ) * s⌋ (Int.fract ((N : ℝ) * s))) :
    (Set.range p \ U).Finite := by
  have hNz : (0 : ℤ) < N := Int.natCast_pos.mpr hN
  have hmod (j : ℤ) : γ (j % N) = γ j := by
    have H := (show Function.Periodic γ (N : ℤ) from hper).sub_int_mul_eq (x := j) (j / N)
    simpa only [Int.emod_def, Int.cast_id, mul_comm] using H
  apply ((Set.finite_Ico (0 : ℤ) N).biUnion (fun j _ ↦ hfin j)).subset
  rintro x ⟨⟨s, rfl⟩, hs⟩
  let j : ℤ := ⌊(N : ℝ) * s⌋
  apply Set.mem_iUnion.mpr
  refine ⟨j % N, Set.mem_iUnion.mpr ⟨⟨Int.emod_nonneg _ hNz.ne', Int.emod_lt_of_pos _ hNz⟩,
    ⟨?_, hs⟩⟩⟩
  exact ⟨Int.fract ((N : ℝ) * s), by rw [hmod, hp]⟩

end HodgeLean.Foundations.Program
