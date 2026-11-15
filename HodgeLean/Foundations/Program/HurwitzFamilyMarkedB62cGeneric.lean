import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cMatchedLoops

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold Filter Topology Set Metric MeasureTheory
open scoped Manifold ContDiff

theorem b6m_exists_generic_family {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {J : Type*} [Countable J]
    (γ : J → ℝ → C) (hγ : ∀ j, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (γ j))
    (x : C) (c₁ c₂ : ℂ) {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ v ∈ U, ∀ j, v ∉ b3Rest_img (γ j) x ∧
      v ∉ b3Rest_bad (γ j) x c₁ ∧ v ∉ b3Rest_bad (γ j) x c₂ := by
  let μ : Measure ℂ := Measure.addHaar
  have h0 : μ (⋃ j, b3Rest_img (γ j) x ∪ b3Rest_bad (γ j) x c₁ ∪
      b3Rest_bad (γ j) x c₂) = 0 := by
    apply measure_iUnion_null
    intro j
    exact measure_union_null (measure_union_null (b3Rest_img_null μ (by simp) (hγ j) x)
      (b3Rest_bad_null μ (by simp) (hγ j) x c₁)) (b3Rest_bad_null μ (by simp) (hγ j) x c₂)
  have hnot : ¬ U ⊆ ⋃ j, b3Rest_img (γ j) x ∪ b3Rest_bad (γ j) x c₁ ∪
      b3Rest_bad (γ j) x c₂ :=
    fun h ↦ (hU.measure_pos μ hne).ne' (measure_mono_null h h0)
  obtain ⟨v, hv, hvnot⟩ := Set.not_subset.mp hnot
  refine ⟨v, hv, fun j ↦ ⟨?_, ?_, ?_⟩⟩
  · exact fun h ↦ hvnot (Set.mem_iUnion.mpr ⟨j, Or.inl (Or.inl h)⟩)
  · exact fun h ↦ hvnot (Set.mem_iUnion.mpr ⟨j, Or.inl (Or.inr h)⟩)
  · exact fun h ↦ hvnot (Set.mem_iUnion.mpr ⟨j, Or.inr h⟩)

theorem b6m_exists_generic_avoiding_finite {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (γ : ℝ → C)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ)
    (S : Set C) (hS : S.Finite) (x : C) (c₁ c₂ : ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ v ∈ U, v ∉ b3Rest_img γ x ∧ v ∉ b3Rest_bad γ x c₁ ∧
      v ∉ b3Rest_bad γ x c₂ ∧ ∀ y ∈ S, y ∈ (chartAt ℂ x).source →
        chartAt ℂ x y ≠ v ∧ ∀ l ∈ Ioc (0 : ℝ) 1,
          chartAt ℂ x y ≠ c₁ + l • (v - c₁) ∧
          chartAt ℂ x y ≠ c₂ + l • (v - c₂) := by
  classical
  letI := hS.fintype
  let family : Option S → ℝ → C := fun j ↦ j.elim γ (fun y _ ↦ y.1)
  have hfamily : ∀ j, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (family j) := by
    intro j
    cases j with
    | none => exact hγ
    | some y => exact contMDiff_const
  obtain ⟨v, hv, hgen⟩ := b6m_exists_generic_family family hfamily x c₁ c₂ hU hne
  refine ⟨v, hv, (hgen none).1, (hgen none).2.1, (hgen none).2.2, ?_⟩
  intro y hy hys
  have H := hgen (some ⟨y, hy⟩)
  refine ⟨?_, fun l hl ↦ ⟨?_, ?_⟩⟩
  · exact fun heq ↦ H.1 ⟨0, hys, heq⟩
  · intro heq
    apply H.2.1
    refine ⟨0, l, hys, hl, heq, 1, 0, Or.inl one_ne_zero, ?_⟩
    simp [family, Function.comp_def]
  · intro heq
    apply H.2.2
    refine ⟨0, l, hys, hl, heq, 1, 0, Or.inl one_ne_zero, ?_⟩
    simp [family, Function.comp_def]

theorem b6m_exists_family_junction {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {J : Type*} [Countable J]
    (γ : J → ℝ → C) (hγ : ∀ j, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (γ j))
    {P : ℝ → C} (K : b3Rest_Cover ℂ P) (k : ℤ) :
    ∃ w : C, (w ∈ (chartAt ℂ (K.x k)).source ∧
        chartAt ℂ (K.x k) w ∈ ball (chartAt ℂ (K.x k) (K.x k)) (K.r k)) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1,
        (chartAt ℂ (K.x k)).symm (chartAt ℂ (K.x k) (P (k / K.N)) +
          τ • (chartAt ℂ (K.x k) w - chartAt ℂ (K.x k) (P (k / K.N)))) ∈
            (chartAt ℂ (K.x (k - 1))).source ∧
        chartAt ℂ (K.x (k - 1)) ((chartAt ℂ (K.x k)).symm
          (chartAt ℂ (K.x k) (P (k / K.N)) +
          τ • (chartAt ℂ (K.x k) w - chartAt ℂ (K.x k) (P (k / K.N))))) ∈
            ball (chartAt ℂ (K.x (k - 1)) (K.x (k - 1))) (K.r (k - 1))) ∧
      ∀ j s, γ j s ≠ w := by
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
  obtain ⟨v, hv, hgen⟩ := b6m_exists_generic_family γ hγ (K.x k) 0 0 isOpen_ball
    ⟨c, mem_ball_self hε⟩
  have hvW := hεW hv
  have hvt : v ∈ φ.target := hvW.2.1
  refine ⟨φ.symm v, ⟨φ.map_target hvt, by rw [φ.right_inv hvt]; exact hvW.1⟩, ?_, ?_⟩
  · intro τ hτ
    rw [φ.right_inv hvt]
    exact (hεW (Convex.add_smul_sub_mem (convex_ball c ε) (mem_ball_self hε) hv hτ)).2.2
  · intro j s hs
    exact (hgen j).1 ⟨s, by rw [hs]; exact φ.map_target hvt,
      by rw [hs, φ.right_inv hvt]⟩

theorem b6m_exists_family_middle {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {J : Type*} [Countable J]
    (γ : J → ℝ → C) (hγ : ∀ j, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (γ j))
    {P : ℝ → C} (K : b3Rest_Cover ℂ P) (k : ℤ) (c₁ c₂ : ℂ) :
    ∃ m : C, (m ∈ (chartAt ℂ (K.x k)).source ∧
        chartAt ℂ (K.x k) m ∈ ball (chartAt ℂ (K.x k) (K.x k)) (K.r k)) ∧
      ∀ j, chartAt ℂ (K.x k) m ∉ b3Rest_bad (γ j) (K.x k) c₁ ∧
        chartAt ℂ (K.x k) m ∉ b3Rest_bad (γ j) (K.x k) c₂ ∧ ∀ s, γ j s ≠ m := by
  let φ := chartAt ℂ (K.x k)
  obtain ⟨v, hv, hgen⟩ := b6m_exists_generic_family γ hγ (K.x k) c₁ c₂ isOpen_ball
    ⟨_, (K.mem_zero k).2⟩
  have hvt : v ∈ φ.target := K.ball_sub k hv
  refine ⟨φ.symm v, ⟨φ.map_target hvt, by rw [φ.right_inv hvt]; exact hv⟩, ?_⟩
  intro j
  refine ⟨by rw [φ.right_inv hvt]; exact (hgen j).2.1,
    by rw [φ.right_inv hvt]; exact (hgen j).2.2, ?_⟩
  intro s hs
  exact (hgen j).1 ⟨s, by rw [hs]; exact φ.map_target hvt,
    by rw [hs, φ.right_inv hvt]⟩

theorem b6m_choice_polygon_directions {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {P : ℝ → C} {K : b3Rest_Cover ℂ P}
    (γ : ℝ → C) (ch : b3Rest_Choice K γ) :
    (∀ j s, γ s ≠ ch.poly.w j) ∧
    ∀ (j : ℤ) (s l : ℝ), l ∈ Ioo (0 : ℝ) 1 →
      γ s ∈ (chartAt ℂ (ch.poly.x j)).source →
      chartAt ℂ (ch.poly.x j) (γ s) = ch.poly.A j + l • (ch.poly.B j - ch.poly.A j) →
      ∀ a b : ℝ, a • fderiv ℝ (chartAt ℂ (ch.poly.x j) ∘ γ) s 1 +
        b • (ch.poly.B j - ch.poly.A j) = 0 → a = 0 ∧ b = 0 := by
  constructor
  · intro j s
    rw [b3Rest_Choice.poly_w]
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
    · rw [b3Rest_Choice.pw_even]; exact ch.w_off k s
    · rw [b3Rest_Choice.pw_odd]; exact ch.m_off k s
  · intro j s l hl hs hcross a b hab
    simp only [b3Rest_Poly.A, b3Rest_Poly.B, b3Rest_Choice.poly_x,
      b3Rest_Choice.poly_w] at hs hcross hab
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
    · rw [show (2 * k) / 2 = k by omega] at hs hcross hab
      rw [b3Rest_Choice.pw_odd, b3Rest_Choice.pw_even] at hcross hab
      by_contra hne
      exact ch.m_bad₁ k ⟨s, l, hs, ⟨hl.1, hl.2.le⟩, hcross, a, b, not_and_or.mp hne, hab⟩
    · rw [show (2 * k + 1) / 2 = k by omega] at hs hcross hab
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
        b3Rest_Choice.pw_odd, b3Rest_Choice.pw_even] at hcross hab
      by_contra hne
      refine ch.m_bad₂ k ⟨s, 1 - l, hs, ⟨by linarith [hl.2], by linarith [hl.1]⟩,
        ?_, a, -b, ?_, ?_⟩
      · rw [hcross]; module
      · rcases not_and_or.mp hne with h | h
        · exact Or.inl h
        · exact Or.inr (neg_ne_zero.mpr h)
      · rw [← hab]; module

theorem b6m_exists_family_polygon_data {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {J : Type*} [Countable J] [Nonempty J]
    (γ : J → b3_SmoothLoop ℂ C) {P : ℝ → C} (hper : Function.Periodic P 1)
    (K : b3Rest_Cover ℂ P) :
    ∃ L : b3Rest_Poly ℂ C, L.Follows P ∧ ∀ j,
      (∀ k s, (γ j).1 s ≠ L.w k) ∧
      ∀ (k : ℤ) (s l : ℝ), l ∈ Ioo (0 : ℝ) 1 →
        (γ j).1 s ∈ (chartAt ℂ (L.x k)).source →
        chartAt ℂ (L.x k) ((γ j).1 s) = L.A k + l • (L.B k - L.A k) →
        ∀ a b : ℝ, a • fderiv ℝ (chartAt ℂ (L.x k) ∘ (γ j).1) s 1 +
          b • (L.B k - L.A k) = 0 → a = 0 ∧ b = 0 := by
  classical
  have hPk : ∀ k : ℤ, P (((k + K.N : ℤ) : ℝ) / K.N) = P (k / K.N) := by
    intro k
    have := K.P_add hper k 0
    simpa only [add_zero] using this
  have hx1 : ∀ k : ℤ, K.x (k + K.N - 1) = K.x (k - 1) := fun k ↦ by
    rw [show k + K.N - 1 = (k - 1) + K.N by ring, K.x_add]
  have hr1 : ∀ k : ℤ, K.r (k + K.N - 1) = K.r (k - 1) := fun k ↦ by
    rw [show k + K.N - 1 = (k - 1) + K.N by ring, K.r_add]
  obtain ⟨w, hw_add, hw⟩ := b3Rest_exists_periodic_choice K.N _ (fun k a ↦ by
    simp only [K.x_add, K.r_add, hPk, hx1, hr1])
      (b6m_exists_family_junction (fun j ↦ (γ j).1) (fun j ↦ (γ j).2.2) K)
  have hw1 : ∀ k : ℤ, w (k + K.N + 1) = w (k + 1) := fun k ↦ by
    rw [show k + K.N + 1 = (k + 1) + K.N by ring, hw_add]
  obtain ⟨m, hm_add, hm⟩ := b3Rest_exists_periodic_choice K.N _ (fun k a ↦ by
    simp only [K.x_add, K.r_add, hw_add, hw1])
      (fun k ↦ b6m_exists_family_middle (fun j ↦ (γ j).1) (fun j ↦ (γ j).2.2) K k
        (chartAt ℂ (K.x k) (w k)) (chartAt ℂ (K.x k) (w (k + 1))))
  let ch (j : J) : b3Rest_Choice K (γ j).1 :=
    ⟨w, m, hw_add, hm_add, (fun k ↦ (hw k).1), (fun k ↦ (hw k).2.1),
      (fun k ↦ (hw k).2.2 j), (fun k ↦ (hm k).1),
      (fun k ↦ ((hm k).2 j).1), (fun k ↦ ((hm k).2 j).2.1),
      (fun k ↦ ((hm k).2 j).2.2)⟩
  refine ⟨(ch (Classical.arbitrary J)).poly, (ch (Classical.arbitrary J)).follows, ?_⟩
  intro j
  exact b6m_choice_polygon_directions (γ j).1 (ch j)

theorem b6m_exists_polygon_data_off_finite {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (γ : b3_SmoothLoop ℂ C) {P : ℝ → C}
    (hper : Function.Periodic P 1) (K : b3Rest_Cover ℂ P) (S : Set C) (hS : S.Finite) :
    ∃ L : b3Rest_Poly ℂ C, L.Follows P ∧ (∀ k s, γ.1 s ≠ L.w k) ∧
      (∀ (k : ℤ) (s l : ℝ), l ∈ Ioo (0 : ℝ) 1 →
        γ.1 s ∈ (chartAt ℂ (L.x k)).source →
        chartAt ℂ (L.x k) (γ.1 s) = L.A k + l • (L.B k - L.A k) →
        ∀ a b : ℝ, a • fderiv ℝ (chartAt ℂ (L.x k) ∘ γ.1) s 1 +
          b • (L.B k - L.A k) = 0 → a = 0 ∧ b = 0) ∧
      ∀ k l, l ∈ Icc (0 : ℝ) 1 →
        (chartAt ℂ (L.x k)).symm (L.A k + l • (L.B k - L.A k)) ∉ S := by
  classical
  letI := hS.fintype
  let family : Option S → b3_SmoothLoop ℂ C := fun j ↦ j.elim γ
    (fun y ↦ ⟨fun _ ↦ y.1, (fun _ ↦ rfl), contMDiff_const⟩)
  obtain ⟨L, hF, hdata⟩ := b6m_exists_family_polygon_data family hper K
  refine ⟨L, hF, (hdata none).1, (hdata none).2, ?_⟩
  intro k l hl hmem
  let φ := chartAt ℂ (L.x k)
  let y := φ.symm (L.A k + l • (L.B k - L.A k))
  have hy : y ∈ S := hmem
  have H := hdata (some ⟨y, hy⟩)
  have hpt := Convex.add_smul_sub_mem (convex_ball _ _) (L.mem_w k).2 (L.mem_w' k).2 hl
  have ht := L.ball_sub k hpt
  have hys : y ∈ φ.source := φ.map_target ht
  have heq : φ y = L.A k + l • (L.B k - L.A k) := φ.right_inv ht
  by_cases h0 : l = 0
  · apply H.1 k 0
    change y = L.w k
    dsimp only [y]
    rw [h0, zero_smul, add_zero]
    exact φ.left_inv (L.mem_w k).1
  by_cases h1 : l = 1
  · apply H.1 (k + 1) 0
    change y = L.w (k + 1)
    dsimp only [y]
    rw [h1, one_smul, add_sub_cancel]
    exact φ.left_inv (L.mem_w' k).1
  have hlin := H.2 k 0 l ⟨lt_of_le_of_ne hl.1 (Ne.symm h0), lt_of_le_of_ne hl.2 h1⟩
    hys heq 1 0 (by
      change (1 : ℝ) • fderiv ℝ (fun _ : ℝ ↦ φ y) 0 1 + (0 : ℝ) • (L.B k - L.A k) = 0
      simp)
  exact one_ne_zero hlin.1

theorem b6m_exists_family_polygon {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {J : Type*} [Countable J] [Nonempty J]
    (γ : J → b3_SmoothLoop ℂ C) {P : ℝ → C} (hper : Function.Periodic P 1)
    (K : b3Rest_Cover ℂ P) :
    ∃ L : b3Rest_Poly ℂ C, L.Follows P ∧ ∀ j, b3_Transverse ℂ (γ j) L.smoothLoop := by
  obtain ⟨L, hF, hdata⟩ := b6m_exists_family_polygon_data γ hper K
  exact ⟨L, hF, fun j ↦ b3Rest_Poly.transverse (by simp) L (γ j)
    (hdata j).1 (hdata j).2⟩

attribute [local instance] b3Forms_isManifold_real in
theorem b6m_exists_transverse_family {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {J : Type*} [Countable J] [Nonempty J]
    (γ : J → b3_SmoothLoop ℂ C) (δ : b3_SmoothLoop ℂ C) :
    ∃ δ' : b3_SmoothLoop ℂ C, (∀ j, b3_Transverse ℂ (γ j) δ') ∧
      b3_period ℂ C δ' = b3_period ℂ C δ := by
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ :=
    b3Rest_exists_chartCover (E := ℂ) δ.1 δ.2.2.continuous δ.2.1
  let K : b3Rest_Cover ℂ δ.1 := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  obtain ⟨L, hF, htrans⟩ := b6m_exists_family_polygon γ δ.2.1 K
  refine ⟨L.smoothLoop, htrans, ?_⟩
  funext θ
  have him : b3Forms_d (b3Forms_imForm θ) = 0 := by
    rw [b3Forms_imForm_eq]
    exact b3Forms_d_reForm (by simp : Module.finrank ℂ ℂ = 1) _
  rw [b3Forms_period_eq, b3Forms_period_eq]
  show (b3Forms_lineIntegral (b3Forms_reForm θ) L.loop 0 1 : ℂ) +
      Complex.I * (b3Forms_lineIntegral (b3Forms_imForm θ) L.loop 0 1 : ℂ) = _
  rw [b3Rest_Poly.lineIntegral_loop hF δ.2.2 δ.2.1 (b3Forms_isSmooth_reForm θ)
      (b3Forms_d_reForm (by simp) θ),
    b3Rest_Poly.lineIntegral_loop hF δ.2.2 δ.2.1 (b3Forms_isSmooth_imForm θ) him]

theorem b6m_exists_transverse_avoiding_finite {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (γ δ : b3_SmoothLoop ℂ C) (S : Set C) (hS : S.Finite) :
    ∃ δ' : b3_SmoothLoop ℂ C, b3_Transverse ℂ γ δ' ∧
      b3_period ℂ C δ' = b3_period ℂ C δ ∧ ∀ s, δ'.1 s ∉ S := by
  classical
  letI := hS.fintype
  let family : Option S → b3_SmoothLoop ℂ C := fun j ↦ j.elim γ
    (fun y ↦ ⟨fun _ ↦ y.1, (fun _ ↦ rfl), contMDiff_const⟩)
  obtain ⟨δ', htrans, hperiod⟩ := b6m_exists_transverse_family family δ
  refine ⟨δ', htrans none, hperiod, ?_⟩
  intro s hs
  have H := htrans (some ⟨δ'.1 s, hs⟩) 0 s rfl
  apply H
  change b3_orient ℂ (b3_velocity ℂ C (fun _ : ℝ ↦ δ'.1 s) 0)
    (b3_velocity ℂ C δ'.1 s) = 0
  rw [b3_velocity, mfderiv_const]
  change b3_orient ℂ (0 : ℂ) (b3_velocity ℂ C δ'.1 s) = 0
  obtain ⟨κ, _, heq⟩ := b6m_orient_complex_coordinates
  exact (heq 0 (b3_velocity ℂ C δ'.1 s)).trans (by simp)

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_regular_transverse_representatives {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart) (ht : t ∈ b6t_polydisc b)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hfn : ∃ x y, f x ≠ f y) (hkn : ∃ x y, k x ≠ k y)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (Γ Δ : b3_SmoothLoop ℂ C) :
    ∃ P : b3_SmoothLoop ℂ C, ∃ Q : b3_SmoothLoop ℂ D, ∃ R : b3_SmoothLoop ℂ C,
      (∀ s, Q.1 s = e (P.1 s)) ∧ b3_period ℂ C P = b3_period ℂ C Γ ∧
      b3_period ℂ C R = b3_period ℂ C Δ ∧ b3_Transverse ℂ P R ∧
      ∀ s u, P.1 s = R.1 u → MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (P.1 s) ∧
        ∀ v w : ℂ, SignType.sign (b3_orient ℂ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (P.1 s) v)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (P.1 s) w)) = SignType.sign (b3_orient ℂ v w) := by
  obtain ⟨P, Q, S, hS, hQ, hP, hreg⟩ :=
    b6m_exists_regular_matched_smoothLoop b t hb ht f k hf hk hfn hkn e he Γ
  obtain ⟨R, htrans, hR, havoid⟩ := b6m_exists_transverse_avoiding_finite P Δ S hS
  refine ⟨P, Q, R, hQ, hP, hR, htrans, ?_⟩
  intro s u hsu
  exact hreg (P.1 s) ⟨⟨s, rfl⟩, by rw [hsu]; exact havoid u⟩

end HodgeLean.Foundations.Program
