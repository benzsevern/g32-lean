import HodgeLean.Foundations.Program.PrymParabolicSimplicesGeom

/-! # Covering lemmas for the lifted cells of stage H3b

Lifts of the base cells through the filling of a quotient covering of the punctured sphere at
`mr_base`, used for the step B statements in `PrymParabolicSimplicesProofs.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex Convexity Topology

namespace HodgeLean.Foundations.Program

/-! ## The simplex minus its vertex `1` -/

/-- The standard `2`-simplex minus the vertex `1`. -/
def hg5_P : Set (StdSimplex ℝ (Fin 3)) := {a | a.weights 1 < 1}

theorem hg5_P_isOpen : IsOpen hg5_P :=
  isOpen_lt (StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 1) continuous_const

theorem hg5_single0_mem_P : (StdSimplex.single 0 : StdSimplex ℝ (Fin 3)) ∈ hg5_P := by
  simp [hg5_P]

theorem hg5_mem_P_iff (a : StdSimplex ℝ (Fin 3)) : a ∈ hg5_P ↔ a ≠ StdSimplex.single 1 := by
  rw [hg5_P, Set.mem_setOf_eq, Ne, hg5_eq_single1]
  have := StdSimplex.weights_apply_le_one (R := ℝ) a 1
  constructor
  · intro h h'; linarith
  · intro h; exact lt_of_le_of_ne this h

theorem hg5_int_mem_P (a : StdSimplex ℝ (Fin 3)) (ha : ∀ k, 0 < a.weights k) : a ∈ hg5_P := by
  have := hg5_sum3 a; have := ha 0; have := ha 2
  show a.weights 1 < 1; linarith

/-- The point `(1 − t) e₀ + t a` of the simplex. -/
def hg5_toward (t : unitInterval) (a : StdSimplex ℝ (Fin 3)) : StdSimplex ℝ (Fin 3) :=
  hg5_pt (1 - t + t * a.weights 0) (t * a.weights 1) (t * a.weights 2)
    (by nlinarith [t.2.1, t.2.2, a.weights_nonneg 0])
    (mul_nonneg t.2.1 (a.weights_nonneg 1)) (mul_nonneg t.2.1 (a.weights_nonneg 2))
    (by have := hg5_sum3 a; linear_combination (t : ℝ) * this)

theorem hg5_toward_w (t : unitInterval) (a : StdSimplex ℝ (Fin 3)) :
    (hg5_toward t a).weights 0 = 1 - t + t * a.weights 0 ∧
      (hg5_toward t a).weights 1 = t * a.weights 1 ∧
      (hg5_toward t a).weights 2 = t * a.weights 2 := by
  simp [hg5_toward]

theorem hg5_toward_continuous :
    Continuous (fun p : unitInterval × StdSimplex ℝ (Fin 3) ↦ hg5_toward p.1 p.2) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
  refine continuous_pi fun k ↦ ?_
  have h0 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 0
  have h1 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 1
  have h2 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 2
  fin_cases k
  · simp only [Function.comp_apply, Fin.zero_eta, (hg5_toward_w _ _).1]; fun_prop
  · simp only [Function.comp_apply, Fin.mk_one, (hg5_toward_w _ _).2.1]; fun_prop
  · simp only [Function.comp_apply, Fin.reduceFinMk, (hg5_toward_w _ _).2.2]; fun_prop

theorem hg5_toward_zero (a : StdSimplex ℝ (Fin 3)) : hg5_toward 0 a = StdSimplex.single 0 := by
  apply hg5_simplex_ext <;> simp [hg5_toward_w]

theorem hg5_toward_one (a : StdSimplex ℝ (Fin 3)) : hg5_toward 1 a = a := by
  apply hg5_simplex_ext <;> simp [hg5_toward_w]

theorem hg5_toward_mem_P (t : unitInterval) (a : StdSimplex ℝ (Fin 3)) (ha : a ∈ hg5_P) :
    hg5_toward t a ∈ hg5_P := by
  show (hg5_toward t a).weights 1 < 1
  rw [(hg5_toward_w t a).2.1]
  have : (t : ℝ) * a.weights 1 ≤ a.weights 1 :=
    mul_le_of_le_one_left (a.weights_nonneg 1) t.2.2
  exact lt_of_le_of_lt this ha

theorem hg5_P_preconnected : IsPreconnected hg5_P := by
  refine IsConnected.isPreconnected (IsPathConnected.isConnected
    ⟨StdSimplex.single 0, hg5_single0_mem_P, fun {a} ha ↦ ?_⟩)
  refine ⟨⟨⟨fun t ↦ hg5_toward t a, hg5_toward_continuous.comp
    (Continuous.prodMk continuous_id continuous_const)⟩, hg5_toward_zero a, hg5_toward_one a⟩,
    fun t ↦ hg5_toward_mem_P t a ha⟩

theorem hg5_closure_Iio_one : (1 : unitInterval) ∈ closure {s : unitInterval | s < 1} := by
  show (1 : unitInterval) ∈ closure (Set.Iio (1 : unitInterval))
  rw [closure_Iio' (show (Set.Iio (1 : unitInterval)).Nonempty from ⟨0, by simp⟩)]
  exact Set.mem_Iic.mpr le_rfl

theorem hg5_closure_Ioi_zero : (0 : unitInterval) ∈ closure {s : unitInterval | 0 < s} := by
  show (0 : unitInterval) ∈ closure (Set.Ioi (0 : unitInterval))
  rw [closure_Ioi' (show (Set.Ioi (0 : unitInterval)).Nonempty from ⟨1, by simp⟩)]
  exact Set.mem_Ici.mpr le_rfl

theorem hg5_P_dense : Dense hg5_P := by
  intro a
  by_cases ha : a ∈ hg5_P
  · exact subset_closure ha
  · rw [hg5_mem_P_iff, not_not] at ha
    subst ha
    have hc : Continuous (fun t : unitInterval ↦ hg5_toward t (StdSimplex.single 1)) :=
      hg5_toward_continuous.comp (Continuous.prodMk continuous_id continuous_const)
    have := map_mem_closure hc hg5_closure_Iio_one (t := hg5_P) (fun t (ht : t < 1) ↦ by
      show (hg5_toward t _).weights 1 < 1
      rw [(hg5_toward_w _ _).2.1]
      simpa [hg5_single_w] using ht)
    rwa [hg5_toward_one] at this

theorem hg5_Iio_dense : Dense {s : unitInterval | s < 1} := by
  intro s
  by_cases hs : s < 1
  · exact subset_closure hs
  · have : s = 1 := le_antisymm s.2.2 (not_lt.mp hs)
    rw [this]; exact hg5_closure_Iio_one

theorem hg5_Ioi_dense : Dense {s : unitInterval | 0 < s} := by
  intro s
  by_cases hs : 0 < s
  · exact subset_closure hs
  · have : s = 0 := le_antisymm (not_lt.mp hs) s.2.1
    rw [this]; exact hg5_closure_Ioi_zero

/-- The point `(1 − t) a + t b` of the simplex. -/
def hg5_seg (a b : StdSimplex ℝ (Fin 3)) (t : unitInterval) : StdSimplex ℝ (Fin 3) :=
  hg5_pt ((1 - t) * a.weights 0 + t * b.weights 0) ((1 - t) * a.weights 1 + t * b.weights 1)
    ((1 - t) * a.weights 2 + t * b.weights 2)
    (by nlinarith [t.2.1, t.2.2, a.weights_nonneg 0, b.weights_nonneg 0])
    (by nlinarith [t.2.1, t.2.2, a.weights_nonneg 1, b.weights_nonneg 1])
    (by nlinarith [t.2.1, t.2.2, a.weights_nonneg 2, b.weights_nonneg 2])
    (by have := hg5_sum3 a; have := hg5_sum3 b; linear_combination (1 - (t : ℝ)) * ‹a.weights 0 + a.weights 1 + a.weights 2 = 1› + (t : ℝ) * this)

theorem hg5_seg_w1 (a b : StdSimplex ℝ (Fin 3)) (t : unitInterval) :
    (hg5_seg a b t).weights 1 = (1 - t) * a.weights 1 + t * b.weights 1 := by
  simp [hg5_seg]

theorem hg5_seg_continuous (a b : StdSimplex ℝ (Fin 3)) : Continuous (hg5_seg a b) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
  refine continuous_pi fun k ↦ ?_
  fin_cases k <;> simp [hg5_seg] <;> fun_prop

theorem hg5_seg_zero (a b : StdSimplex ℝ (Fin 3)) : hg5_seg a b 0 = a := by
  apply hg5_simplex_ext <;> simp [hg5_seg]

theorem hg5_seg_one (a b : StdSimplex ℝ (Fin 3)) : hg5_seg a b 1 = b := by
  apply hg5_simplex_ext <;> simp [hg5_seg]

/-- The punctured neighbourhoods `{1 − δ < a₁ < 1}` of the vertex `1` are preconnected. -/
theorem hg5_M_preconnected (δ : ℝ) :
    IsPreconnected ({a : StdSimplex ℝ (Fin 3) | 1 - δ < a.weights 1} ∩ hg5_P) := by
  apply isPreconnected_of_forall_pair
  intro a ha b hb
  refine ⟨Set.range (hg5_seg a b), ?_, ⟨0, hg5_seg_zero a b⟩, ⟨1, hg5_seg_one a b⟩,
    isPreconnected_range (hg5_seg_continuous a b)⟩
  rintro _ ⟨t, rfl⟩
  have ha1 : 1 - δ < a.weights 1 := ha.1
  have ha2 : a.weights 1 < 1 := ha.2
  have hb1 : 1 - δ < b.weights 1 := hb.1
  have hb2 : b.weights 1 < 1 := hb.2
  have ht0 := t.2.1
  have ht1 := t.2.2
  have e1 : (1 - (t : ℝ)) * a.weights 1 + t * b.weights 1 - min (a.weights 1) (b.weights 1) =
      (1 - t) * (a.weights 1 - min (a.weights 1) (b.weights 1)) +
        t * (b.weights 1 - min (a.weights 1) (b.weights 1)) := by ring
  have e2 : max (a.weights 1) (b.weights 1) - ((1 - (t : ℝ)) * a.weights 1 + t * b.weights 1) =
      (1 - t) * (max (a.weights 1) (b.weights 1) - a.weights 1) +
        t * (max (a.weights 1) (b.weights 1) - b.weights 1) := by ring
  have p1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (min_le_left (a.weights 1) (b.weights 1)))
  have p2 := mul_nonneg ht0 (sub_nonneg.mpr (min_le_right (a.weights 1) (b.weights 1)))
  have p3 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (le_max_left (a.weights 1) (b.weights 1)))
  have p4 := mul_nonneg ht0 (sub_nonneg.mpr (le_max_right (a.weights 1) (b.weights 1)))
  have hmin : 1 - δ < min (a.weights 1) (b.weights 1) := lt_min ha1 hb1
  have hmax : max (a.weights 1) (b.weights 1) < 1 := max_lt ha2 hb2
  refine ⟨?_, ?_⟩
  · show 1 - δ < (hg5_seg a b t).weights 1
    rw [hg5_seg_w1]; linarith
  · show (hg5_seg a b t).weights 1 < 1
    rw [hg5_seg_w1]; linarith

/-- The sets `{1 − δ < a₁}` form a basis of neighbourhoods of the vertex `1`. -/
theorem hg5_basis (O : Set (StdSimplex ℝ (Fin 3))) (hO : O ∈ 𝓝 (StdSimplex.single 1)) :
    ∃ δ > 0, {a : StdSimplex ℝ (Fin 3) | 1 - δ < a.weights 1} ⊆ O := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).nhds_eq_comap] at hO
  obtain ⟨V, hV, hVO⟩ := Filter.mem_comap.mp hO
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ε, hε, fun a ha ↦ hVO (hball ?_)⟩
  have ha' : 1 - ε < a.weights 1 := ha
  have hs := hg5_sum3 a
  have h0 := a.weights_nonneg 0
  have h2 := a.weights_nonneg 2
  have h1 := StdSimplex.weights_apply_le_one (R := ℝ) a 1
  show dist (fun k ↦ a.weights k) (fun k ↦ (StdSimplex.single 1 : StdSimplex ℝ (Fin 3)).weights k) < ε
  rw [dist_pi_lt_iff hε]
  intro k
  rw [Real.dist_eq, hg5_single_w]
  fin_cases k <;> simp <;> rw [abs_lt] <;> constructor <;> linarith

/-! ## Uniqueness of lifts through the filling -/

section Cover

variable {G : Type} [Group G] {U : Type} [TopologicalSpace U] [MulAction G U]
  {π : U → b6t_punctured mr_base} {C : Type} [TopologicalSpace C] [T2Space C]
  {f : C → OnePoint ℂ} {ι : U → C}

omit [TopologicalSpace U] [TopologicalSpace C] [T2Space C] in
/-- A point of `C` off the marks comes from `U`. -/
theorem hg5_mem_range (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (c : C)
    (hc : f c ∉ Set.range (b6_branch mr_base)) : c ∈ Set.range ι := by
  rw [hιr]; exact hc

omit [T2Space C] in
/-- Pull back a continuous map into `C` whose values lie off the marks to `U`. -/
theorem hg5_pullback {A : Type*} [TopologicalSpace A] (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (σ : A → C) (hσ : Continuous σ)
    (hm : ∀ a, f (σ a) ∉ Set.range (b6_branch mr_base)) :
    ∃ Λ : C(A, U), ∀ a, ι (Λ a) = σ a := by
  have h := fun a ↦ hg5_mem_range hιr (σ a) (hm a)
  choose Λ hΛ using h
  have hc : Continuous Λ := by
    rw [hι.isInducing.continuous_iff]
    have : ι ∘ Λ = σ := funext hΛ
    rw [this]; exact hσ
  exact ⟨⟨Λ, hc⟩, hΛ⟩

theorem hg5_unique (hπ : IsQuotientCoveringMap π G) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (hfι : ∀ u, f (ι u) = π u)
    {A : Type*} [TopologicalSpace A] (S : Set A) (hSc : IsPreconnected S) (hSd : Dense S)
    (σ σ' : C(A, C)) (heq : ∀ a, f (σ a) = f (σ' a))
    (hm : ∀ a ∈ S, f (σ a) ∉ Set.range (b6_branch mr_base)) (a₀ : A) (ha₀ : a₀ ∈ S)
    (h0 : σ a₀ = σ' a₀) : σ = σ' := by
  have : PreconnectedSpace S := Subtype.preconnectedSpace hSc
  obtain ⟨Λ, hΛ⟩ := hg5_pullback hι hιr (fun a : S ↦ σ a) (σ.continuous.comp continuous_subtype_val)
    (fun a ↦ hm a a.2)
  obtain ⟨Λ', hΛ'⟩ := hg5_pullback hι hιr (fun a : S ↦ σ' a)
    (σ'.continuous.comp continuous_subtype_val) (fun a ↦ by rw [← heq]; exact hm a a.2)
  have hcomp : π ∘ Λ = π ∘ Λ' := by
    funext a
    apply Subtype.ext
    simp only [Function.comp_apply, ← hfι, hΛ, hΛ', heq]
  have hΛ0 : Λ ⟨a₀, ha₀⟩ = Λ' ⟨a₀, ha₀⟩ := hι.injective (by rw [hΛ, hΛ', h0])
  have hΛΛ := hπ.isCoveringMap.eq_of_comp_eq Λ.continuous Λ'.continuous hcomp _ hΛ0
  have hon : Set.EqOn σ σ' S := fun a ha ↦ by
    have := congrArg ι (congrFun hΛΛ ⟨a, ha⟩)
    rwa [hΛ, hΛ'] at this
  ext a
  exact congrFun (Continuous.ext_on hSd σ.continuous σ'.continuous hon) a


/-- Two lifts of one base triangle that agree at a point other than the vertex `1` agree. -/
theorem hg5_tri_unique (hπ : IsQuotientCoveringMap π G) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (hfι : ∀ u, f (ι u) = π u)
    (τ₀ : hg2_Tri Unit 13) (σ σ' : C(StdSimplex ℝ (Fin 3), C))
    (h : ∀ a, f (σ a) = hg5_tri τ₀ a) (h' : ∀ a, f (σ' a) = hg5_tri τ₀ a)
    (a₀ : StdSimplex ℝ (Fin 3)) (ha₀ : a₀ ∈ hg5_P) (h0 : σ a₀ = σ' a₀) : σ = σ' := by
  refine hg5_unique hπ hι hιr hfι hg5_P hg5_P_preconnected hg5_P_dense σ σ'
    (fun a ↦ by rw [h, h']) (fun a ha ↦ ?_) a₀ ha₀ h0
  rw [h, hg5_tri_marks]; exact (hg5_mem_P_iff a).mp ha

variable [MulAction G C]

omit [T2Space C] in
theorem hg5_free (hπ : IsQuotientCoveringMap π G) (hι : Topology.IsOpenEmbedding ι)
    (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u) (u : U) (x x' : G)
    (h : x • ι u = x' • ι u) : x = x' := by
  have := hπ.isCancelSMul
  rw [← hιG, ← hιG] at h
  exact IsCancelSMul.right_cancel x x' u (hι.injective h)

theorem hg5_triBase_act (h : G) (τ : hg2_Tri G 13) :
    hg5_triBase (hg2_actTri h τ) = hg5_triBase τ := by
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> rfl

theorem hg5_triSheet_act (h : G) (τ : hg2_Tri G 13) :
    hg5_triSheet (hg2_actTri h τ) = h * hg5_triSheet τ := by
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> rfl

omit [Group G] [MulAction G C] in
theorem hg5_tri_eq_of (τ τ' : hg2_Tri G 13) (hb : hg5_triBase τ = hg5_triBase τ')
    (hs : hg5_triSheet τ = hg5_triSheet τ') : τ = τ' := by
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> rcases τ' with ⟨j, y⟩ | ⟨j, y⟩ <;>
    simp_all [hg5_triBase, hg5_triSheet]

/-- Deck equivariance of a family of lifts. -/
theorem hg5_deck (hπ : IsQuotientCoveringMap π G) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (hfι : ∀ u, f (ι u) = π u)
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c)) (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (u₀ : U) (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (h : G) (τ : hg2_Tri G 13) (a : StdSimplex ℝ (Fin 3)) :
    h • L τ a = L (hg2_actTri h τ) a := by
  let σ : C(StdSimplex ℝ (Fin 3), C) := ⟨fun a ↦ h • L τ a, (hC h).comp (L τ).continuous⟩
  have := hg5_tri_unique hπ hι hιr hfι (hg5_triBase τ) σ (L (hg2_actTri h τ))
    (fun a ↦ by simp only [σ, ContinuousMap.coe_mk, hfinv]; exact (hL τ).1 a)
    (fun a ↦ by rw [(hL _).1 a, hg5_triBase_act])
    _ hg5_single0_mem_P (by
      simp only [σ, ContinuousMap.coe_mk]
      rw [(hL τ).2, (hL _).2, hg5_triSheet_act, mul_smul])
  exact congrFun (congrArg DFunLike.coe this) a

/-- The lift of a base triangle on the sheet `x`. -/
def hg5_triLift {H : Type*} : hg2_Tri Unit 13 → H → hg2_Tri H 13
  | Sum.inl (i, _), x => Sum.inl (i, x)
  | Sum.inr (i, _), x => Sum.inr (i, x)

theorem hg5_triBase_lift {H : Type*} (τ : hg2_Tri Unit 13) (x : H) :
    hg5_triBase (hg5_triLift τ x) = τ := by
  rcases τ with ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ <;> rfl

theorem hg5_lift_cells_proof (hπ : IsQuotientCoveringMap π G)
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u) (u₀ : U)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    (∀ c : C, ∃ (τ : hg2_Tri G 13) (a : StdSimplex ℝ (Fin 3)), L τ a = c) ∧
      ∀ (τ τ' : hg2_Tri G 13) (a a' : StdSimplex ℝ (Fin 3)),
        (∀ k, 0 < a.weights k) → (∀ k, 0 < a'.weights k) → L τ a = L τ' a' →
          τ = τ' ∧ a = a' := by
  have _ := hf
  refine ⟨fun c ↦ ?_, fun τ τ' a a' ha ha' h ↦ ?_⟩
  · obtain ⟨τ₀, a, ha⟩ := hg5_cover_proof (f c)
    set τ₁ := hg5_triLift τ₀ (1 : G)
    have hf1 : f (L τ₁ a) = f c := by rw [(hL τ₁).1, hg5_triBase_lift, ha]
    obtain ⟨h, hh⟩ := hftr _ _ hf1
    exact ⟨hg2_actTri h τ₁, a, by
      rw [← hg5_deck hπ hι hιr hfι hC hfinv u₀ L hL h τ₁ a, hh]⟩
  · have hfa := congrArg f h
    rw [(hL τ).1, (hL τ').1] at hfa
    have hb := (hg5_open_cells_proof.1) _ _ a a' ha ha' hfa
    rw [hb] at hfa
    have haa := hg5_tri_injective_proof _ hfa
    subst haa
    have hLL := hg5_tri_unique hπ hι hιr hfι (hg5_triBase τ') (L τ) (L τ')
      (fun b ↦ by rw [(hL τ).1, hb]) (hL τ').1 a (hg5_int_mem_P a ha) h
    have h0 := congrArg (fun σ : C(StdSimplex ℝ (Fin 3), C) ↦ σ (StdSimplex.single 0)) hLL
    simp only [(hL τ).2, (hL τ').2] at h0
    exact ⟨hg5_tri_eq_of τ τ' hb (hg5_free hπ hι hιG u₀ _ _ h0), rfl⟩


/-! ## Lifted edges -/

omit [MulAction G C] in
theorem hg5_edgeE_unique (hπ : IsQuotientCoveringMap π G) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (hfι : ∀ u, f (ι u) = π u)
    (i : Fin 13) (γ γ' : C(unitInterval, C)) (h : ∀ s, f (γ s) = hg5_edgeE i s)
    (h' : ∀ s, f (γ' s) = hg5_edgeE i s) (h0 : γ 0 = γ' 0) : γ = γ' :=
  hg5_unique hπ hι hιr hfι {s | s < 1} isPreconnected_Iio hg5_Iio_dense γ γ'
    (fun s ↦ by rw [h, h']) (fun s hs ↦ by
      rw [h, hg5_edgeE_marks]; exact ne_of_lt hs) 0 (by show (0 : unitInterval) < 1; simp) h0

omit [MulAction G C] in
theorem hg5_edgeH_unique (hπ : IsQuotientCoveringMap π G) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (hfι : ∀ u, f (ι u) = π u)
    (i : Fin 13) (γ γ' : C(unitInterval, C)) (h : ∀ s, f (γ s) = hg5_edgeH i s)
    (h' : ∀ s, f (γ' s) = hg5_edgeH i s) (h1 : γ 1 = γ' 1) : γ = γ' :=
  hg5_unique hπ hι hιr hfι {s | 0 < s} isPreconnected_Ioi hg5_Ioi_dense γ γ'
    (fun s ↦ by rw [h, h']) (fun s hs ↦ by
      rw [h, hg5_edgeH_marks]; exact ne_of_gt hs) 1 (by show (0 : unitInterval) < 1; simp) h1

omit [MulAction G C] in
theorem hg5_edgeF_unique (hπ : IsQuotientCoveringMap π G) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (hfι : ∀ u, f (ι u) = π u)
    (i : Fin 13) (γ γ' : C(unitInterval, C)) (h : ∀ s, f (γ s) = hg5_edgeF i s)
    (h' : ∀ s, f (γ' s) = hg5_edgeF i s) (s₀ : unitInterval) (h0 : γ s₀ = γ' s₀) : γ = γ' :=
  hg5_unique hπ hι hιr hfι Set.univ isPreconnected_univ dense_univ γ γ'
    (fun s ↦ by rw [h, h']) (fun s _ ↦ by rw [h]; exact hg5_edgeF_marks i s) s₀ trivial h0

omit [T2Space C] [MulAction G C] in
/-- The faces of a lifted triangle lie over the base edges. -/
theorem hg5_face_lies (L : C(StdSimplex ℝ (Fin 3), C)) (τ₀ : hg2_Tri Unit 13)
    (hL : ∀ a, f (L a) = hg5_tri τ₀ a) (s : unitInterval) :
    f (hg5_face L 0 s) = hg5_edge (hg2_face0 hg5_one τ₀) s ∧
      f (hg5_face L 1 s) = hg5_edge (hg2_face1 τ₀) s ∧
      f (hg5_face L 2 s) = hg5_edge (hg2_face2 τ₀) s := by
  obtain ⟨e0, e1, e2⟩ := hg5_faces_proof τ₀
  refine ⟨?_, ?_, ?_⟩
  · rw [hg5_face_apply, hL, ← hg5_face_apply, e0]
  · rw [hg5_face_apply, hL, ← hg5_face_apply, e1]
  · rw [hg5_face_apply, hL, ← hg5_face_apply, e2]

/-! ## Endpoints of the lifted arcs in `U` -/

/-- The end of the lift of `f_j` from `u₀`, the monodromy of `F j` at `u₀`. -/
def hg5_T {y₀ y₁ : b6t_punctured mr_base} (hπ : IsQuotientCoveringMap π G) (u₀ : π ⁻¹' {y₀})
    (F : Fin 13 → Path y₀ y₁) (j : Fin 13) : π ⁻¹' {y₁} :=
  hπ.isCoveringMap.monodromy ⟦F j⟧ u₀

omit [TopologicalSpace C] [T2Space C] [MulAction G C] in
theorem hg5_arc_end {y₀ y₁ : b6t_punctured mr_base} (hπ : IsQuotientCoveringMap π G)
    (u₀ : π ⁻¹' {y₀}) (F : Fin 13 → Path y₀ y₁) (j : Fin 13) (y : G) (Γ : C(unitInterval, U))
    (hΓ : ∀ s, π (Γ s) = F j s) (h0 : Γ 0 = y • (u₀ : U)) :
    Γ 1 = y • (hg5_T hπ u₀ F j : U) := by
  have he := hπ.isCoveringMap.monodromy_eq_apply_one
    (e := hπ.toPermFiber y₀ y u₀) (γ := F j) (Γ := Γ) (funext hΓ) h0
  rw [← he, hπ.monodromy_toPermFiber]
  rfl

omit [TopologicalSpace C] [T2Space C] [MulAction G C] in
theorem hg5_step {y₀ y₁ : b6t_punctured mr_base} (hπ : IsQuotientCoveringMap π G)
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (j : Fin 13) :
    (hg5_T hπ u₀ F j : U) = g j • (hg5_T hπ u₀ F (finRotate 13 j) : U) := by
  set T := hg5_T hπ u₀ F
  have hk := hπ.fundamentalGroupToMulOpposite_apply_eq_iff.mp (hroot j)
  rw [← hg3_ell_isLoop_aux mr_base hg3_base_mem_polydisc y₀ y₁ F hF γ hγ j] at hk
  change g j • (u₀ : U) =
    (hπ.isCoveringMap.monodromy ⟦(F j).trans (F (finRotate 13 j)).symm⟧ u₀ : U) at hk
  have hh : hπ.toPermFiber y₀ (g j) u₀ =
      hπ.isCoveringMap.monodromy ⟦(F (finRotate 13 j)).symm⟧ (T j) := by
    apply Subtype.ext
    change g j • (u₀ : U) =
      (hπ.isCoveringMap.monodromy
        ((Path.Homotopic.Quotient.mk (F j)).trans (.mk (F (finRotate 13 j)).symm)) u₀ : U) at hk
    rw [hπ.isCoveringMap.monodromy_trans_apply] at hk
    exact hk
  have hr := hg3_transport_retrace hπ.isCoveringMap (F (finRotate 13 j)) u₀
  have hc := hπ.monodromy_toPermFiber
    (γ := ⟦(F (finRotate 13 j)).symm⟧) (e := T (finRotate 13 j)) (g := g j)
  change (T j : U) = (hπ.toPermFiber y₁ (g j) (T (finRotate 13 j)) : U)
  apply congrArg Subtype.val
  apply (hπ.isCoveringMap.monodromy_bijective ⟦(F (finRotate 13 j)).symm⟧).injective
  exact hh.symm.trans (hc.trans (congrArg (hπ.toPermFiber y₀ (g j)) hr)).symm

omit [T2Space C] in
/-- The arc face of a lifted triangle comes from a lift of `F j` in `U`. -/
theorem hg5_arc_pull {y₀ y₁ : b6t_punctured mr_base} (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (hfι : ∀ u, f (ι u) = π u)
    (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (u₀ : U) (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (j : Fin 13) (y : G) (γ : C(unitInterval, C)) (hγ : ∀ s, f (γ s) = hg5_edgeF j s)
    (h0 : γ 0 = y • ι u₀) :
    ∃ Γ : C(unitInterval, U), (∀ s, ι (Γ s) = γ s) ∧ (∀ s, π (Γ s) = F j s) ∧
      Γ 0 = y • u₀ := by
  obtain ⟨Γ, hΓ⟩ := hg5_pullback hι hιr γ γ.continuous (fun s ↦ by
    rw [hγ]; exact hg5_edgeF_marks j s)
  refine ⟨Γ, hΓ, fun s ↦ ?_, hι.injective (by rw [hΓ, h0, hιG])⟩
  apply Subtype.ext
  rw [← hfι, hΓ, hγ, hF]
  rfl


theorem hg5_bottom_mem : ((hg3_bottom : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
  show _ ∉ _
  rw [hg5_coe_mark_iff]; simp [hg3_bottom, mr_centre]

/-- The arcs as paths of the punctured sphere at `mr_base`, from a base point over `b₀` to `b_∞`. -/
theorem hg5_arcs (y₀ : b6t_punctured mr_base)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ)) :
    ∃ F : Fin 13 → Path y₀ ⟨_, hg5_bottom_mem⟩,
      ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ) :=
  hg3_arc_paths_base y₀ ⟨_, hg5_bottom_mem⟩ hy₀ rfl

omit [T2Space C] in
/-- The end of the arc face of a lifted `A`-triangle, in `U`. -/
theorem hg5_vertex2_eq {y₀ : b6t_punctured mr_base} (hπ : IsQuotientCoveringMap π G)
    (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ) (hfι : ∀ u, f (ι u) = π u)
    (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u) (u₀ : π ⁻¹' {y₀})
    (F : Fin 13 → Path y₀ ⟨_, hg5_bottom_mem⟩)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) (j : Fin 13) (y : G) :
    L (Sum.inl (j, y)) (StdSimplex.single 2) = ι (y • (hg5_T hπ u₀ F j : U)) ∧
      ∃ Γ : C(unitInterval, U), (∀ s, ι (Γ s) = hg5_face (L (Sum.inl (j, y))) 1 s) ∧
        (∀ s, π (Γ s) = F j s) ∧ Γ 0 = y • (u₀ : U) := by
  obtain ⟨Γ, hΓ, hπΓ, hΓ0⟩ := hg5_arc_pull hι hιr hfι hιG (u₀ : U) F hF j y
    (hg5_face (L (Sum.inl (j, y))) 1) (fun s ↦ (hg5_face_lies _ _ (hL _).1 s).2.1)
    (by rw [(hg5_face_vertex _).2.2.1, (hL _).2]; rfl)
  refine ⟨?_, Γ, hΓ, hπΓ, hΓ0⟩
  rw [← (hg5_face_vertex _).2.2.2.1, ← hΓ, hg5_arc_end hπ u₀ F j y Γ hπΓ hΓ0]

theorem hg5_lift_faces_proof {y₀ : b6t_punctured mr_base} (hπ : IsQuotientCoveringMap π G)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (τ : hg2_Tri G 13) :
    hg5_face (L τ) 0 = hg5_liftEdge L (hg2_face0 g τ) ∧
      hg5_face (L τ) 1 = hg5_liftEdge L (hg2_face1 τ) ∧
      hg5_face (L τ) 2 = hg5_liftEdge L (hg2_face2 τ) := by
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩
  · exact ⟨rfl, rfl, rfl⟩
  obtain ⟨F, hF⟩ := hg5_arcs y₀ hy₀
  have hv0 : ∀ τ, L τ (StdSimplex.single 0) = hg5_triSheet τ • ι (u₀ : U) := fun τ ↦ (hL τ).2
  have h1 : hg5_face (L (Sum.inr (i, x))) 1 = hg5_face (L (Sum.inl (finRotate 13 i, x))) 1 :=
    hg5_edgeF_unique hπ hι hιr hfι (finRotate 13 i) _ _
      (fun s ↦ (hg5_face_lies _ _ (hL _).1 s).2.1) (fun s ↦ (hg5_face_lies _ _ (hL _).1 s).2.1)
      0 (by rw [(hg5_face_vertex _).2.2.1, (hg5_face_vertex _).2.2.1, hv0, hv0]; rfl)
  refine ⟨?_, h1, ?_⟩
  · apply hg5_edgeH_unique hπ hι hιr hfι i _ _
      (fun s ↦ (hg5_face_lies _ _ (hL _).1 s).1) (fun s ↦ (hg5_face_lies _ _ (hL _).1 s).1)
    show hg5_face (L (Sum.inr (i, x))) 0 1 = hg5_face (L (Sum.inl (i, x * (g i)⁻¹))) 0 1
    rw [(hg5_face_vertex _).2.2.2.2.2, (hg5_face_vertex _).2.2.2.2.2,
      ← (hg5_face_vertex (L (Sum.inr (i, x)))).2.2.2.1, h1, (hg5_face_vertex _).2.2.2.1,
      (hg5_vertex2_eq hπ hι hιr hfι hιG u₀ F hF L hL _ _).1,
      (hg5_vertex2_eq hπ hι hιr hfι hιG u₀ F hF L hL _ _).1,
      hg5_step hπ u₀ g γ hγ hroot F hF i, ← mul_smul, inv_mul_cancel_right]
  · exact hg5_edgeE_unique hπ hι hιr hfι i _ _
      (fun s ↦ (hg5_face_lies _ _ (hL _).1 s).2.2) (fun s ↦ (hg5_face_lies _ _ (hL _).1 s).2.2)
      (by show hg5_face (L _) 2 0 = hg5_face (L (Sum.inl (i, x))) 2 0
          rw [(hg5_face_vertex _).1, (hg5_face_vertex _).1, hv0, hv0]; rfl)


/-! ## Lifted vertices -/

omit [TopologicalSpace C] [T2Space C] in
/-- The stabilizer argument: a deck-equivariant labelling `x ↦ V x` constant on the cosets
`x⟨g₀⟩`, whose stabilizers have order `orderOf g₀`, separates the cosets. -/
theorem hg5_coset_eq [Finite G] (g₀ : G) (V : G → C) (hdeck : ∀ h x, V (h * x) = h • V x)
    (hVg : ∀ x, V (x * g₀) = V x)
    (hcard : ∀ x, Nat.card (MulAction.stabilizer G (V x)) = orderOf g₀) (x y : G)
    (h : V x = V y) : (x : G ⧸ Subgroup.zpowers g₀) = y := by
  set H := Subgroup.zpowers (x * g₀ * x⁻¹)
  have hle : H ≤ MulAction.stabilizer G (V x) := by
    rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, ← hdeck]
    simp only [inv_mul_cancel_right, hVg]
  have hH : Nat.card H = orderOf g₀ := by
    rw [Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hH])
  have hy : (y * x⁻¹) • V x = V x := by
    rw [← hdeck, inv_mul_cancel_right, h]
  have hmem : y * x⁻¹ ∈ H := by rw [heq]; exact hy
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [conj_zpow] at hn
  rw [QuotientGroup.eq]
  have : x⁻¹ * y = g₀ ^ n := by
    have := congrArg (fun z ↦ x⁻¹ * z * x) hn
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] at this
    exact this.symm
  rw [this]
  exact Subgroup.zpow_mem_zpowers g₀ n

omit [TopologicalSpace C] [T2Space C] in
theorem hg5_stab_card (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c') (c c₀ : C)
    (hc : f c = f c₀) :
    Nat.card (MulAction.stabilizer G c) = Nat.card (MulAction.stabilizer G c₀) := by
  obtain ⟨h, rfl⟩ := hftr c c₀ hc
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj h).injective]

/-- The base vertex under a lifted vertex. -/
def hg5_vertBase {H : Type*} [Group H] {g : Fin 13 → H} : hg2_Vert g → hg2_Vert hg5_one
  | Sum.inl _ => Sum.inl ()
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl ())
  | Sum.inr (Sum.inr ⟨i, _⟩) =>
    Sum.inr (Sum.inr ⟨i, ((() : Unit) : Unit ⧸ Subgroup.zpowers (hg5_one i))⟩)

theorem hg5_lift_vertices_proof [Finite G] {y₀ : b6t_punctured mr_base}
    (hπ : IsQuotientCoveringMap π G)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    (∀ ε : hg2_Edge G 13, hg5_liftEdge L ε 0 = hg5_liftVert g L (hg2_src g ε) ∧
        hg5_liftEdge L ε 1 = hg5_liftVert g L (hg2_tgt g ε)) ∧
      Function.Injective (hg5_liftVert g L) := by
  obtain ⟨F, hF⟩ := hg5_arcs y₀ hy₀
  have faces := hg5_lift_faces_proof hπ hy₀ u₀ g γ hγ hroot hι hιr hfι hιG L hL
  set V : Fin 13 → G → C := fun i x ↦ L (Sum.inl (i, x)) (StdSimplex.single 1) with hVdef
  have hVg : ∀ i x, V i (x * g i) = V i x := by
    intro i x
    have e2 := congrArg (fun σ : C(unitInterval, C) ↦ σ 1) (faces (Sum.inr (i, x * g i))).2.2
    have e0 := congrArg (fun σ : C(unitInterval, C) ↦ σ 0) (faces (Sum.inr (i, x * g i))).1
    simp only [hg5_liftEdge, hg2_face2, hg2_face0, mul_inv_cancel_right] at e2 e0
    rw [(hg5_face_vertex _).2.1, (hg5_face_vertex _).2.1] at e2
    rw [(hg5_face_vertex _).2.2.2.2.1, (hg5_face_vertex _).2.2.2.2.1] at e0
    simp only [hVdef]
    rw [← e2, e0]
  have hVz : ∀ i x, ∀ n : ℤ, V i (x * g i ^ n) = V i x := by
    intro i x n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, ← mul_assoc, hVg, ih]
    | pred n ih =>
      rw [← ih, ← hVg i (x * g i ^ (-(n : ℤ) - 1)), mul_assoc, ← zpow_add_one]
      congr 3; ring
  have hVout : ∀ i (x : G), V i ((x : G ⧸ Subgroup.zpowers (g i)).out) = V i x := by
    intro i x
    obtain ⟨⟨h, hh⟩, he⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.zpowers (g i)) x
    rw [he]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact hVz i x n
  have hdeck : ∀ i h x, V i (h * x) = h • V i x := fun i h x ↦
    (hg5_deck hπ hι hιr hfι hC hfinv (u₀ : U) L hL h (Sum.inl (i, x)) _).symm
  obtain ⟨-, Δ, hΔι, hΔπ, hΔ0⟩ := hg5_vertex2_eq hπ hι hιr hfι hιG u₀ F hF L hL 0 1
  rw [one_smul] at hΔ0
  have hv2 : ∀ j y, L (Sum.inl (j, y)) (StdSimplex.single 2) =
      ι ((y * (hg_Q g j)⁻¹) • Δ 1) := by
    intro j y
    obtain ⟨-, Γ, hΓι, hΓπ, hΓ0⟩ := hg5_vertex2_eq hπ hι hιr hfι hιG u₀ F hF L hL j y
    rw [← (hg5_face_vertex _).2.2.2.1, ← hΓι,
      hg3_arc_endpoint mr_base hg3_base_mem_polydisc g U π hπ y₀ _ u₀ γ hγ hroot F hF Δ hΔπ hΔ0
        j y Γ hΓπ hΓ0]
  have hQ0 : hg_Q g 0 = 1 := hg_Q_zero g (by decide)
  have hv0 : ∀ τ, L τ (StdSimplex.single 0) = hg5_triSheet τ • ι (u₀ : U) := fun τ ↦ (hL τ).2
  refine ⟨fun ε ↦ ?_, fun v v' hvv ↦ ?_⟩
  · rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
    · refine ⟨?_, ?_⟩
      · show hg5_face (L (Sum.inl (i, x))) 2 0 = L (Sum.inl (0, x)) (StdSimplex.single 0)
        rw [(hg5_face_vertex _).1, hv0, hv0]; rfl
      · show hg5_face (L (Sum.inl (i, x))) 2 1 =
          L (Sum.inl (i, (x : G ⧸ Subgroup.zpowers (g i)).out)) (StdSimplex.single 1)
        rw [(hg5_face_vertex _).2.1]; exact (hVout i x).symm
    · refine ⟨?_, ?_⟩
      · show hg5_face (L (Sum.inl (i, x))) 1 0 = L (Sum.inl (0, x)) (StdSimplex.single 0)
        rw [(hg5_face_vertex _).2.2.1, hv0, hv0]; rfl
      · show hg5_face (L (Sum.inl (i, x))) 1 1 =
          L (Sum.inl (0, x * (hg2_Q g i)⁻¹)) (StdSimplex.single 2)
        rw [(hg5_face_vertex _).2.2.2.1, hv2, hv2, hQ0, inv_one, mul_one]; rfl
    · refine ⟨?_, ?_⟩
      · show hg5_face (L (Sum.inl (i, x))) 0 0 =
          L (Sum.inl (i, (x : G ⧸ Subgroup.zpowers (g i)).out)) (StdSimplex.single 1)
        rw [(hg5_face_vertex _).2.2.2.2.1]; exact (hVout i x).symm
      · show hg5_face (L (Sum.inl (i, x))) 0 1 =
          L (Sum.inl (0, x * (hg2_Q g i)⁻¹)) (StdSimplex.single 2)
        rw [(hg5_face_vertex _).2.2.2.2.2, hv2, hv2, hQ0, inv_one, mul_one]; rfl
  · have hfv : ∀ w, f (hg5_liftVert g L w) = hg5_vert (hg5_vertBase w) := by
      intro w
      rcases w with x | z | ⟨i, c⟩
      · show f (L (Sum.inl (0, x)) (StdSimplex.single 0)) = _
        rw [(hL _).1, hg5_tri_single0]; rfl
      · show f (L (Sum.inl (0, z)) (StdSimplex.single 2)) = _
        rw [(hL _).1, hg5_tri_single2]; rfl
      · show f (L (Sum.inl (i, c.out)) (StdSimplex.single 1)) = _
        rw [(hL _).1]
        exact (hg5_tri_single1 i ()).1
    have hb := hg5_vert_injective
      (show hg5_vert (hg5_vertBase v) = hg5_vert (hg5_vertBase v') by rw [← hfv, ← hfv, hvv])
    rcases v with x | z | ⟨i, c⟩ <;> rcases v' with x' | z' | ⟨j, c'⟩
    all_goals first | (exfalso; revert hb; simp [hg5_vertBase]; done) | skip
    · change L (Sum.inl (0, x)) (StdSimplex.single 0) =
        L (Sum.inl (0, x')) (StdSimplex.single 0) at hvv
      rw [hv0, hv0] at hvv
      have := hg5_free hπ hι hιG _ _ _ hvv
      simp only [hg5_triSheet] at this
      rw [this]
    · change L (Sum.inl (0, z)) (StdSimplex.single 2) =
        L (Sum.inl (0, z')) (StdSimplex.single 2) at hvv
      rw [hv2, hv2, hQ0, inv_one, mul_one, mul_one] at hvv
      have := hπ.isCancelSMul
      rw [IsCancelSMul.right_cancel z z' _ (hι.injective hvv)]
    · have hij : i = j := by
        simp only [hg5_vertBase, Sum.inr.injEq, Sigma.mk.injEq] at hb
        exact hb.1
      subst hij
      change V i c.out = V i c'.out at hvv
      obtain ⟨c₀, hc₀, hc₀card⟩ := hstab i
      have hcard : ∀ x, Nat.card (MulAction.stabilizer G (V i x)) = orderOf (g i) := by
        intro x
        rw [← hc₀card]
        apply hg5_stab_card hftr
        simp only [hVdef]
        rw [(hL _).1, hc₀]
        exact (hg5_tri_single1 i ()).1
      have := hg5_coset_eq (g i) (V i) (hdeck i) (hVg i) hcard _ _ hvv
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      rw [this]


/-! ## Existence of lifts through the filling -/

omit [TopologicalSpace C] [T2Space C] in
/-- The fibre over the base point: `x • ι u₀` comes from the fibre of `π`, since the fibre of `f`
over `b₀` contains the `|G|` points `ι(π⁻¹ y₀)` and lies in an orbit of at most `|G|` points. -/
theorem hg5_fiber_orbit [Finite G] {y₀ : b6t_punctured mr_base} (hπ : IsQuotientCoveringMap π G)
    (u₀ : π ⁻¹' {y₀}) (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hι : Function.Injective ι) (hfι : ∀ u, f (ι u) = π u) (x : G) :
    ∃ u : U, π u = y₀ ∧ ι u = x • ι u₀ := by
  set A := ι '' (π ⁻¹' {y₀})
  set O := Set.range (fun h : G ↦ h • ι (u₀ : U))
  have hAO : A ⊆ O := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : π u = y₀ := hu
    have h0 : π (u₀ : U) = y₀ := u₀.2
    obtain ⟨h, hh⟩ := hftr (ι u₀) (ι u) (by rw [hfι, hfι, hu', h0])
    exact ⟨h, hh⟩
  have hO : O.ncard ≤ Nat.card G := by
    show (Set.range (fun h : G ↦ h • ι (u₀ : U))).ncard ≤ _
    rw [← Set.image_univ, ← Set.ncard_univ G]
    exact Set.ncard_image_le (Set.toFinite _)
  have hA : A.ncard = Nat.card G := by
    rw [Set.ncard_image_of_injective _ hι, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (hπ.fiberEquivGroup u₀)
  have hAO' := Set.eq_of_subset_of_ncard_le hAO (by rw [hA]; exact hO) (Set.finite_range _)
  have hx : x • ι (u₀ : U) ∈ A := by rw [hAO']; exact ⟨x, rfl⟩
  obtain ⟨u, hu, hu'⟩ := (show x • ι (u₀ : U) ∈ ι '' (π ⁻¹' {y₀}) from hx)
  exact ⟨u, hu, hu'⟩

theorem hg5_lift_existsUnique_proof [Finite G] [CompactSpace C] {y₀ : b6t_punctured mr_base}
    (hπ : IsQuotientCoveringMap π G)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (hf : Continuous f)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (τ : hg2_Tri G 13) :
    ∃! σ : C(StdSimplex ℝ (Fin 3), C), (∀ a, f (σ a) = hg5_tri (hg5_triBase τ) a) ∧
      σ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀ := by
  classical
  set β := hg5_tri (hg5_triBase τ) with hβ
  set x := hg5_triSheet τ
  obtain ⟨ux, hux, hιux⟩ := hg5_fiber_orbit hπ u₀ hftr hι.injective hfι x
  have hβ0 : β (StdSimplex.single 0) = ((π ux : b6t_punctured mr_base) : OnePoint ℂ) := by
    rw [hux, hy₀, hβ, hg5_tri_single0]
  have hmem : ∀ p : hg5_P, β p.1 ∈ b6t_punctured mr_base := fun p ↦ by
    show β p.1 ∉ _
    rw [hβ, hg5_tri_marks]; exact (hg5_mem_P_iff _).mp p.2
  let H : C(unitInterval × hg5_P, b6t_punctured mr_base) :=
    ⟨fun q ↦ ⟨β (hg5_toward q.1 q.2.1), hmem ⟨_, hg5_toward_mem_P q.1 q.2.1 q.2.2⟩⟩, by
      apply Continuous.subtype_mk
      exact β.continuous.comp (hg5_toward_continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  have H0 : ∀ p, H (0, p) = π (ContinuousMap.const hg5_P ux p) := by
    intro p
    apply Subtype.ext
    show β (hg5_toward 0 p.1) = (π ux : OnePoint ℂ)
    rw [hg5_toward_zero, hβ0]
  set Λ := hπ.isCoveringMap.liftHomotopy H (ContinuousMap.const hg5_P ux) H0
  have hΛ := hπ.isCoveringMap.liftHomotopy_lifts H (ContinuousMap.const hg5_P ux) H0
  let σ0 : hg5_P → C := fun p ↦ ι (Λ (1, p))
  have hσ0c : Continuous σ0 :=
    hι.continuous.comp (Λ.continuous.comp (continuous_const.prodMk continuous_id))
  have hσ0f : ∀ p, f (σ0 p) = β p.1 := by
    intro p
    have := congrFun hΛ (1, p)
    show f (ι (Λ (1, p))) = _
    rw [hfι]
    simp only [Function.comp_apply] at this
    rw [this]
    show β (hg5_toward 1 p.1) = _
    rw [hg5_toward_one]
  set e0 : hg5_P := ⟨_, hg5_single0_mem_P⟩
  have hσ0e : σ0 e0 = x • ι u₀ := by
    have hc : Continuous (fun t : unitInterval ↦ Λ (t, e0)) :=
      Λ.continuous.comp (continuous_id.prodMk continuous_const)
    have hpath := hπ.isCoveringMap.eq_of_comp_eq hc (continuous_const (y := ux)) (by
      funext t
      have := congrFun hΛ (t, e0)
      simp only [Function.comp_apply] at this ⊢
      rw [this]
      apply Subtype.ext
      show β (hg5_toward t (StdSimplex.single 0)) = (π ux : OnePoint ℂ)
      rw [show hg5_toward t (StdSimplex.single 0) = StdSimplex.single 0 by
        apply hg5_simplex_ext <;> simp [hg5_toward_w], hβ0]) 0
      (hπ.isCoveringMap.liftHomotopy_zero H _ H0 e0)
    show ι (Λ (1, e0)) = _
    rw [congrFun hpath 1, hιux]
  -- the extension at the vertex `1`
  let g0 : StdSimplex ℝ (Fin 3) → C := fun a ↦ if h : a ∈ hg5_P then σ0 ⟨a, h⟩ else ι u₀
  have hg0P : ∀ a (h : a ∈ hg5_P), g0 a = σ0 ⟨a, h⟩ := fun a h ↦ dif_pos h
  have hg0c : ContinuousOn g0 hg5_P := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : hg5_P.domRestrict g0 = σ0 := funext fun p ↦ hg0P p.1 p.2
    rw [this]; exact hσ0c
  set M : ℝ → Set (StdSimplex ℝ (Fin 3)) :=
    fun δ ↦ {a : StdSimplex ℝ (Fin 3) | 1 - δ < a.weights 1} ∩ hg5_P with hM
  have hne : (𝓝[hg5_P] (StdSimplex.single 1 : StdSimplex ℝ (Fin 3))).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (hg5_P_dense _)
  obtain ⟨cs, -, hcs⟩ := isCompact_univ.exists_clusterPt
    (f := Filter.map g0 (𝓝[hg5_P] (StdSimplex.single 1))) (Filter.le_principal_iff.mpr Filter.univ_mem)
  have hMmem : ∀ δ > 0, M δ ∈ 𝓝[hg5_P] (StdSimplex.single 1 : StdSimplex ℝ (Fin 3)) := by
    intro δ hδ
    show {a : StdSimplex ℝ (Fin 3) | 1 - δ < a.weights 1} ∩ hg5_P ∈ _
    rw [Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply (isOpen_lt continuous_const
      (StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 1)).mem_nhds
    show 1 - δ < (StdSimplex.single 1 : StdSimplex ℝ (Fin 3)).weights 1
    rw [hg5_single_w]; simp; linarith
  have hmeet : ∀ W ∈ 𝓝 cs, ∀ δ > 0, (W ∩ g0 '' M δ).Nonempty := fun W hW δ hδ ↦
    clusterPt_iff_nonempty.mp hcs hW (Filter.image_mem_map (hMmem δ hδ))
  have hfcs : f cs = β (StdSimplex.single 1) := by
    by_contra hne'
    obtain ⟨Wq, D, hWq, hD, hcsW, hpD, hdisj⟩ := t2_separation hne'
    obtain ⟨δ, hδ, hsub⟩ := hg5_basis (β ⁻¹' D)
      (β.continuous.continuousAt.preimage_mem_nhds (hD.mem_nhds hpD))
    obtain ⟨c, hcW, a, ha, rfl⟩ :=
      hmeet (f ⁻¹' Wq) (hf.continuousAt.preimage_mem_nhds (hWq.mem_nhds hcsW)) δ hδ
    have h1 : f (g0 a) = β a := by rw [hg0P a ha.2, hσ0f]
    have h2 : f (g0 a) ∈ D := by rw [h1]; exact hsub ha.1
    exact Set.disjoint_left.mp hdisj hcW h2
  have hconv : ∀ W, IsOpen W → cs ∈ W → ∃ δ > 0, g0 '' M δ ⊆ W := by
    intro W hW hcsW
    set Fm := f ⁻¹' {β (StdSimplex.single 1)}
    have hFm : Fm.Finite := (Set.finite_range (fun h : G ↦ h • cs)).subset (fun c hc ↦ by
      obtain ⟨h, hh⟩ := hftr cs c (by rw [hfcs]; exact (Set.mem_preimage.mp hc).symm)
      exact ⟨h, hh⟩)
    obtain ⟨V, V', hV, hV', hcsV, hFV', hVV'⟩ := SeparatedNhds.of_isCompact_isCompact
      (isCompact_singleton (x := cs)) (hFm.sdiff (t := {cs})).isCompact
      (Set.disjoint_singleton_left.mpr (fun h ↦ h.2 rfl))
    have hV₁ : IsOpen (V ∩ W) := hV.inter hW
    have hK : IsCompact ((V ∩ W) ∪ V')ᶜ := (hV₁.union hV').isClosed_compl.isCompact
    have hD : IsOpen (f '' ((V ∩ W) ∪ V')ᶜ)ᶜ := (hK.image hf).isClosed.isOpen_compl
    have hpD : β (StdSimplex.single 1) ∈ (f '' ((V ∩ W) ∪ V')ᶜ)ᶜ := by
      rintro ⟨c, hc, hfc⟩
      apply hc
      by_cases hcc : c = cs
      · left; rw [hcc]; exact ⟨hcsV rfl, hcsW⟩
      · right; exact hFV' ⟨hfc, hcc⟩
    obtain ⟨δ, hδ, hsub⟩ := hg5_basis _ (β.continuous.continuousAt.preimage_mem_nhds
      (hD.mem_nhds hpD))
    refine ⟨δ, hδ, ?_⟩
    have himg : g0 '' M δ ⊆ (V ∩ W) ∪ V' := by
      rintro _ ⟨a, ha, rfl⟩
      by_contra hc
      exact hsub ha.1 ⟨g0 a, hc, by rw [hg0P a ha.2, hσ0f]⟩
    have hpc : IsPreconnected (g0 '' M δ) :=
      (hg5_M_preconnected δ).image g0 (hg0c.mono Set.inter_subset_right)
    have hmV : (g0 '' M δ ∩ (V ∩ W)).Nonempty := by
      obtain ⟨c, hc1, hc2⟩ := hmeet (V ∩ W) (hV₁.mem_nhds ⟨hcsV rfl, hcsW⟩) δ hδ
      exact ⟨c, hc2, hc1⟩
    exact (hpc.subset_left_of_subset_union hV₁ hV' (hVV'.mono_left Set.inter_subset_left)
      himg hmV).trans Set.inter_subset_right
  let σf : StdSimplex ℝ (Fin 3) → C := fun a ↦ if h : a ∈ hg5_P then σ0 ⟨a, h⟩ else cs
  have h1P : (StdSimplex.single 1 : StdSimplex ℝ (Fin 3)) ∉ hg5_P := by
    rw [hg5_mem_P_iff, not_not]
  have hσfc : Continuous σf := by
    rw [continuous_iff_continuousAt]
    intro a
    by_cases ha : a ∈ hg5_P
    · have hon : ContinuousOn σf hg5_P := by
        rw [continuousOn_iff_continuous_domRestrict]
        have : hg5_P.domRestrict σf = σ0 := funext fun p ↦ dif_pos p.2
        rw [this]; exact hσ0c
      exact hon.continuousAt (hg5_P_isOpen.mem_nhds ha)
    · have ha1 : a = StdSimplex.single 1 := by rwa [hg5_mem_P_iff, not_not] at ha
      subst ha1
      rw [ContinuousAt, show σf (StdSimplex.single 1) = cs from dif_neg h1P,
        (nhds_basis_opens cs).tendsto_right_iff]
      rintro W ⟨hcsW, hW⟩
      obtain ⟨δ, hδ, hsub⟩ := hconv W hW hcsW
      have hN : {a : StdSimplex ℝ (Fin 3) | 1 - δ < a.weights 1} ∈
          𝓝 (StdSimplex.single 1 : StdSimplex ℝ (Fin 3)) := by
        apply (isOpen_lt continuous_const
          (StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 1)).mem_nhds
        show 1 - δ < (StdSimplex.single 1 : StdSimplex ℝ (Fin 3)).weights 1
        rw [hg5_single_w]; simp; linarith
      filter_upwards [hN] with b hb
      by_cases hbP : b ∈ hg5_P
      · show σf b ∈ W
        rw [show σf b = σ0 ⟨b, hbP⟩ from dif_pos hbP]
        exact hsub ⟨b, ⟨hb, hbP⟩, hg0P b hbP⟩
      · show σf b ∈ W
        rw [show σf b = cs from dif_neg hbP]
        exact hcsW
  have hσf : ∀ a, f (σf a) = β a := by
    intro a
    by_cases ha : a ∈ hg5_P
    · rw [show σf a = σ0 ⟨a, ha⟩ from dif_pos ha, hσ0f]
    · have ha1 : a = StdSimplex.single 1 := by rwa [hg5_mem_P_iff, not_not] at ha
      subst ha1
      rw [show σf (StdSimplex.single 1) = cs from dif_neg h1P]
      exact hfcs
  have hσf0 : σf (StdSimplex.single 0) = x • ι u₀ := by
    rw [show σf (StdSimplex.single 0) = σ0 e0 from dif_pos hg5_single0_mem_P]
    exact hσ0e
  refine ⟨⟨σf, hσfc⟩, ⟨hσf, hσf0⟩, fun σ' hσ' ↦ ?_⟩
  exact hg5_tri_unique hπ hι hιr hfι _ σ' ⟨σf, hσfc⟩ hσ'.1 hσf _ hg5_single0_mem_P
    (by rw [hσ'.2]; exact hσf0.symm)

end Cover

end HodgeLean.Foundations.Program
