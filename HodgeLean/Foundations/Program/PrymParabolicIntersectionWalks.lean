import HodgeLean.Foundations.Program.PrymParabolicIntersectionIncidence

set_option linter.unusedSectionVars false

noncomputable section
namespace HodgeLean.Foundations.Program

open Classical

section Walks

variable {G : Type} [Group G] (g : Fin 13 → G)

/-- The sign `±1` of a step direction.
Source: oriented edges of a Δ-complex. -/
def hga_sgn (b : Bool) : ℤ := if b then 1 else -1

/-- The start vertex of a signed edge step.
Source: `hg2_src`, `hg2_tgt`. -/
def hga_pStart (st : hg2_Edge G 13 × Bool) : hg2_Vert g :=
  if st.2 then hg2_src g st.1 else hg2_tgt g st.1

/-- The end vertex of a signed edge step.
Source: `hg2_src`, `hg2_tgt`. -/
def hga_pEnd (st : hg2_Edge G 13 × Bool) : hg2_Vert g :=
  if st.2 then hg2_tgt g st.1 else hg2_src g st.1

/-- The start triangle of a signed dual step (forward: from the outgoing to the incoming triangle).
Source: `hga_triOut`, `hga_triIn`. -/
def hga_dStart (st : hg2_Edge G 13 × Bool) : hg2_Tri G 13 :=
  if st.2 then hga_triOut g st.1 else hga_triIn st.1

/-- The end triangle of a signed dual step.
Source: `hga_triOut`, `hga_triIn`. -/
def hga_dEnd (st : hg2_Edge G 13 × Bool) : hg2_Tri G 13 :=
  if st.2 then hga_triIn st.1 else hga_triOut g st.1

/-- An edge walk from `v` to `w`.
Source: walks in a graph. -/
def hga_PChain : hg2_Vert g → List (hg2_Edge G 13 × Bool) → hg2_Vert g → Prop
  | v, [], w => v = w
  | v, st :: L, w => hga_pStart g st = v ∧ hga_PChain (hga_pEnd g st) L w

/-- A dual walk from `τ` to `τ'`.
Source: walks in the dual graph. -/
def hga_DChain : hg2_Tri G 13 → List (hg2_Edge G 13 × Bool) → hg2_Tri G 13 → Prop
  | τ, [], τ' => τ = τ'
  | τ, st :: L, τ' => hga_dStart g st = τ ∧ hga_DChain (hga_dEnd g st) L τ'

/-- The reversed walk.
Source: walks in a graph. -/
def hga_rev (L : List (hg2_Edge G 13 × Bool)) : List (hg2_Edge G 13 × Bool) :=
  (L.map fun st ↦ (st.1, !st.2)).reverse

/-- The coefficient of an edge in a walk: signed count of its passes.
Source: the cellular chain of a walk. -/
def hga_coef (L : List (hg2_Edge G 13 × Bool)) (ε : hg2_Edge G 13) : ℤ :=
  (L.map fun st ↦ if st.1 = ε then hga_sgn st.2 else 0).sum

theorem hga_PChain_append {v w u : hg2_Vert g} {L₁ L₂ : List (hg2_Edge G 13 × Bool)}
    (h₁ : hga_PChain g v L₁ w) (h₂ : hga_PChain g w L₂ u) : hga_PChain g v (L₁ ++ L₂) u := by
  induction L₁ generalizing v with
  | nil => simp only [hga_PChain] at h₁; subst h₁; simpa using h₂
  | cons st L ih => exact ⟨h₁.1, ih h₁.2⟩

theorem hga_DChain_append {τ τ' τ'' : hg2_Tri G 13} {L₁ L₂ : List (hg2_Edge G 13 × Bool)}
    (h₁ : hga_DChain g τ L₁ τ') (h₂ : hga_DChain g τ' L₂ τ'') :
    hga_DChain g τ (L₁ ++ L₂) τ'' := by
  induction L₁ generalizing τ with
  | nil => simp only [hga_DChain] at h₁; subst h₁; simpa using h₂
  | cons st L ih => exact ⟨h₁.1, ih h₁.2⟩

theorem hga_PChain_snoc {v w : hg2_Vert g} {L : List (hg2_Edge G 13 × Bool)}
    (h : hga_PChain g v L w) (st : hg2_Edge G 13 × Bool) (hst : hga_pStart g st = w) :
    hga_PChain g v (L ++ [st]) (hga_pEnd g st) :=
  hga_PChain_append g h ⟨hst, rfl⟩

theorem hga_DChain_snoc {τ τ' : hg2_Tri G 13} {L : List (hg2_Edge G 13 × Bool)}
    (h : hga_DChain g τ L τ') (st : hg2_Edge G 13 × Bool) (hst : hga_dStart g st = τ') :
    hga_DChain g τ (L ++ [st]) (hga_dEnd g st) :=
  hga_DChain_append g h ⟨hst, rfl⟩

theorem hga_PChain_rev {v w : hg2_Vert g} {L : List (hg2_Edge G 13 × Bool)}
    (h : hga_PChain g v L w) : hga_PChain g w (hga_rev L) v := by
  induction L generalizing v with
  | nil => simp only [hga_PChain] at h; subst h; rfl
  | cons st L ih =>
    obtain ⟨h1, h2⟩ := h
    have := ih h2
    simp only [hga_rev, List.map_cons, List.reverse_cons] at this ⊢
    apply hga_PChain_append g this
    refine ⟨?_, ?_⟩
    · simp only [hga_pStart, hga_pEnd, Bool.not_eq_true']; cases st.2 <;> rfl
    · simp only [hga_PChain, hga_pEnd, Bool.not_eq_true']
      rw [← h1]; simp only [hga_pStart]; cases st.2 <;> rfl

theorem hga_DChain_rev {τ τ' : hg2_Tri G 13} {L : List (hg2_Edge G 13 × Bool)}
    (h : hga_DChain g τ L τ') : hga_DChain g τ' (hga_rev L) τ := by
  induction L generalizing τ with
  | nil => simp only [hga_DChain] at h; subst h; rfl
  | cons st L ih =>
    obtain ⟨h1, h2⟩ := h
    have := ih h2
    simp only [hga_rev, List.map_cons, List.reverse_cons] at this ⊢
    apply hga_DChain_append g this
    refine ⟨?_, ?_⟩
    · simp only [hga_dStart, hga_dEnd, Bool.not_eq_true']; cases st.2 <;> rfl
    · simp only [hga_DChain, hga_dEnd, Bool.not_eq_true']
      rw [← h1]; simp only [hga_dStart]; cases st.2 <;> rfl

theorem hga_coef_nil (ε : hg2_Edge G 13) : hga_coef ([] : List (hg2_Edge G 13 × Bool)) ε = 0 :=
  rfl

theorem hga_coef_append (L₁ L₂ : List (hg2_Edge G 13 × Bool)) (ε : hg2_Edge G 13) :
    hga_coef (L₁ ++ L₂) ε = hga_coef L₁ ε + hga_coef L₂ ε := by
  simp [hga_coef]

theorem hga_coef_rev (L : List (hg2_Edge G 13 × Bool)) (ε : hg2_Edge G 13) :
    hga_coef (hga_rev L) ε = -hga_coef L ε := by
  induction L with
  | nil => rfl
  | cons st L ih =>
    simp only [hga_rev, List.map_cons, List.reverse_cons] at ih ⊢
    rw [hga_coef_append, ih]
    simp only [hga_coef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> cases st.2 <;> simp [hga_sgn]

theorem hga_coef_single (ε ε' : hg2_Edge G 13) :
    hga_coef [(ε, true)] ε' = if ε = ε' then 1 else 0 := by
  simp [hga_coef, hga_sgn]

end Walks

/-! ## Connectivity -/

section Connectivity

variable {G : Type} [Group G] (g : Fin 13 → G)

/-- Triangles reachable from `τ₀` by a dual walk. -/
def hga_DReach (τ₀ τ : hg2_Tri G 13) : Prop := ∃ L, hga_DChain g τ₀ L τ

theorem hga_DReach_step {τ₀ : hg2_Tri G 13} (st : hg2_Edge G 13 × Bool)
    (h : hga_DReach g τ₀ (hga_dStart g st)) : hga_DReach g τ₀ (hga_dEnd g st) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨_, hga_DChain_snoc g hL st rfl⟩

theorem hga_DReach_out_in {τ₀ : hg2_Tri G 13} (ε : hg2_Edge G 13) :
    hga_DReach g τ₀ (hga_triOut g ε) ↔ hga_DReach g τ₀ (hga_triIn ε) :=
  ⟨fun h ↦ hga_DReach_step g (ε, true) h, fun h ↦ hga_DReach_step g (ε, false) h⟩

theorem hga_dual_connected (hg : Subgroup.closure (Set.range g) = ⊤) (τ : hg2_Tri G 13) :
    hga_DReach g (Sum.inl (0, 1)) τ := by
  let R := hga_DReach g (Sum.inl (0, 1))
  -- `A_i(x) ~ B_i(x)` (edge `e_i(x)`), `A_{i+1}(x) ~ B_i(x)` (arc `f_{i+1}(x)`),
  -- `A_i(x) ~ B_i(x g_i)` (edge `h_i(x)`)
  have hAB : ∀ i x, R (Sum.inl (i, x)) ↔ R (Sum.inr (i, x)) := fun i x ↦
    (hga_DReach_out_in g (Sum.inl (i, x))).symm
  have hArot : ∀ i x, R (Sum.inl (finRotate 13 i, x)) ↔ R (Sum.inr (i, x)) := by
    intro i x
    have := hga_DReach_out_in g (τ₀ := Sum.inl (0, 1)) (Sum.inr (Sum.inl (finRotate 13 i, x)))
    simpa [hga_triOut, hga_triIn] using this
  have hAm : ∀ i x, R (Sum.inl (i, x)) ↔ R (Sum.inl (i, x * g i)) := by
    intro i x
    have h1 := hga_DReach_out_in g (τ₀ := Sum.inl (0, 1)) (Sum.inr (Sum.inr (i, x)))
    simp only [hga_triOut, hga_triIn] at h1
    change R _ ↔ R _ at h1
    rw [← h1, ← hAB]
  have hA0 : ∀ i x, R (Sum.inl (i, x)) ↔ R (Sum.inl (0, x)) := by
    intro i x
    induction i using Fin.induction with
    | zero => rfl
    | succ j hj =>
      have hjr : finRotate 13 j.castSucc = j.succ := finRotate_of_lt j.isLt
      rw [← hjr, hArot, ← hAB, hj]
  have hinv : ∀ y : G, ∀ x : G, R (Sum.inl (0, x)) ↔ R (Sum.inl (0, x * y)) := by
    intro y
    have hy : y ∈ Subgroup.closure (Set.range g) := by rw [hg]; trivial
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      intro x
      rw [← hA0 i x, hAm, hA0]
    | one => intro x; simp
    | mul a b _ _ ia ib => intro x; rw [ia, ib, mul_assoc]
    | inv a _ ia =>
      intro x
      have h := ia (x * a⁻¹)
      rw [inv_mul_cancel_right] at h
      exact h.symm
  have hbase : R (Sum.inl (0, 1)) := ⟨[], rfl⟩
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩
  · show R _
    rw [hA0]; simpa using (hinv x 1).mp hbase
  · show R _
    rw [← hAB, hA0]; simpa using (hinv x 1).mp hbase

/-- Vertices reachable from `v₀` by an edge walk. -/
def hga_PReach (v₀ v : hg2_Vert g) : Prop := ∃ L, hga_PChain g v₀ L v

theorem hga_PReach_step {v₀ : hg2_Vert g} (st : hg2_Edge G 13 × Bool)
    (h : hga_PReach g v₀ (hga_pStart g st)) : hga_PReach g v₀ (hga_pEnd g st) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨_, hga_PChain_snoc g hL st rfl⟩

theorem hga_PReach_src_tgt {v₀ : hg2_Vert g} (ε : hg2_Edge G 13) :
    hga_PReach g v₀ (hg2_src g ε) ↔ hga_PReach g v₀ (hg2_tgt g ε) :=
  ⟨fun h ↦ hga_PReach_step g (ε, true) h, fun h ↦ hga_PReach_step g (ε, false) h⟩

theorem hga_primal_connected (hprod : (List.ofFn g).prod = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) (v : hg2_Vert g) :
    hga_PReach g (Sum.inl 1) v := by
  let R := hga_PReach g (Sum.inl 1)
  -- `b₀(x) ~ b_∞(x Q_i⁻¹)` (arc `f_i(x)`)
  have hf : ∀ i x, R (Sum.inl x) ↔ R (Sum.inr (Sum.inl (x * (hg2_Q g i)⁻¹))) := fun i x ↦
    hga_PReach_src_tgt g (Sum.inr (Sum.inl (i, x)))
  have hm : ∀ i x, R (Sum.inl x) ↔ R (Sum.inl (x * g i)) := by
    intro i x
    rw [hf (finRotate 13 i) (x * g i), hg2_Q_rotate g hprod i, mul_inv_rev, ← mul_assoc,
      mul_inv_cancel_right, ← hf i x]
  have hinv : ∀ y : G, ∀ x : G, R (Sum.inl x) ↔ R (Sum.inl (x * y)) := by
    intro y
    have hy : y ∈ Subgroup.closure (Set.range g) := by rw [hg]; trivial
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact hm i
    | one => intro x; simp
    | mul a b _ _ ia ib => intro x; rw [ia, ib, mul_assoc]
    | inv a _ ia =>
      intro x
      have h := ia (x * a⁻¹)
      rw [inv_mul_cancel_right] at h
      exact h.symm
  have hbase : R (Sum.inl 1) := ⟨[], rfl⟩
  have hb0 : ∀ x, R (Sum.inl x) := fun x ↦ by simpa using (hinv x 1).mp hbase
  show R v
  rcases v with x | x | ⟨i, c⟩
  · exact hb0 x
  · have := (hf 0 (x * hg2_Q g 0)).mp (hb0 _)
    simpa using this
  · induction c using Quotient.inductionOn with
    | h x =>
      exact (hga_PReach_src_tgt g (Sum.inl (i, x))).mp (hb0 x)

end Connectivity

end HodgeLean.Foundations.Program
